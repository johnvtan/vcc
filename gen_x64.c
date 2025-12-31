#include <assert.h>
#include <limits.h>
#include <math.h>
#include <stdlib.h>
#include <vcc/errors.h>
#include <vcc/gen_x64.h>
#include <vcc/hashmap.h>

typedef struct {
  // Vec<x64_StaticConst>
  Vec* out;

  // Map from string repr of constant --> label of constant
  Hashmap* map;

  int num;
} StaticConstContext;

typedef struct {
  SymbolTable* symbol_table;
  StaticConstContext* static_consts;

  // For pseudo regs.
  Hashmap* stack_map;
  int stack_pos;

  // Vec<x64_Instruction>
  Vec* out;
} Context;

static int data_type_to_size_bytes(x64_DataType type) {
  switch (type) {
    case X64_QUADWORD:
    case X64_DOUBLE:
      return 8;
    case X64_LONGWORD:
      return 4;
    default:
      assert(false);
  }
}

static x64_DataType c_to_data_type(CType c_type) {
  switch (c_type.ty) {
    case CTYPE_INT:
    case CTYPE_UINT:
      return X64_LONGWORD;
    case CTYPE_LONG:
    case CTYPE_ULONG:
      return X64_QUADWORD;
    case CTYPE_DOUBLE:
      return X64_DOUBLE;
    default:
      assert(false);
  }
}

static CType symbol_c_type(Context* cx, String* symbol) {
  assert(symbol);
  SymbolTableEntry* st_entry = hashmap_get(cx->symbol_table->map, symbol);
  assert(st_entry);

  switch (st_entry->ty) {
    case ST_LOCAL_VAR:
      return st_entry->local.c_type;
    case ST_STATIC_VAR:
      return st_entry->static_.c_type;
    case ST_FN:
      assert(false);
  }
}

static CType ir_val_c_type(Context* cx, IrVal* val) {
  assert(val);

  if (val->ty == IR_VAL_CONST) {
    return val->constant.c_type;
  }

  return symbol_c_type(cx, val->var);
}

static x64_DataType ir_val_to_data_type(Context* cx, IrVal* val) {
  return c_to_data_type(ir_val_c_type(cx, val));
}

static x64_DataType symbol_to_data_type(Context* cx, String* symbol) {
  return c_to_data_type(symbol_c_type(cx, symbol));
}

static x64_DataType data_type_of(Context* cx, IrInstruction* ir) {
  // This should only be called for instructions that have arguments.
  // In that case, r1 will always be populated. r2 and dst are optional.
  assert(ir->r1);

  x64_DataType type = ir_val_to_data_type(cx, ir->r1);
  if (ir->r2) {
    // assert(size == ir_val_to_data_type(ir->r2));
    x64_DataType r2_type = ir_val_to_data_type(cx, ir->r2);
    if (type != r2_type) {
      panic("instr %lu r1 %lu r2 %lu", ir->ty, type, r2_type);
    }
  }
  if (ir->dst) {
    // assert(type == ir_val_to_data_type(ir->dst));
    x64_DataType dst_type = ir_val_to_data_type(cx, ir->dst);
    if (type != dst_type) {
      panic("instr %lu r1 %lu dst %lu", ir->ty, type, dst_type);
    }
  }
  return type;
}

static x64_RegType fixup_src_reg(x64_DataType type) {
  return type == X64_DOUBLE ? REG_XMM14 : REG_R10;
}

static x64_RegType fixup_dst_reg(x64_DataType type) {
  return type == X64_DOUBLE ? REG_XMM15 : REG_R11;
}

//
// x64_Operand helpers
//

static x64_Operand* imm(uint64_t val, CType c_type) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_IMM;
  ret->imm = val;
  ret->is_signed = type_is_signed(c_type);
  return ret;
}

static inline x64_Operand* reg(x64_RegType ty) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_REG;
  ret->reg = ty;
  return ret;
}

static x64_Operand* stack(int val) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_STACK;
  ret->stack = val;
  return ret;
}

static x64_Operand* data(String* ident, bool constant) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_DATA;
  ret->ident = ident;
  ret->is_constant = constant;
  return ret;
}

// For pseudoregs, provide the symbol table, stack map, and stack pos in |cx| so
// that pseudoregs can be translated to stack addresses immediately. This way,
// we don't need a separate pass to handle pseudoregs.
static x64_Operand* pseudo(Context* cx, String* name) {
  x64_Operand* stack_operand = hashmap_get(cx->stack_map, name);
  if (stack_operand) {
    return stack_operand;
  }

  // If we find a pseudoreg not in |stackmap|, check the symbol table if it's a
  // static variable.
  SymbolTableEntry* st_entry = hashmap_get(cx->symbol_table->map, name);
  assert(st_entry);
  assert(st_entry->ty != ST_FN);

  // Emit data operands for static variables.
  if (st_entry->ty == ST_STATIC_VAR) {
    return data(name, false);
  }

  x64_DataType type = c_to_data_type(st_entry->local.c_type);
  const int bytes = data_type_to_size_bytes(type);
  cx->stack_pos += bytes;

  // align stack pos by rounding up to next multiple of bytes
  if (cx->stack_pos % bytes != 0) {
    cx->stack_pos += bytes - (cx->stack_pos % bytes);
  }

  assert(cx->stack_pos % bytes == 0);

  // allocate a new stack operand if one doesn't exist
  stack_operand = stack(cx->stack_pos * -1);
  hashmap_put(cx->stack_map, name, stack_operand);
  return stack_operand;
}

static x64_Operand* label_op(String* label) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_LABEL;
  ret->ident = label;
  return ret;
}

static String* double_const(Context* cx, double d, int align) {
  // Create a mapping from the actual value of the double to the generated
  // constant label. We don't use the stringified value of the double directly
  // as the label because it may be negative, and the assembler doesn't allow
  // hyphens in labels.

  // Note: %a formats the double as a hexadecimal float which can be thought of
  // as the "whole float". See
  // https://stackoverflow.com/questions/31861160/get-printf-to-print-all-float-digits
  String* double_as_string = string_format("%a", d);
  String* static_const_ident =
      hashmap_get(cx->static_consts->map, double_as_string);
  if (static_const_ident == NULL) {
    // Create a new static constant if this is the first instance.
    static_const_ident =
        string_format(".SC_DOUBLE_%d", cx->static_consts->num++);
    hashmap_put(cx->static_consts->map, double_as_string, static_const_ident);

    x64_StaticConst static_const = {.name = static_const_ident,
                                    .init = {.ty = INIT_HAS_VALUE,
                                             .c_type = {.ty = CTYPE_DOUBLE},
                                             .numeric = {.double_ = d}},
                                    .alignment = align};
    vec_push(cx->static_consts->out, &static_const);
  }

  return static_const_ident;
}

static x64_Operand* to_x64_op(Context* cx, IrVal* ir) {
  if (ir->ty == IR_VAL_VAR) {
    return pseudo(cx, ir->var);
  }

  assert(ir->ty == IR_VAL_CONST);
  CompTimeConst c = ir->constant;

  if (type_is_integer(c.c_type)) {
    return imm(c.numeric.int_, c.c_type);
  }

  assert(c.c_type.ty == CTYPE_DOUBLE);
  return data(double_const(cx, c.numeric.double_, 8), true);
}

static inline bool op_is_stack_or_data(x64_Operand* op) {
  return op->ty == X64_OP_STACK || op->ty == X64_OP_DATA;
}

//
// x64 instruction helpers
//

static inline void push_instr(Context* cx, x64_Instruction instr) {
  *(x64_Instruction*)vec_push_empty(cx->out) = instr;
}

static inline void instr2(Context* cx, x64_InstructionType ty, x64_Operand* r1,
                          x64_Operand* r2, x64_DataType type) {
  push_instr(
      cx, (x64_Instruction){.ty = ty, .r1 = r1, .r2 = r2, .data_type = type});
}

static inline void instr1(Context* cx, x64_InstructionType ty, x64_Operand* r1,
                          x64_DataType type) {
  instr2(cx, ty, r1, NULL, type);
}

static inline void instr0(Context* cx, x64_InstructionType ty,
                          x64_DataType type) {
  instr2(cx, ty, NULL, NULL, type);
}

static inline void label(Context* cx, String* label) {
  push_instr(cx, (x64_Instruction){.ty = X64_LABEL, .r1 = label_op(label)});
}

static inline void setcc(Context* cx, x64_ConditionCode cc, x64_Operand* r1) {
  // Size will be ignored for setcc
  x64_Instruction ret = {
      .ty = X64_SETCC, .r1 = r1, .data_type = X64_QUADWORD, .cc = cc};
  push_instr(cx, ret);
}

static inline void jmp(Context* cx, String* label) {
  push_instr(cx, (x64_Instruction){.ty = X64_JMP, .r1 = label_op(label)});
}

static inline void jmpcc(Context* cx, x64_ConditionCode cc, String* label) {
  push_instr(
      cx, (x64_Instruction){.ty = X64_JMPCC, .cc = cc, .r1 = label_op(label)});
}

static inline void mov(Context* cx, x64_Operand* r1, x64_Operand* r2,
                       x64_DataType type) {
  // Memory to memory moves require an intermediate move to a register.
  bool is_mem_to_mem = op_is_stack_or_data(r1) && op_is_stack_or_data(r2);

  // Can only move 32 bit immediates directly into memory.
  bool imm_too_large = op_is_stack_or_data(r2) && r1->ty == X64_OP_IMM &&
                       r1->imm > (uint64_t)INT_MAX;

  // Doubles shouldn't use immediates, sanity check here.
  assert(!(imm_too_large && type == X64_DOUBLE));

  if (is_mem_to_mem || imm_too_large) {
    // insert intermediate move to fixup reg based on type.
    x64_Operand* fixup = reg(fixup_src_reg(type));
    instr2(cx, X64_MOV, r1, fixup, type);
    instr2(cx, X64_MOV, fixup, r2, type);
  } else {
    instr2(cx, X64_MOV, r1, r2, type);
  }
}

static void cvttsd2si(Context* cx, x64_Operand* src, x64_Operand* dst,
                      x64_DataType dst_type) {
  if (dst->ty == X64_OP_REG) {
    instr2(cx, X64_CVTTSD2SI, src, dst, dst_type);
    return;
  }

  // The destination for CVTSDD2SI must be a reg, so insert an
  // intermediate move here.
  assert(dst->ty == X64_OP_STACK);

  x64_Operand* fixup = reg(fixup_dst_reg(dst_type));
  instr2(cx, X64_CVTTSD2SI, src, fixup, dst_type);
  mov(cx, fixup, dst, dst_type);
}

static void cvtsi2sd(Context* cx, x64_Operand* src, x64_Operand* dst,
                     x64_DataType src_type) {
  if (src->ty == X64_OP_IMM) {
    x64_Operand* fixup = reg(fixup_src_reg(src_type));
    mov(cx, src, fixup, src_type);
    src = fixup;
  }

  if (dst->ty == X64_OP_REG) {
    instr2(cx, X64_CVTSI2SD, src, dst, src_type);
    return;
  }

  // The destination for CVTSI2SD must be a register, so insert an
  // intermediate move to xmm15 here.
  assert(dst->ty == X64_OP_STACK);

  x64_Operand* fixup = reg(fixup_dst_reg(X64_DOUBLE));
  instr2(cx, X64_CVTSI2SD, src, fixup, src_type);
  mov(cx, fixup, dst, X64_DOUBLE);
}

static inline x64_Operand* mov_to_reg(Context* cx, x64_Operand* arg,
                                      x64_RegType reg_ty, x64_DataType type) {
  x64_Operand* reg_op = reg(reg_ty);
  instr2(cx, X64_MOV, arg, reg_op, type);
  return reg_op;
}

x64_Operand* zero(Context* cx, CType c_type) {
  if (type_is_integer(c_type)) {
    static x64_Operand ZERO_INT = {
        .ty = X64_OP_IMM,
        .imm = 0,
    };

    return &ZERO_INT;
  }

  x64_Operand* xmm0 = reg(REG_XMM0);
  instr2(cx, X64_XOR, xmm0, xmm0, X64_DOUBLE);
  return xmm0;
}

static bool imm_bigger_than_int(x64_Operand* op) {
  return op->ty == X64_OP_IMM && op->imm > (uint64_t)INT_MAX;
}

static inline void push(Context* cx, x64_Operand* arg, x64_DataType type) {
  if (imm_bigger_than_int(arg)) {
    arg = mov_to_reg(cx, arg, fixup_src_reg(type), type);
  }
  instr1(cx, X64_PUSH, arg, type);
}

static inline x64_Function* function(String* name) {
  x64_Function* ret = calloc(1, sizeof(x64_Function));
  ret->name = name;
  ret->instructions = vec_new(sizeof(x64_Instruction));
  return ret;
}

static void unary(Context* cx, x64_InstructionType ty, IrInstruction* ir) {
  x64_Operand* dst = to_x64_op(cx, ir->dst);

  x64_DataType type = data_type_of(cx, ir);

  mov(cx, to_x64_op(cx, ir->r1), dst, type);
  instr1(cx, ty, dst, type);
  return;
}

static void binary_inner(Context* cx, x64_InstructionType instr_ty,
                         x64_Operand* r1, x64_Operand* r2, x64_DataType type) {
  if (type == X64_DOUBLE) {
    if (r2->ty == X64_OP_REG) {
      instr2(cx, instr_ty, r1, r2, type);
    } else {
      // For binary ops on doubles, the destination must always be a register.
      x64_Operand* fixup = reg(fixup_dst_reg(type));

      // First, move r2 into the fixup register because r2 contains one of the
      // operands.
      mov(cx, r2, fixup, type);

      // Then perform the binary op on r1 and the fixup register.
      instr2(cx, instr_ty, r1, fixup, type);

      // Then move the result in fixup into r2. Except for CMP, whose result
      // is really in the status register.
      if (instr_ty != X64_CMP) {
        mov(cx, fixup, r2, type);
      }
    }
  } else {
    // integer instruction
    switch (instr_ty) {
      case X64_ADD:
      case X64_SUB: {
        bool is_mem_to_mem = op_is_stack_or_data(r1) && op_is_stack_or_data(r2);
        if (is_mem_to_mem || imm_bigger_than_int(r1)) {
          r1 = mov_to_reg(cx, r1, fixup_src_reg(type), type);
        }

        instr2(cx, instr_ty, r1, r2, type);
        return;
      }
      case X64_MUL: {
        if (imm_bigger_than_int(r1)) {
          r1 = mov_to_reg(cx, r1, fixup_src_reg(type), type);
        }

        if (op_is_stack_or_data(r2)) {
          // mul can't use a stack location as its r2
          x64_Operand* fixup = reg(fixup_dst_reg(type));
          instr2(cx, X64_MOV, r2, fixup, type);
          instr2(cx, X64_MUL, r1, fixup, type);
          instr2(cx, X64_MOV, fixup, r2, type);
        } else {
          instr2(cx, X64_MUL, r1, r2, type);
        }
        return;
      }
      case X64_CMP: {
        const bool requires_fixup =
            (op_is_stack_or_data(r1) && op_is_stack_or_data(r2)) ||
            imm_bigger_than_int(r1);

        if (requires_fixup) {
          // insert intermediate move from r2 to r10
          r1 = mov_to_reg(cx, r1, fixup_src_reg(type), type);
        }

        if (r2->ty == X64_OP_IMM) {
          // cmp can't have an imm as its r2, move r2 to r11 and use r11 as the
          // argument.
          r2 = mov_to_reg(cx, r2, fixup_dst_reg(type), type);
        }

        // cmp r2, r1
        instr2(cx, X64_CMP, r1, r2, type);
        break;
      }
      default:
        instr2(cx, instr_ty, r1, r2, type);
        return;
    }
  }
}

static void binary(Context* cx, x64_InstructionType instr_ty,
                   IrInstruction* ir) {
  x64_DataType type = data_type_of(cx, ir);

  x64_Operand* r1;
  x64_Operand* r2;

  // A bit confusing, but all binary operations first move r1 into dst then do
  // the binary operation on r2, dst. Because r2 becomes the binary op's r1, and
  // dst becomes the binary op's r2, we rename them here.
  {
    x64_Operand* ir_r1 = to_x64_op(cx, ir->r1);
    x64_Operand* ir_r2 = to_x64_op(cx, ir->r2);
    x64_Operand* ir_dst = to_x64_op(cx, ir->dst);

    // mov r1, dst
    mov(cx, ir_r1, ir_dst, type);
    r1 = ir_r2;
    r2 = ir_dst;
  }

  // Fixup binary instruction
  binary_inner(cx, instr_ty, r1, r2, type);
}

static void cmp_and_setcc(Context* cx, x64_ConditionCode cc,
                          IrInstruction* ir) {
  // cmps are different because their dst type is always an int
  x64_DataType r1_type = ir_val_to_data_type(cx, ir->r1);
  assert(ir_val_to_data_type(cx, ir->r2) == r1_type);
  x64_DataType dst_type = ir_val_to_data_type(cx, ir->dst);

  x64_Operand* r1 = to_x64_op(cx, ir->r1);
  x64_Operand* r2 = to_x64_op(cx, ir->r2);
  x64_Operand* dst = to_x64_op(cx, ir->dst);

  binary_inner(cx, X64_CMP, r2, r1, r1_type);

  // mov 0, dst
  mov(cx, imm(0, ir_val_c_type(cx, ir->dst)), dst, dst_type);
  // setcc(cc, dst)
  setcc(cx, cc, dst);
}

static void divide_int(Context* cx, IrInstruction* ir) {
  CType c_type = ir_val_c_type(cx, ir->r1);
  assert(c_type_eq(c_type, ir_val_c_type(cx, ir->r2)));

  x64_DataType type = data_type_of(cx, ir);
  x64_Operand* r1 = to_x64_op(cx, ir->r1);
  x64_Operand* r2 = to_x64_op(cx, ir->r2);
  const bool is_signed = type_is_signed(c_type);

  mov(cx, r1, reg(REG_AX), type);
  if (is_signed) {
    instr0(cx, X64_CDQ, type);
  } else {
    mov(cx, imm(0, c_type), reg(REG_DX), type);
  }

  x64_InstructionType div_instr = is_signed ? X64_IDIV : X64_DIV;

  if (r2->ty == X64_OP_IMM) {
    // idiv isn't allowed with immediate args
    // instead, move the arg into a register then idiv on that
    r2 = mov_to_reg(cx, r2, fixup_src_reg(type), type);
  }
  instr1(cx, div_instr, r2, type);
}

static void movsx(Context* cx, x64_Operand* src, x64_Operand* dst,
                  x64_DataType from, x64_DataType to) {
  if (src->ty == X64_OP_IMM) {
    src = mov_to_reg(cx, src, fixup_src_reg(from), from);
  }

  if (op_is_stack_or_data(dst)) {
    x64_Operand* fixup = reg(fixup_dst_reg(to));
    instr2(cx, X64_MOVSX, src, fixup, to);
    instr2(cx, X64_MOV, fixup, dst, to);
  } else {
    instr2(cx, X64_MOVSX, src, dst, to);
  }
}

static void zero_extend(Context* cx, x64_Operand* src, x64_Operand* dst,
                        x64_DataType from, x64_DataType to) {
  if (dst->ty == X64_OP_REG) {
    // If dst is a reg then simply move from src to dst.
    // Note that this uses |from| as the type, and presumably when the data is
    // read from |dst| it will use dst's type (|to|).
    mov(cx, src, dst, from);
    return;
  }

  x64_Operand* fixup = reg(fixup_dst_reg(from));

  // Note that the fixup register has different types here.
  mov(cx, src, fixup, from);
  mov(cx, fixup, dst, to);
}

static bool use_signed_cc(CType c_type) {
  return type_is_integer(c_type) && type_is_signed(c_type);
}

//
// x64 generation function helpers
//
static const x64_RegType kGpArgRegs[] = {
    REG_DI, REG_SI, REG_DX, REG_CX, REG_R8, REG_R9,
};
#define NUM_GP_ARG_REGS (sizeof(kGpArgRegs) / sizeof(kGpArgRegs[0]))

static const x64_RegType kFpArgRegs[] = {REG_XMM0, REG_XMM1, REG_XMM2,
                                         REG_XMM3, REG_XMM4, REG_XMM5,
                                         REG_XMM6, REG_XMM7};
#define NUM_FP_ARG_REGS (sizeof(kFpArgRegs) / sizeof(kFpArgRegs[0]))

// Move arguments from registers/stack into dedicated locations on the stack.
// For simplicity, this currently moves every argument into a new location on
// the stack, but this can definitely be optimized (e.g., reuse the stack
// location for arguments that are passed on the stack).
static int retrieve_fn_args(Context* cx, IrFunction* fn) {
  int stack_size = 0;

  // Retrieve arguments from registers or stack and move them
  // into pseudo registers.
  size_t n_gp = 0;
  size_t n_fp = 0;
  size_t n_stack = 0;
  vec_for_each(fn->params, String, param) {
    x64_Operand* arg = NULL;
    x64_DataType param_type = symbol_to_data_type(cx, iter.param);
    const bool is_fp = param_type == X64_DOUBLE;

    if (is_fp && n_fp < NUM_FP_ARG_REGS) {
      arg = reg(kFpArgRegs[n_fp++]);
    } else if (!is_fp && n_gp < NUM_GP_ARG_REGS) {
      arg = reg(kGpArgRegs[n_gp++]);
    } else {
      // arguments are always passed as 8 bytes on the stack.
      int stack_offset = (8 * n_stack++) + 16;
      arg = stack(stack_offset);
    }

    mov(cx, arg, pseudo(cx, iter.param), param_type);

    // Note: this size corresponds to the pseudoreg that the argument is moved
    // into, not the size of the argument passed on the stack (which is always 8
    // bytes currently).
    stack_size += data_type_to_size_bytes(param_type);
  }

  return stack_size;
}

// Put arguments into registers/stack according to the x64 calling convention
// prior to a function call.
static int prepare_fn_call(Context* cx, IrInstruction* ir) {
  assert(ir->ty == IR_FN_CALL);

  //
  // Separate out all the args by where we will pass them.
  //

  Vec* gp_args = vec_new(sizeof(IrVal));
  Vec* fp_args = vec_new(sizeof(IrVal));
  Vec* stack_args = vec_new(sizeof(IrVal));

  vec_for_each(ir->args, IrVal, arg) {
    x64_DataType type = ir_val_to_data_type(cx, iter.arg);
    const bool is_fp = type == X64_DOUBLE;

    if (is_fp && fp_args->len < NUM_FP_ARG_REGS) {
      vec_push(fp_args, iter.arg);
    } else if (!is_fp && gp_args->len < NUM_GP_ARG_REGS) {
      vec_push(gp_args, iter.arg);
    } else {
      vec_push(stack_args, iter.arg);
    }
  }

  assert(gp_args->len <= NUM_GP_ARG_REGS);
  assert(fp_args->len <= NUM_FP_ARG_REGS);

  //
  // Then allocate the arguments to registers/stack.
  //

  int stack_to_dealloc = 0;
  if (stack_args->len % 2) {
    // adjust stack if we have an odd number of arguments.
    // The x64 stack must be 16 byte aligned.
    instr2(cx, X64_SUB, imm(8, (CType){.ty = CTYPE_ULONG}), reg(REG_SP),
           X64_QUADWORD);
    stack_to_dealloc += 8;
  }

  for (size_t i = 0; i < gp_args->len; i++) {
    IrVal* val = vec_get(gp_args, i);
    x64_DataType type = ir_val_to_data_type(cx, val);
    x64_Operand* arg = to_x64_op(cx, val);
    x64_Operand* x64_reg = reg(kGpArgRegs[i]);
    mov(cx, arg, x64_reg, type);
  }

  for (size_t i = 0; i < fp_args->len; i++) {
    IrVal* val = vec_get(fp_args, i);
    x64_DataType type = ir_val_to_data_type(cx, val);
    assert(type == X64_DOUBLE);

    x64_Operand* arg = to_x64_op(cx, val);
    x64_Operand* x64_reg = reg(kFpArgRegs[i]);
    mov(cx, arg, x64_reg, type);
  }

  // Stack arguments must be pushed in reverse.
  // Note: i must be signed here otherwise i >= 0 is always true.
  for (int i = stack_args->len - 1; i >= 0; i--) {
    IrVal* val = vec_get(stack_args, i);
    x64_DataType type = ir_val_to_data_type(cx, val);
    x64_Operand* arg = to_x64_op(cx, val);

    // Note: push will ignore types, but we use them here for
    // convenience.
    if (arg->ty == X64_OP_IMM || arg->ty == X64_OP_REG ||
        type == X64_QUADWORD || type == X64_DOUBLE) {
      push(cx, arg, type);
    } else {
      x64_Operand* fixup = reg(REG_AX);
      mov(cx, arg, fixup, type);
      push(cx, fixup, type);
    }
    // must deallocate stack reserved for arguments pushed onto the
    // stack.
    stack_to_dealloc += 8;
  }

  return stack_to_dealloc;
}

//
// x64 generation passes
//
static x64_Function* convert_function(IrFunction* ir_function, SymbolTable* st,
                                      StaticConstContext* static_consts) {
  x64_Function* ret = function(ir_function->name);
  ret->global = ir_function->global;

  // Reserve space for the first sub instruction to allocate stack space for
  // local variables. We don't yet know how much space to allocate, so this will
  // be filled out at the end of this function.
  vec_push_empty(ret->instructions);

  Context cx = {.symbol_table = st,
                .static_consts = static_consts,
                .stack_map = hashmap_new(),
                .stack_pos = 0,
                .out = ret->instructions};

  ret->stack_size = retrieve_fn_args(&cx, ir_function);

  // Handle instructions in the function.
  vec_for_each(ir_function->instructions, IrInstruction, ir_instr) {
    IrInstruction* ir = iter.ir_instr;
    switch (ir->ty) {
      case IR_RET: {
        // mov $val, %rax
        x64_DataType type = ir_val_to_data_type(&cx, ir->r1);
        x64_Operand* ret = type == X64_DOUBLE ? reg(REG_XMM0) : reg(REG_AX);
        mov(&cx, to_x64_op(&cx, ir->r1), ret, type);

        // type for RET should be ignored.
        instr0(&cx, X64_RET, type);
        break;
      }
      case IR_UNARY_COMPLEMENT: {
        unary(&cx, X64_NOT, ir);
        break;
      }
      case IR_UNARY_NEG: {
        if (type_is_integer(ir_val_c_type(&cx, ir->r1))) {
          unary(&cx, X64_NEG, ir);
        } else {
          assert(ir_val_c_type(&cx, ir->r1).ty == CTYPE_DOUBLE);
          x64_DataType data_type = data_type_of(&cx, ir);

          // Must be 16 byte aligned for xorpd instruction.
          String* neg_zero = double_const(&cx, -0.0, 16);
          x64_Operand* dst = to_x64_op(&cx, ir->dst);
          if (dst->ty == X64_OP_REG) {
            mov(&cx, to_x64_op(&cx, ir->r1), dst, data_type);
            instr2(&cx, X64_XOR, data(neg_zero, true), dst, data_type);
          } else {
            // xorpd requires dst to be a register.
            x64_Operand* fixup = reg(fixup_dst_reg(data_type));
            mov(&cx, to_x64_op(&cx, ir->r1), fixup, data_type);
            instr2(&cx, X64_XOR, data(neg_zero, true), fixup, data_type);
            mov(&cx, fixup, dst, data_type);
          }
        }
        break;
      }
      case IR_ADD: {
        binary(&cx, X64_ADD, ir);
        break;
      }
      case IR_SUB: {
        binary(&cx, X64_SUB, ir);
        break;
      }
      case IR_MUL: {
        binary(&cx, X64_MUL, ir);
        break;
      }
      case IR_GT: {
        assert(
            c_type_eq(ir_val_c_type(&cx, ir->r1), ir_val_c_type(&cx, ir->r2)));
        x64_ConditionCode cc =
            use_signed_cc(ir_val_c_type(&cx, ir->r1)) ? CC_G : CC_A;
        cmp_and_setcc(&cx, cc, ir);
        break;
      }
      case IR_GTEQ: {
        assert(
            c_type_eq(ir_val_c_type(&cx, ir->r1), ir_val_c_type(&cx, ir->r2)));
        x64_ConditionCode cc =
            use_signed_cc(ir_val_c_type(&cx, ir->r1)) ? CC_GE : CC_AE;
        cmp_and_setcc(&cx, cc, ir);
        break;
      }
      case IR_LT: {
        assert(
            c_type_eq(ir_val_c_type(&cx, ir->r1), ir_val_c_type(&cx, ir->r2)));
        x64_ConditionCode cc =
            use_signed_cc(ir_val_c_type(&cx, ir->r1)) ? CC_L : CC_B;
        cmp_and_setcc(&cx, cc, ir);
        break;
      }
      case IR_LTEQ: {
        assert(
            c_type_eq(ir_val_c_type(&cx, ir->r1), ir_val_c_type(&cx, ir->r2)));
        x64_ConditionCode cc =
            use_signed_cc(ir_val_c_type(&cx, ir->r1)) ? CC_LE : CC_BE;
        cmp_and_setcc(&cx, cc, ir);
        break;
      }
      case IR_EQ: {
        cmp_and_setcc(&cx, CC_E, ir);
        break;
      }
      case IR_NEQ: {
        cmp_and_setcc(&cx, CC_NE, ir);
        break;
      }
      case IR_DIV: {
        x64_DataType type = data_type_of(&cx, ir);
        if (type == X64_DOUBLE) {
          binary(&cx, X64_DIV_DOUBLE, ir);
        } else {
          // do integer division and return ax
          divide_int(&cx, ir);
          x64_Operand* dst = to_x64_op(&cx, ir->dst);
          mov(&cx, reg(REG_AX), dst, type);
        }
        break;
      }
      case IR_REM: {
        // do Idiv and return dx
        divide_int(&cx, ir);
        x64_Operand* dst = to_x64_op(&cx, ir->dst);
        x64_DataType type = data_type_of(&cx, ir);
        mov(&cx, reg(REG_DX), dst, type);
        break;
      }
      case IR_JMP: {
        jmp(&cx, ir->label);
        break;
      }
      case IR_JZ: {
        binary_inner(&cx, X64_CMP, zero(&cx, ir_val_c_type(&cx, ir->r1)),
                     to_x64_op(&cx, ir->r1), data_type_of(&cx, ir));
        jmpcc(&cx, CC_E, ir->label);
        break;
      }
      case IR_JNZ: {
        binary_inner(&cx, X64_CMP, zero(&cx, ir_val_c_type(&cx, ir->r1)),
                     to_x64_op(&cx, ir->r1), data_type_of(&cx, ir));
        jmpcc(&cx, CC_NE, ir->label);
        break;
      }
      case IR_LABEL: {
        label(&cx, ir->label);
        break;
      }
      case IR_COPY: {
        mov(&cx, to_x64_op(&cx, ir->r1), to_x64_op(&cx, ir->dst),
            data_type_of(&cx, ir));
        break;
      }
      case IR_SIGN_EXTEND: {
        assert(ir_val_to_data_type(&cx, ir->r1) == X64_LONGWORD);
        assert(ir_val_to_data_type(&cx, ir->dst) == X64_QUADWORD);
        movsx(&cx, to_x64_op(&cx, ir->r1), to_x64_op(&cx, ir->dst),
              X64_LONGWORD, X64_QUADWORD);
        break;
      }
      case IR_TRUNCATE: {
        assert(ir_val_to_data_type(&cx, ir->r1) == X64_QUADWORD);
        assert(ir_val_to_data_type(&cx, ir->dst) == X64_LONGWORD);

        x64_Operand* src = to_x64_op(&cx, ir->r1);

        // Truncate here to placate the assembler.
        if (src->ty == X64_OP_IMM) {
          src->imm = (int)src->imm;
        }

        mov(&cx, src, to_x64_op(&cx, ir->dst), X64_LONGWORD);
        break;
      }
      case IR_ZERO_EXTEND: {
        x64_Operand* src = to_x64_op(&cx, ir->r1);
        x64_Operand* dst = to_x64_op(&cx, ir->dst);
        x64_DataType src_type = ir_val_to_data_type(&cx, ir->r1);
        x64_DataType dst_type = ir_val_to_data_type(&cx, ir->dst);
        zero_extend(&cx, src, dst, src_type, dst_type);
        break;
      }
      case IR_DOUBLE_TO_INT: {
        assert(ir_val_c_type(&cx, ir->r1).ty == CTYPE_DOUBLE);

        x64_Operand* src = to_x64_op(&cx, ir->r1);
        x64_Operand* dst = to_x64_op(&cx, ir->dst);

        // In this case, the type of dst (signed integer) determines the type of
        // the instruction.
        x64_DataType type = ir_val_to_data_type(&cx, ir->dst);
        cvttsd2si(&cx, src, dst, type);
        break;
      }
      case IR_DOUBLE_TO_UINT: {
        assert(ir_val_c_type(&cx, ir->r1).ty == CTYPE_DOUBLE);

        x64_Operand* src = to_x64_op(&cx, ir->r1);
        x64_Operand* dst = to_x64_op(&cx, ir->dst);

        if (ir_val_c_type(&cx, ir->dst).ty == CTYPE_UINT) {
          // If converting to a uint, then convert to a signed long
          // If the double we're converting from is outside the range of a uint
          // (e.g. negative), then behavior is undefined so anything can happen.
          cvttsd2si(&cx, src, dst, X64_QUADWORD);
          break;
        }

        // Compare against LONG_MAX + 1 to determine how to convert the double
        const double upper_bound_val = 9223372036854775808.0;
        x64_Operand* upper_bound =
            data(double_const(&cx, upper_bound_val, 8), true);
        binary_inner(&cx, X64_CMP, upper_bound, src, X64_DOUBLE);

        static int n = 0;
        String* out_of_range = string_format(".D2UI_OUT_OF_RANGE_%d", n++);
        String* end = string_format(".D2UI_END_%d", n++);

        jmpcc(&cx, CC_AE, out_of_range);

        // If we're in range, we can convert directly using cvtsd2si
        cvttsd2si(&cx, src, dst, X64_QUADWORD);
        jmp(&cx, end);

        // If we're out of range, subtract the upper bound then convert, then
        // add back the upper bound as a ULONG.
        label(&cx, out_of_range);
        x64_Operand* xmm1 = reg(REG_XMM1);
        mov(&cx, src, xmm1, X64_DOUBLE);
        binary_inner(&cx, X64_SUB, upper_bound, xmm1, X64_DOUBLE);

        cvttsd2si(&cx, xmm1, dst, X64_QUADWORD);
        binary_inner(&cx, X64_ADD,
                     imm((uint64_t)LONG_MAX + 1, (CType){.ty = CTYPE_ULONG}),
                     dst, X64_QUADWORD);

        label(&cx, end);
        break;
      }
      case IR_INT_TO_DOUBLE: {
        assert(ir_val_c_type(&cx, ir->dst).ty == CTYPE_DOUBLE);

        x64_Operand* src = to_x64_op(&cx, ir->r1);
        x64_Operand* dst = to_x64_op(&cx, ir->dst);

        // In this case, the type of r1 (long or int) determines the type of the
        // instruction.
        x64_DataType type = ir_val_to_data_type(&cx, ir->r1);
        cvtsi2sd(&cx, src, dst, type);
        break;
      }
      case IR_UINT_TO_DOUBLE: {
        assert(ir_val_c_type(&cx, ir->dst).ty == CTYPE_DOUBLE);
        x64_Operand* src = to_x64_op(&cx, ir->r1);
        x64_Operand* dst = to_x64_op(&cx, ir->dst);
        x64_DataType src_type = ir_val_to_data_type(&cx, ir->r1);
        CType src_c_type = ir_val_c_type(&cx, ir->r1);

        if (ir_val_c_type(&cx, ir->r1).ty == CTYPE_UINT) {
          // Similar to double to UINT. Zero extend to a signed long then
          // convert.
          x64_Operand* ax = reg(REG_AX);
          zero_extend(&cx, src, ax, src_type, X64_QUADWORD);
          cvtsi2sd(&cx, ax, dst, X64_QUADWORD);
          break;
        }

        static int n = 0;
        String* out_of_range = string_format(".UI2D_OUT_OF_RANGE_%d", n++);
        String* end = string_format(".UI2D_END_%d", n++);

        binary_inner(&cx, X64_CMP, zero(&cx, src_c_type), src, src_type);
        jmpcc(&cx, CC_L, out_of_range);
        cvtsi2sd(&cx, src, dst, src_type);
        jmp(&cx, end);
        label(&cx, out_of_range);

        if (src->ty != X64_OP_REG) {
          x64_Operand* ax = reg(REG_AX);
          mov(&cx, src, ax, src_type);
          src = ax;
        }

        assert(src->reg != REG_DX);
        x64_Operand* dx = reg(REG_DX);
        mov(&cx, src, dx, src_type);
        instr1(&cx, X64_SHR, dx, src_type);
        instr2(&cx, X64_AND, imm(1, src_c_type), src, src_type);
        instr2(&cx, X64_OR, src, dx, src_type);
        cvtsi2sd(&cx, dx, dst, src_type);
        binary_inner(&cx, X64_ADD, dst, dst, X64_DOUBLE);
        label(&cx, end);
        break;
      }
      case IR_FN_CALL: {
        int stack_to_dealloc = prepare_fn_call(&cx, ir);

        // Call the function
        x64_Instruction call = {
            .ty = X64_CALL,
            .r1 = label_op(ir->label),
        };
        push_instr(&cx, call);

        // Deallocate stack if necessary.
        if (stack_to_dealloc) {
          instr2(&cx, X64_ADD,
                 imm(stack_to_dealloc, (CType){.ty = CTYPE_ULONG}), reg(REG_SP),
                 X64_QUADWORD);
        }

        // Move the return value in RAX to the call's destination.
        x64_DataType type = ir_val_to_data_type(&cx, ir->dst);
        x64_Operand* dst = to_x64_op(&cx, ir->dst);
        x64_Operand* ret = type == X64_DOUBLE ? reg(REG_XMM0) : reg(REG_AX);
        mov(&cx, ret, dst, type);
        break;
      }
      default:
        panic("Unexpected IR instruction type: %lu", iter.ir_instr->ty);
    }
  }

  ret->stack_size = cx.stack_pos;
  if (ret->stack_size % 16) {
    ret->stack_size += (16 - ret->stack_size % 16);
  }

  // Fill out alloc_stack instruction at the start of the function.
  // Note that this has to be accessed here. If we access it and save it at the
  // beginning of the function, the vector may be reallocated by the time we get
  // here.
  x64_Instruction* alloc_stack = vec_get(ret->instructions, 0);
  *alloc_stack = (x64_Instruction){
      .ty = X64_SUB,
      .r1 = imm(ret->stack_size, (CType){.ty = CTYPE_ULONG}),
      .r2 = reg(REG_SP),
      .data_type = X64_QUADWORD,
  };

  return ret;
}

x64_StaticVariable* convert_static_variable(IrStaticVariable* ir) {
  x64_StaticVariable* ret = calloc(1, sizeof(x64_StaticVariable));
  ret->name = ir->name;
  ret->global = ir->global;
  ret->init = ir->init;
  switch (ret->init.c_type.ty) {
    case CTYPE_INT:
    case CTYPE_UINT:
      ret->alignment = 4;
      break;
    case CTYPE_LONG:
    case CTYPE_ULONG:
    case CTYPE_DOUBLE:
      ret->alignment = 8;
      break;
    case CTYPE_NONE:
      assert(false);
  }
  assert(ret->init.ty != INIT_TENTATIVE);
  return ret;
}

x64_Program* generate_x64(IrProgram* ast_program) {
  x64_Program* x64_prog = calloc(1, sizeof(x64_Program));
  x64_prog->functions = vec_new(sizeof(x64_Function));
  x64_prog->static_variables = vec_new(sizeof(x64_StaticVariable));
  x64_prog->static_constants = vec_new(sizeof(x64_StaticConst));

  StaticConstContext static_consts = {
      .out = x64_prog->static_constants, .map = hashmap_new(), .num = 0};

  // Generate function bodies
  vec_for_each(ast_program->functions, IrFunction, ir_func) {
    x64_Function* f = convert_function(iter.ir_func, ast_program->symbol_table,
                                       &static_consts);
    vec_push(x64_prog->functions, f);
  }

  // Generate static variables
  vec_for_each(ast_program->static_variables, IrStaticVariable,
               ir_static_variable) {
    vec_push(x64_prog->static_variables,
             convert_static_variable(iter.ir_static_variable));
  }

  return x64_prog;
}
