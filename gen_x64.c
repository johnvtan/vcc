#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <vcc/errors.h>
#include <vcc/gen_x64.h>
#include <vcc/hashmap.h>

typedef struct {
  SymbolTable* symbol_table;

  // For pseudo regs.
  Hashmap* stack_map;
  int stack_pos;

  // Vec<x64_Instruction>
  Vec* out;
} Context;

static int size_to_bytes(x64_Size size) {
  switch (size) {
    case QUADWORD:
      return 8;
    case LONGWORD:
      return 4;
    default:
      assert(false);
  }
}

static x64_Size type_to_size(CType c_type) {
  switch (c_type) {
    case TYPE_INT:
    case TYPE_UINT:
      return LONGWORD;
    case TYPE_LONG:
    case TYPE_ULONG:
      return QUADWORD;
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

static x64_Size ir_val_to_size(Context* cx, IrVal* val) {
  return type_to_size(ir_val_c_type(cx, val));
}

static x64_Size symbol_to_size(Context* cx, String* symbol) {
  return type_to_size(symbol_c_type(cx, symbol));
}

static x64_Size asm_size_of(Context* cx, IrInstruction* ir) {
  // This should only be called for instructions that have arguments.
  // In that case, r1 will always be populated. r2 and dst are optional.
  assert(ir->r1);

  x64_Size size = ir_val_to_size(cx, ir->r1);
  if (ir->r2) {
    // assert(size == ir_val_to_size(ir->r2));
    x64_Size r2_size = ir_val_to_size(cx, ir->r2);
    if (size != r2_size) {
      panic("instr %lu r1 %lu r2 %lu", ir->ty, size, r2_size);
    }
  }
  if (ir->dst) {
    // assert(size == ir_val_to_size(ir->dst));
    x64_Size dst_size = ir_val_to_size(cx, ir->dst);
    if (size != dst_size) {
      panic("instr %lu r1 %lu dst %lu", ir->ty, size, dst_size);
    }
  }
  return size;
}

static x64_Operand ZERO = {
    .ty = X64_OP_IMM,
    .imm = 0,
};

//
// x64_Operand helpers
//

static x64_Operand* imm(uint64_t val, bool sign) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_IMM;
  ret->imm = val;
  ret->sign = sign;
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

static x64_Operand* data(String* ident) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_DATA;
  ret->ident = ident;
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
    return data(name);
  }

  x64_Size size = type_to_size(st_entry->local.c_type);
  const int bytes = size_to_bytes(size);
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

static x64_Operand* to_x64_op(Context* cx, IrVal* ir) {
  x64_Operand* ret = NULL;
  switch (ir->ty) {
    case IR_VAL_CONST:
      ret = imm(ir->constant.storage_, ir->constant.c_type);
      break;
    case IR_VAL_VAR:
      ret = pseudo(cx, ir->var);
      break;
    default:
      panic("Unexpected IrVal type %lu", ir->ty);
  }

  return ret;
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
                          x64_Operand* r2, x64_Size size) {
  push_instr(cx, (x64_Instruction){.ty = ty, .r1 = r1, .r2 = r2, .size = size});
}

static inline void instr1(Context* cx, x64_InstructionType ty, x64_Operand* r1,
                          x64_Size size) {
  instr2(cx, ty, r1, NULL, size);
}

static inline void instr0(Context* cx, x64_InstructionType ty, x64_Size size) {
  instr2(cx, ty, NULL, NULL, size);
}

static inline void label(Context* cx, String* label) {
  push_instr(cx, (x64_Instruction){.ty = X64_LABEL, .r1 = label_op(label)});
}

static inline void setcc(Context* cx, x64_ConditionCode cc, x64_Operand* r1) {
  // Size will be ignored for setcc
  x64_Instruction ret = {.ty = X64_SETCC, .r1 = r1, .size = QUADWORD, .cc = cc};
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
                       x64_Size size) {
  // Memory to memory moves require an intermediate move to a register.
  bool is_mem_to_mem = op_is_stack_or_data(r1) && op_is_stack_or_data(r2);

  // Can only move 32 bit immediates directly into memory.
  bool imm_too_large = op_is_stack_or_data(r2) && r1->ty == X64_OP_IMM &&
                       r1->imm > (uint64_t)INT_MAX;
  if (is_mem_to_mem || imm_too_large) {
    // insert intermediate move to r10
    x64_Operand* r10 = reg(REG_R10);
    instr2(cx, X64_MOV, r1, r10, size);
    instr2(cx, X64_MOV, r10, r2, size);
  } else {
    instr2(cx, X64_MOV, r1, r2, size);
  }
}

static inline void push(Context* cx, x64_Operand* arg, x64_Size size) {
  if (arg->ty == X64_OP_IMM && arg->imm > INT_MAX) {
    // insert intermediate move to r10
    x64_Operand* r10 = reg(REG_R10);
    instr2(cx, X64_MOV, arg, r10, size);
    instr1(cx, X64_PUSH, r10, size);
  } else {
    instr1(cx, X64_PUSH, arg, size);
  }
}

static inline x64_Function* function(String* name) {
  x64_Function* ret = calloc(1, sizeof(x64_Function));
  ret->name = name;
  ret->instructions = vec_new(sizeof(x64_Instruction));
  return ret;
}

static void unary(Context* cx, x64_InstructionType ty, IrInstruction* ir) {
  x64_Operand* dst = to_x64_op(cx, ir->dst);

  x64_Size size = asm_size_of(cx, ir);

  mov(cx, to_x64_op(cx, ir->r1), dst, size);
  instr1(cx, ty, dst, size);
  return;
}

static bool imm_bigger_than_int(x64_Operand* op) {
  return op->ty == X64_OP_IMM && op->imm > (uint64_t)INT_MAX;
}

static void binary(Context* cx, x64_InstructionType ty, IrInstruction* ir) {
  x64_Size size = asm_size_of(cx, ir);

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
    mov(cx, ir_r1, ir_dst, size);
    r1 = ir_r2;
    r2 = ir_dst;
  }

  switch (ty) {
    case X64_ADD:
    case X64_SUB: {
      bool is_mem_to_mem = op_is_stack_or_data(r1) && op_is_stack_or_data(r2);
      if (is_mem_to_mem || imm_bigger_than_int(r1)) {
        x64_Operand* r10 = reg(REG_R10);
        instr2(cx, X64_MOV, r1, r10, size);
        instr2(cx, ty, r10, r2, size);
      } else {
        instr2(cx, ty, r1, r2, size);
      }
      return;
    }
    case X64_MUL: {
      if (imm_bigger_than_int(r1)) {
        x64_Operand* r10 = reg(REG_R10);
        instr2(cx, X64_MOV, r1, r10, size);
        r1 = r10;
      }

      if (op_is_stack_or_data(r2)) {
        // mul can't use a stack location as its r2
        x64_Operand* r11 = reg(REG_R11);
        instr2(cx, X64_MOV, r2, r11, size);
        instr2(cx, X64_MUL, r1, r11, size);
        instr2(cx, X64_MOV, r11, r2, size);
      } else {
        instr2(cx, X64_MUL, r1, r2, size);
      }
      return;
    }
    default:
      instr2(cx, ty, r1, r2, size);
      return;
  }

  return;
}

static void cmp(Context* cx, x64_Operand* r1, x64_Operand* r2, x64_Size size) {
  const bool requires_move_to_r10 =
      (op_is_stack_or_data(r1) && op_is_stack_or_data(r2)) ||
      imm_bigger_than_int(r1);

  // if (r1->ty == X64_OP_IMM) {
  //   printf("cmp: imm %lu, imm_bigger_than_int: %u, INT_MAX=%u\n", r1->imm,
  //   imm_bigger_than_int(r1), INT_MAX);
  // }
  if (requires_move_to_r10) {
    // insert intermediate move from r2 to r10
    x64_Operand* r10 = reg(REG_R10);
    instr2(cx, X64_MOV, r1, r10, size);
    r1 = r10;
  }

  if (r2->ty == X64_OP_IMM) {
    // cmp can't have an imm as its r2, move r2 to r11 and use r11 as the
    // argument.
    x64_Operand* r11 = reg(REG_R11);
    mov(cx, r2, r11, size);
    r2 = r11;
  }

  // cmp r2, r1
  instr2(cx, X64_CMP, r1, r2, size);
}

static void cmp_and_setcc(Context* cx, x64_ConditionCode cc,
                          IrInstruction* ir) {
  // cmps are different because their dst type is always an int
  x64_Size r1_size = ir_val_to_size(cx, ir->r1);
  assert(ir_val_to_size(cx, ir->r2) == r1_size);
  x64_Size dst_size = ir_val_to_size(cx, ir->dst);

  x64_Operand* r1 = to_x64_op(cx, ir->r1);
  x64_Operand* r2 = to_x64_op(cx, ir->r2);
  x64_Operand* dst = to_x64_op(cx, ir->dst);

  cmp(cx, r2, r1, r1_size);

  // mov 0, dst
  mov(cx, imm(0, ir_val_c_type(cx, ir->dst)), dst, dst_size);
  // setcc(cc, dst)
  setcc(cx, cc, dst);
}

static void divide(Context* cx, IrInstruction* ir) {
  CType c_type = ir_val_c_type(cx, ir->r1);
  assert(c_type == ir_val_c_type(cx, ir->r2));

  x64_Size size = asm_size_of(cx, ir);
  x64_Operand* r1 = to_x64_op(cx, ir->r1);
  x64_Operand* r2 = to_x64_op(cx, ir->r2);
  const bool is_signed = type_is_signed(c_type);

  mov(cx, r1, reg(REG_AX), size);
  if (is_signed) {
    instr0(cx, X64_CDQ, size);
  } else {
    mov(cx, imm(0, c_type), reg(REG_DX), size);
  }

  x64_InstructionType div_instr = is_signed ? X64_IDIV : X64_DIV;

  if (r2->ty == X64_OP_IMM) {
    // idiv isn't allowed with immediate args
    // instead, move the arg into a register then idiv on that
    x64_Operand* r10 = reg(REG_R10);
    mov(cx, r2, r10, size);
    instr1(cx, div_instr, r10, size);
  } else {
    instr1(cx, div_instr, r2, size);
  }
}

static void movsx(Context* cx, x64_Operand* r1, x64_Operand* r2, x64_Size from,
                  x64_Size to) {
  if (r1->ty == X64_OP_IMM) {
    x64_Operand* r10 = reg(REG_R10);
    instr2(cx, X64_MOV, r1, r10, from);
    r1 = r10;
  }

  if (op_is_stack_or_data(r2)) {
    x64_Operand* r11 = reg(REG_R11);
    instr2(cx, X64_MOVSX, r1, r11, to);
    instr2(cx, X64_MOV, r11, r2, to);
  } else {
    instr2(cx, X64_MOVSX, r1, r2, to);
  }
}

//
// x64 generation passes
//

static x64_Function* convert_function(IrFunction* ir_function,
                                      SymbolTable* st) {
  x64_Function* ret = function(ir_function->name);
  ret->global = ir_function->global;

  // Reserve space for the first sub instruction to allocate stack space for
  // local variables. We don't yet know how much space to allocate, so this will
  // be filled out at the end of this function.
  vec_push_empty(ret->instructions);

  Context cx = {.symbol_table = st,
                .stack_map = hashmap_new(),
                .stack_pos = 0,
                .out = ret->instructions};

  // Retrieve arguments from registers or stack and move them
  // into pseudo registers.
  static const x64_RegType kArgumentRegs[] = {
      REG_DI, REG_SI, REG_DX, REG_CX, REG_R8, REG_R9,
  };
  const size_t kNumArgumentRegs = 6;

  size_t n = 0;
  vec_for_each(ir_function->params, String, param) {
    x64_Operand* arg = NULL;
    if (n < kNumArgumentRegs) {
      arg = reg(kArgumentRegs[n]);
    } else {
      // arguments are always passed as 8 bytes on the stack.
      int stack_offset = (8 * (n - kNumArgumentRegs)) + 16;
      arg = stack(stack_offset);
    }
    n++;

    x64_Size param_size = symbol_to_size(&cx, iter.param);
    mov(&cx, arg, pseudo(&cx, iter.param), param_size);
    // TODO: correct sizing.
    // Note: this size corresponds to the pseudoreg that the argument is moved
    // into, not the size of the argument passed on the stack (which is always 8
    // bytes currently).
    ret->stack_size += size_to_bytes(param_size);
  }

  // Handle instructions in the function.
  vec_for_each(ir_function->instructions, IrInstruction, ir_instr) {
    IrInstruction* ir = iter.ir_instr;
    switch (ir->ty) {
      case IR_RET: {
        // mov $val, %rax
        x64_Size size = ir_val_to_size(&cx, ir->r1);
        mov(&cx, to_x64_op(&cx, ir->r1), reg(REG_AX), size);

        // size for RET should be ignored.
        instr0(&cx, X64_RET, QUADWORD);
        break;
      }
      case IR_UNARY_COMPLEMENT: {
        unary(&cx, X64_NOT, ir);
        break;
      }
      case IR_UNARY_NEG: {
        unary(&cx, X64_NEG, ir);
        break;
      }
      case IR_UNARY_NOT: {
        // this is rewritten as a cmp 0, r1
        ir->r2 = ir->r1;
        ir->r1 = constant(zero(ir_val_c_type(&cx, ir->r1)));
        cmp_and_setcc(&cx, CC_E, ir);
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
        assert(ir_val_c_type(&cx, ir->r1) == ir_val_c_type(&cx, ir->r2));
        if (type_is_signed(ir_val_c_type(&cx, ir->r1))) {
          cmp_and_setcc(&cx, CC_G, ir);
        } else {
          cmp_and_setcc(&cx, CC_A, ir);
        }
        break;
      }
      case IR_GTEQ: {
        assert(ir_val_c_type(&cx, ir->r1) == ir_val_c_type(&cx, ir->r2));
        if (type_is_signed(ir_val_c_type(&cx, ir->r1))) {
          cmp_and_setcc(&cx, CC_GE, ir);
        } else {
          cmp_and_setcc(&cx, CC_AE, ir);
        }
        break;
      }
      case IR_LT: {
        assert(ir_val_c_type(&cx, ir->r1) == ir_val_c_type(&cx, ir->r2));
        if (type_is_signed(ir_val_c_type(&cx, ir->r1))) {
          cmp_and_setcc(&cx, CC_L, ir);
        } else {
          cmp_and_setcc(&cx, CC_B, ir);
        }
        break;
      }
      case IR_LTEQ: {
        assert(ir_val_c_type(&cx, ir->r1) == ir_val_c_type(&cx, ir->r2));
        if (type_is_signed(ir_val_c_type(&cx, ir->r1))) {
          cmp_and_setcc(&cx, CC_LE, ir);
        } else {
          cmp_and_setcc(&cx, CC_BE, ir);
        }
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
        // do Idiv and return ax
        divide(&cx, ir);
        x64_Operand* dst = to_x64_op(&cx, ir->dst);
        x64_Size size = asm_size_of(&cx, ir);
        mov(&cx, reg(REG_AX), dst, size);
        break;
      }
      case IR_REM: {
        // do Idiv and return dx
        divide(&cx, ir);
        x64_Operand* dst = to_x64_op(&cx, ir->dst);
        x64_Size size = asm_size_of(&cx, ir);
        mov(&cx, reg(REG_DX), dst, size);
        break;
      }
      case IR_JMP: {
        jmp(&cx, ir->label);
        break;
      }
      case IR_JZ: {
        cmp(&cx, &ZERO, to_x64_op(&cx, ir->r1), asm_size_of(&cx, ir));
        jmpcc(&cx, CC_E, ir->label);
        break;
      }
      case IR_JNZ: {
        cmp(&cx, &ZERO, to_x64_op(&cx, ir->r1), asm_size_of(&cx, ir));
        jmpcc(&cx, CC_NE, ir->label);
        break;
      }
      case IR_LABEL: {
        label(&cx, ir->label);
        break;
      }
      case IR_COPY: {
        mov(&cx, to_x64_op(&cx, ir->r1), to_x64_op(&cx, ir->dst),
            asm_size_of(&cx, ir));
        break;
      }
      case IR_SIGN_EXTEND: {
        assert(ir_val_to_size(&cx, ir->r1) == LONGWORD);
        assert(ir_val_to_size(&cx, ir->dst) == QUADWORD);
        movsx(&cx, to_x64_op(&cx, ir->r1), to_x64_op(&cx, ir->dst), LONGWORD,
              QUADWORD);
        break;
      }
      case IR_TRUNCATE: {
        assert(ir_val_to_size(&cx, ir->r1) == QUADWORD);
        assert(ir_val_to_size(&cx, ir->dst) == LONGWORD);

        x64_Operand* src = to_x64_op(&cx, ir->r1);

        // Truncate here to placate the assembler.
        if (src->ty == X64_OP_IMM) {
          src->imm = (int)src->imm;
        }

        mov(&cx, src, to_x64_op(&cx, ir->dst), LONGWORD);
        break;
      }
      case IR_ZERO_EXTEND: {
        assert(ir->r1);
        assert(ir->dst);
        x64_Operand* src = to_x64_op(&cx, ir->r1);
        x64_Operand* dst = to_x64_op(&cx, ir->dst);
        x64_Size size = ir_val_to_size(&cx, ir->r1);

        if (dst->ty == X64_OP_REG) {
          mov(&cx, src, dst, size);
        } else {
          x64_Size dst_size = ir_val_to_size(&cx, ir->dst);

          // Note that each R11 has different sizes here.
          // TODO: I bet I can remove the sizes from each individual register
          // and rely on the instruction size instead.
          mov(&cx, src, reg(REG_R11), size);
          mov(&cx, reg(REG_R11), dst, dst_size);
        }
        break;
      }
      case IR_FN_CALL: {
        int stack_to_dealloc = 0;
        // adjust stack if we have an odd number of arguments.
        // The x64 stack must be 16 byte aligned.
        if (ir->args->len > kNumArgumentRegs && (ir->args->len % 2)) {
          instr2(&cx, X64_SUB, imm(8, TYPE_ULONG), reg(REG_SP), QUADWORD);
          stack_to_dealloc += 8;
        }

        // pass first 6 arguments in registers
        for (size_t i = 0; (i < kNumArgumentRegs) && (i < ir->args->len); i++) {
          IrVal* val = vec_get(ir->args, i);
          x64_Size size = ir_val_to_size(&cx, val);
          x64_Operand* arg = to_x64_op(&cx, val);
          x64_Operand* x64_reg = reg(kArgumentRegs[i]);
          mov(&cx, arg, x64_reg, size);
        }

        // pass remaining arguments onto the stack in reverse.
        if (ir->args->len > kNumArgumentRegs) {
          for (size_t i = ir->args->len - 1; i >= kNumArgumentRegs; i--) {
            IrVal* val = vec_get(ir->args, i);
            x64_Size size = ir_val_to_size(&cx, val);
            x64_Operand* arg = to_x64_op(&cx, val);

            // Note: push will ignore sizes, but we use them here for
            // convenience.
            if (arg->ty == X64_OP_IMM || arg->ty == X64_OP_REG ||
                size == QUADWORD) {
              push(&cx, arg, size);
            } else {
              x64_Operand* rax = reg(REG_AX);
              mov(&cx, arg, rax, size);
              push(&cx, rax, size);
            }
            // must deallocate stack reserved for arguments pushed onto the
            // stack.
            stack_to_dealloc += 8;
          }
        }

        // Call the function
        x64_Instruction call = {
            .ty = X64_CALL,
            .r1 = label_op(ir->label),
        };
        push_instr(&cx, call);

        // Deallocate stack if necessary.
        if (stack_to_dealloc) {
          instr2(&cx, X64_ADD, imm(stack_to_dealloc, false), reg(REG_SP),
                 QUADWORD);
        }

        // Move the return value in RAX to the call's destination.
        x64_Size size = ir_val_to_size(&cx, ir->dst);
        x64_Operand* dst = to_x64_op(&cx, ir->dst);
        mov(&cx, reg(REG_AX), dst, size);
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
      .r1 = imm(ret->stack_size, false),
      .r2 = reg(REG_SP),
      .size = QUADWORD,
  };

  return ret;
}

x64_StaticVariable* convert_static_variable(IrStaticVariable* ir) {
  x64_StaticVariable* ret = calloc(1, sizeof(x64_StaticVariable));
  ret->name = ir->name;
  ret->global = ir->global;
  ret->init = ir->init;
  switch (ret->init.c_type) {
    case TYPE_INT:
    case TYPE_UINT:
      ret->alignment = 4;
      break;
    case TYPE_LONG:
    case TYPE_ULONG:
      ret->alignment = 8;
      break;
    default:
      assert(false);
  }
  assert(ret->init.ty != INIT_TENTATIVE);
  return ret;
}

x64_Program* generate_x86(IrProgram* ast_program) {
  x64_Program* x64_prog = calloc(1, sizeof(x64_Program));
  x64_prog->functions = vec_new(sizeof(x64_Function));
  x64_prog->static_variables = vec_new(sizeof(x64_StaticVariable));
  vec_for_each(ast_program->functions, IrFunction, ir_func) {
    x64_Function* f = convert_function(iter.ir_func, ast_program->symbol_table);
    vec_push(x64_prog->functions, f);
  }

  vec_for_each(ast_program->static_variables, IrStaticVariable,
               ir_static_variable) {
    vec_push(x64_prog->static_variables,
             convert_static_variable(iter.ir_static_variable));
  }
  return x64_prog;
}
