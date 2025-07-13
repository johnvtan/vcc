#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <vcc/errors.h>
#include <vcc/gen_x64.h>
#include <vcc/hashmap.h>

typedef struct {
  SymbolTable* symbol_table;

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
      return LONGWORD;
    case TYPE_LONG:
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
static x64_Operand* imm(int64_t val) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_IMM;
  ret->imm = val;
  return ret;
}

static inline x64_Operand* reg(x64_RegType ty, x64_Size size) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_REG;
  ret->reg = ty;
  ret->size = size;
  return ret;
}

static x64_Operand* pseudo(String* name) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_PSEUDO;
  ret->pseudo = name;
  return ret;
}

static x64_Operand* stack(int val, x64_Size size) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_STACK;
  ret->stack = val;
  ret->size = size;
  return ret;
}

static x64_Operand* label_op(String* label) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_LABEL;
  ret->ident = label;
  ret->size = 0;
  return ret;
}

static x64_Operand* data(String* ident, x64_Size size) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_DATA;
  ret->ident = ident;
  ret->size = size;
  return ret;
}

static x64_Operand* to_x64_op(Context* cx, IrVal* ir) {
  x64_Operand* ret = NULL;
  switch (ir->ty) {
    case IR_VAL_CONST:
      ret = imm(ir->constant.storage_);
      break;
    case IR_VAL_VAR:
      ret = pseudo(ir->var);
      break;
    default:
      panic("Unexpected IrVal type %lu", ir->ty);
  }

  ret->size = ir_val_to_size(cx, ir);
  return ret;
}

//
// x64 instruction helpers
// TODO(johntan): If I want to remove the other passes, I might need to change
// the API of all the instruction generation functions. It might be better to
// have all of them take the |out| instruction vector directly, so that these
// functions can insert e.g. additional moves or whatever.
//
// Or instead, just make the |out| instruction vector a global that these
// functions push to directly.
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
  instr2(cx, X64_MOV, r1, r2, size);
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

static void binary(Context* cx, x64_InstructionType ty, IrInstruction* ir) {
  x64_Size size = asm_size_of(cx, ir);

  x64_Operand* r1 = to_x64_op(cx, ir->r1);
  x64_Operand* r2 = to_x64_op(cx, ir->r2);
  x64_Operand* dst = to_x64_op(cx, ir->dst);

  // mov r1, dst
  mov(cx, r1, dst, size);

  // {op} r2, dst
  instr2(cx, ty, r2, dst, size);
  return;
}

static void comparison(Context* cx, x64_ConditionCode cc, IrInstruction* ir) {
  // comparisons are different because their dst type is always an int
  x64_Size r1_size = ir_val_to_size(cx, ir->r1);
  assert(ir_val_to_size(cx, ir->r2) == r1_size);
  x64_Size dst_size = ir_val_to_size(cx, ir->dst);

  x64_Operand* r1 = to_x64_op(cx, ir->r1);
  x64_Operand* r2 = to_x64_op(cx, ir->r2);
  x64_Operand* dst = to_x64_op(cx, ir->dst);

  // cmp r2, r1
  instr2(cx, X64_CMP, r2, r1, r1_size);
  // mov 0, dst
  mov(cx, imm(0), dst, dst_size);
  // setcc(cc, dst)
  setcc(cx, cc, dst);
}

static void idiv(Context* cx, IrInstruction* ir) {
  x64_Size size = asm_size_of(cx, ir);
  x64_Operand* r1 = to_x64_op(cx, ir->r1);
  x64_Operand* r2 = to_x64_op(cx, ir->r2);

  mov(cx, r1, reg(REG_AX, size), size);
  instr0(cx, X64_CDQ, size);
  instr1(cx, X64_IDIV, r2, size);
}

// Returns the fixed-up x64_Operand for |operand|.
// If |operand| is not a pseudoreg, this does nothing and returns |operand|.
// If |operand| is a pseudoreg, then it finds or inserts its position in |h|.
// This changes |stack_pos| if this is the first time we encounter |operand|.
static x64_Operand* fixup_pseudoreg(Context* cx, Hashmap* stackmap,
                                    x64_Operand* operand, int* stack_pos) {
  if (!operand || operand->ty != X64_OP_PSEUDO) {
    return operand;
  }

  x64_Operand* stack_operand = hashmap_get(stackmap, operand->pseudo);
  if (stack_operand) {
    return stack_operand;
  }

  // If we find a pseudoreg not in |stackmap|, check the symbol table if it's a
  // static variable.
  SymbolTableEntry* st_entry =
      hashmap_get(cx->symbol_table->map, operand->pseudo);
  assert(st_entry);
  assert(st_entry->ty != ST_FN);

  // Emit data operands for static variables.
  if (st_entry->ty == ST_STATIC_VAR) {
    x64_Size size = type_to_size(st_entry->static_.c_type);
    return data(operand->pseudo, size);
  }

  // TODO: i guess pseudoregs don't have their size filled out.
  x64_Size size = type_to_size(st_entry->local.c_type);
  const int bytes = size_to_bytes(size);
  *stack_pos += bytes;

  // align stack pos by rounding up to next multiple of bytes
  if (*stack_pos % bytes != 0) {
    *stack_pos += bytes - (*stack_pos % bytes);
  }

  assert(*stack_pos % bytes == 0);

  // allocate a new stack operand if one doesn't exist
  stack_operand = stack(*stack_pos * -1, size);
  hashmap_put(stackmap, operand->pseudo, stack_operand);
  return stack_operand;
}

static inline bool op_is_stack_or_data(x64_Operand* op) {
  return op->ty == X64_OP_STACK || op->ty == X64_OP_DATA;
}

static bool is_mem_to_mem(x64_Instruction* instr) {
  switch (instr->ty) {
    case X64_MOV:
    case X64_ADD:
    case X64_SUB:
    case X64_CMP:
      break;
    default:
      return false;
  }

  assert(instr->r1 && instr->r2);
  return op_is_stack_or_data(instr->r1) && op_is_stack_or_data(instr->r2);
}

static bool imm_too_large(x64_Instruction* instr) {
  switch (instr->ty) {
    case X64_MOV:
      if (!op_is_stack_or_data(instr->r2)) {
        return false;
      }
    case X64_ADD:
    case X64_SUB:
    case X64_PUSH:
      if (instr->r1->ty == X64_OP_IMM && instr->r1->imm > INT_MAX) {
        return true;
      }
    default:
      return false;
  }
}

static bool requires_intermediate_register_mov(x64_Instruction* instr) {
  return is_mem_to_mem(instr) || imm_too_large(instr);
}

static void insert_intermediate_move(Context* cx, x64_Instruction* instr) {
  // mov r1, %r10d
  // {op} %r10d, r2
  x64_Operand* r10 = reg(REG_R10, instr->size);
  mov(cx, instr->r1, r10, instr->size);
  instr2(cx, instr->ty, r10, instr->r2, instr->size);
}

//
// x64 generation passes
//
static x64_Function* fixup_instructions(x64_Function* input) {
  x64_Function* ret = function(input->name);
  ret->global = input->global;

  // Round up stack to nearest 16 bytes.
  if (input->stack_size % 16) {
    input->stack_size += (16 - input->stack_size % 16);
  }

  // allocate stack for function local variables.
  Context cx = {.out = ret->instructions};
  instr2(&cx, X64_SUB, imm(input->stack_size), reg(REG_SP, QUADWORD), QUADWORD);
  vec_for_each(input->instructions, x64_Instruction, instr) {
    // TODO refactor
    if (requires_intermediate_register_mov(iter.instr)) {
      insert_intermediate_move(&cx, iter.instr);
      continue;
    } else if (iter.instr->ty == X64_IDIV && iter.instr->r1->ty == X64_OP_IMM) {
      // idiv isn't allowed with immediate args
      // instead, move the arg into a register then idiv on that
      x64_Operand* r10 = reg(REG_R10, iter.instr->size);
      mov(&cx, iter.instr->r1, r10, iter.instr->size);
      instr1(&cx, X64_IDIV, r10, iter.instr->size);
    } else if (iter.instr->ty == X64_MUL) {
      x64_Operand* src = iter.instr->r1;
      if (iter.instr->r1->ty == X64_OP_IMM && iter.instr->r1->imm > INT_MAX) {
        x64_Operand* r10 = reg(REG_R10, iter.instr->size);
        mov(&cx, iter.instr->r1, r10, iter.instr->size);
        src = r10;
      }

      if (op_is_stack_or_data(iter.instr->r2)) {
        // mul can't use a stack location as its r2
        x64_Operand* r11 = reg(REG_R11, iter.instr->size);
        mov(&cx, iter.instr->r2, r11, iter.instr->size);
        instr2(&cx, X64_MUL, src, r11, iter.instr->size);
        mov(&cx, r11, iter.instr->r2, iter.instr->size);
      } else {
        instr2(&cx, X64_MUL, src, iter.instr->r2, iter.instr->size);
      }
    } else if (iter.instr->ty == X64_CMP) {
      x64_Operand* src = iter.instr->r1;

      if (iter.instr->r1->ty == X64_OP_IMM && iter.instr->r1->imm > INT_MAX) {
        x64_Operand* r10 = reg(REG_R10, iter.instr->size);
        mov(&cx, iter.instr->r1, r10, iter.instr->size);
        src = r10;
      }

      if (iter.instr->r2->ty == X64_OP_IMM) {
        // cmp can't have an imm as its r2
        x64_Operand* r11 = reg(REG_R11, iter.instr->size);
        mov(&cx, iter.instr->r2, r11, iter.instr->size);
        instr2(&cx, X64_CMP, src, r11, iter.instr->size);
      } else {
        instr2(&cx, X64_CMP, src, iter.instr->r2, iter.instr->size);
      }
    } else if (iter.instr->ty == X64_MOVSX &&
               (iter.instr->r1->ty == X64_OP_IMM ||
                op_is_stack_or_data(iter.instr->r2))) {
      // movsx can't use imm as source or memory as dst
      x64_Operand* src = iter.instr->r1;
      if (iter.instr->r1->ty == X64_OP_IMM) {
        x64_Operand* r10 = reg(REG_R10, iter.instr->r1->size);
        mov(&cx, iter.instr->r1, r10, iter.instr->r1->size);
        src = r10;
      }
      assert(src->size);

      // For simplicity when fixing up movsx, we always movsx to r11 even if r2
      // is a register.
      x64_Operand* r11 = reg(REG_R11, iter.instr->r2->size);
      assert(r11->size);

      instr2(&cx, X64_MOVSX, src, r11, iter.instr->r2->size);
      mov(&cx, r11, iter.instr->r2, iter.instr->r2->size);
    } else {
      push_instr(&cx, *iter.instr);
    }
  }
  return ret;
}

static x64_Function* replace_pseudoregs(x64_Function* input,
                                        SymbolTable* symbol_table) {
  x64_Function* ret = function(input->name);
  ret->global = input->global;

  Context cx = {.symbol_table = symbol_table, .out = ret->instructions};

  // maps from pseudoreg name -> x64_Operand(stack)
  Hashmap* stack_map = hashmap_new();
  int stack_pos = input->stack_size;
  vec_for_each(input->instructions, x64_Instruction, instr) {
    x64_Instruction cp = *iter.instr;
    cp.r1 = fixup_pseudoreg(&cx, stack_map, iter.instr->r1, &stack_pos);
    cp.r2 = fixup_pseudoreg(&cx, stack_map, iter.instr->r2, &stack_pos);
    push_instr(&cx, cp);
  }

  ret->stack_size = stack_pos;
  return ret;
}

static x64_Function* convert_function(IrFunction* ir_function,
                                      SymbolTable* st) {
  x64_Function* ret = function(ir_function->name);
  ret->global = ir_function->global;

  Context cx = {.symbol_table = st, .out = ret->instructions};

  // Retrieve arguments from registers or stack and move them
  // into pseudo registers.
  static const x64_RegType kArgumentRegs[] = {
      REG_DI, REG_SI, REG_DX, REG_CX, REG_R8, REG_R9,
  };
  const size_t kNumArgumentRegs = 6;

  size_t n = 0;
  vec_for_each(ir_function->params, String, param) {
    x64_Size param_size = symbol_to_size(&cx, iter.param);

    x64_Operand* arg = NULL;
    if (n < kNumArgumentRegs) {
      arg = reg(kArgumentRegs[n], param_size);
    } else {
      // arguments are always passed as 8 bytes on the stack.
      int stack_offset = (8 * (n - kNumArgumentRegs)) + 16;
      arg = stack(stack_offset, param_size);
    }
    n++;

    mov(&cx, arg, pseudo(iter.param), param_size);
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
        mov(&cx, to_x64_op(&cx, ir->r1), reg(REG_AX, size), size);

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
        comparison(&cx, CC_E, ir);
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
        comparison(&cx, CC_G, ir);
        break;
      }
      case IR_GTEQ: {
        comparison(&cx, CC_GE, ir);
        break;
      }
      case IR_LT: {
        comparison(&cx, CC_L, ir);
        break;
      }
      case IR_LTEQ: {
        comparison(&cx, CC_LE, ir);
        break;
      }
      case IR_EQ: {
        comparison(&cx, CC_E, ir);
        break;
      }
      case IR_NEQ: {
        comparison(&cx, CC_NE, ir);
        break;
      }
      case IR_DIV: {
        // do Idiv and return ax
        idiv(&cx, ir);
        x64_Operand* dst = to_x64_op(&cx, ir->dst);
        x64_Size size = asm_size_of(&cx, ir);
        mov(&cx, reg(REG_AX, size), dst, size);
        break;
      }
      case IR_REM: {
        // do Idiv and return dx
        idiv(&cx, ir);
        x64_Operand* dst = to_x64_op(&cx, ir->dst);
        x64_Size size = asm_size_of(&cx, ir);
        mov(&cx, reg(REG_DX, size), dst, size);
        break;
      }
      case IR_JMP: {
        jmp(&cx, ir->label);
        break;
      }
      case IR_JZ: {
        instr2(&cx, X64_CMP, &ZERO, to_x64_op(&cx, ir->r1),
               asm_size_of(&cx, ir));
        jmpcc(&cx, CC_E, ir->label);
        break;
      }
      case IR_JNZ: {
        instr2(&cx, X64_CMP, &ZERO, to_x64_op(&cx, ir->r1),
               asm_size_of(&cx, ir));
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

        instr2(&cx, X64_MOVSX, to_x64_op(&cx, ir->r1), to_x64_op(&cx, ir->dst),
               QUADWORD);
        break;
      }
      case IR_TRUNCATE: {
        assert(ir_val_to_size(&cx, ir->r1) == QUADWORD);
        assert(ir_val_to_size(&cx, ir->dst) == LONGWORD);
        mov(&cx, to_x64_op(&cx, ir->r1), to_x64_op(&cx, ir->dst), LONGWORD);
        break;
      }
      case IR_FN_CALL: {
        int stack_to_dealloc = 0;
        // adjust stack if we have an odd number of arguments.
        // The x64 stack must be 16 byte aligned.
        if (ir->args->len > kNumArgumentRegs && (ir->args->len % 2)) {
          instr2(&cx, X64_SUB, imm(8), reg(REG_SP, QUADWORD), QUADWORD);
          stack_to_dealloc += 8;
        }

        // pass first 6 arguments in registers
        for (size_t i = 0; (i < kNumArgumentRegs) && (i < ir->args->len); i++) {
          IrVal* val = vec_get(ir->args, i);
          x64_Size size = ir_val_to_size(&cx, val);
          x64_Operand* arg = to_x64_op(&cx, val);
          x64_Operand* x64_reg = reg(kArgumentRegs[i], size);
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
              instr1(&cx, X64_PUSH, arg, size);
            } else {
              x64_Operand* rax = reg(REG_AX, arg->size);
              mov(&cx, arg, rax, size);
              instr1(&cx, X64_PUSH, rax, size);
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
          instr2(&cx, X64_ADD, imm(stack_to_dealloc), reg(REG_SP, QUADWORD),
                 QUADWORD);
        }

        // Move the return value in RAX to the call's destination.
        x64_Size size = ir_val_to_size(&cx, ir->dst);
        x64_Operand* dst = to_x64_op(&cx, ir->dst);
        mov(&cx, reg(REG_AX, size), dst, size);
        break;
      }
      default:
        panic("Unexpected IR instruction type: %lu", iter.ir_instr->ty);
    }
  }

  return ret;
}

x64_StaticVariable* convert_static_variable(IrStaticVariable* ir) {
  x64_StaticVariable* ret = calloc(1, sizeof(x64_StaticVariable));
  ret->name = ir->name;
  ret->global = ir->global;
  ret->init = ir->init;
  switch (ret->init.c_type) {
    case TYPE_INT:
      ret->alignment = 4;
      break;
    case TYPE_LONG:
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
    x64_Function* f = fixup_instructions(replace_pseudoregs(
        convert_function(iter.ir_func, ast_program->symbol_table),
        ast_program->symbol_table));
    vec_push(x64_prog->functions, f);
  }

  vec_for_each(ast_program->static_variables, IrStaticVariable,
               ir_static_variable) {
    vec_push(x64_prog->static_variables,
             convert_static_variable(iter.ir_static_variable));
  }
  return x64_prog;
}
