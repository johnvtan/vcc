#include <assert.h>
#include <stdlib.h>
#include <vcc/errors.h>
#include <vcc/gen_x64.h>
#include <vcc/hashmap.h>

//
// x64_Operand helpers
//
static x64_Operand* imm(int val) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_IMM;
  ret->imm = val;
  return ret;
}
static inline x64_Operand* reg(x64_RegType ty) {
  static x64_Operand regs[] = {
      [REG_AX] = (x64_Operand){.ty = X64_OP_REG, .reg = REG_AX},
      [REG_DX] = (x64_Operand){.ty = X64_OP_REG, .reg = REG_DX},
      [REG_R10] = (x64_Operand){.ty = X64_OP_REG, .reg = REG_R10},
      [REG_R11] = (x64_Operand){.ty = X64_OP_REG, .reg = REG_R11},
  };
  return &regs[ty];
}

static x64_Operand* pseudo(String* name) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_PSEUDO;
  ret->pseudo = name;
  return ret;
}
static x64_Operand* stack(int val) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_STACK;
  ret->stack = val;
  return ret;
}

static x64_Operand* to_x64_op(IrVal* ir) {
  switch (ir->ty) {
    case IR_VAL_CONST:
      return imm(ir->constant);
    case IR_VAL_VAR:
      return pseudo(ir->var);
    default:
      panic("Unexpected IrVal type %lu", ir->ty);
  }
}

static inline bool is_pseudo(x64_Operand* op) {
  return op->ty == X64_OP_PSEUDO;
}

//
// x64 instruction helpers
//
static inline x64_Instruction instr2(x64_InstructionType ty, x64_Operand* r1,
                                     x64_Operand* r2) {
  return (x64_Instruction){.ty = ty, .r1 = r1, .r2 = r2};
}

static inline x64_Instruction instr1(x64_InstructionType ty, x64_Operand* r1) {
  return instr2(ty, r1, NULL);
}

static inline x64_Instruction instr0(x64_InstructionType ty) {
  return instr2(ty, NULL, NULL);
}

static inline x64_Instruction mov(x64_Operand* r1, x64_Operand* r2) {
  return instr2(X64_MOV, r1, r2);
}

static inline void push_instr(Vec* out, x64_Instruction instr) {
  *(x64_Instruction*)vec_push_empty(out) = instr;
}

static inline x64_Function* function(String* name) {
  x64_Function* ret = calloc(1, sizeof(x64_Function));
  ret->name = name;
  ret->instructions = vec_new(sizeof(x64_Instruction));
  return ret;
}

static void unary(x64_InstructionType ty, IrInstruction* ir, Vec* out) {
  x64_Operand* dst = to_x64_op(ir->dst);
  push_instr(out, mov(to_x64_op(ir->r1), dst));
  push_instr(out, instr1(ty, dst));
  return;
}

static void binary(x64_InstructionType ty, IrInstruction* ir, Vec* out) {
  x64_Operand* r1 = to_x64_op(ir->r1);
  x64_Operand* r2 = to_x64_op(ir->r2);
  x64_Operand* dst = to_x64_op(ir->dst);

  // mov r1, dst
  push_instr(out, mov(r1, dst));

  // {op} r2, dst
  push_instr(out, instr2(ty, r2, dst));
  return;
}

static void idiv(IrVal* ir_r1, IrVal* ir_r2, Vec* out) {
  x64_Operand* r1 = to_x64_op(ir_r1);
  x64_Operand* r2 = to_x64_op(ir_r2);

  push_instr(out, mov(r1, reg(REG_AX)));
  push_instr(out, instr0(X64_CDQ));
  push_instr(out, instr1(X64_IDIV, r2));
}

// Returns the fixed-up x64_Operand for |operand|.
// If |operand| is not a pseudoreg, this does nothing and returns |operand|.
// If |operand| is a pseudoreg, then it finds or inserts its position in |h|.
// This changes |stack_pos| if this is the first time we encounter |operand|.
static x64_Operand* fixup_pseudoreg(Hashmap* h, x64_Operand* operand,
                                    int* stack_pos) {
  if (!operand || !is_pseudo(operand)) {
    return operand;
  }

  // Casting from void* to int is typically unsafe, but hopefully this is fine
  // because I'm only putting ints in h anyway.
  x64_Operand* stack_operand = hashmap_get(h, operand->pseudo);

  if (!stack_operand) {
    *stack_pos -= 4;

    // allocate a new stack operand if one doesn't exist
    stack_operand = stack(*stack_pos);
    hashmap_put(h, operand->pseudo, stack_operand);
  }
  return stack_operand;
}

static inline bool stack_to_stack_not_allowed(x64_Instruction* instr) {
  bool stack_to_stack = instr->r1 && instr->r1->ty == X64_OP_STACK &&
                        instr->r2 && instr->r2->ty == X64_OP_STACK;

  if (!stack_to_stack) {
    return false;
  }
  return instr->ty == X64_MOV || instr->ty == X64_ADD || instr->ty == X64_SUB;
}

//
// x64 generation passes
//
static x64_Function* fixup_instructions(x64_Function* input, int stack_size) {
  x64_Function* ret = function(input->name);

  push_instr(ret->instructions,
             (x64_Instruction){.ty = X64_ALLOC_STACK, .stack = stack_size});

  vec_for_each(input->instructions, x64_Instruction, instr) {
    if (stack_to_stack_not_allowed(iter.instr)) {
      // split up stack->stack ops into
      // mov r1, %r10d
      // {op} %r10d, r2
      x64_Operand* r10 = reg(REG_R10);
      push_instr(ret->instructions, mov(iter.instr->r1, r10));
      push_instr(ret->instructions,
                 instr2(iter.instr->ty, r10, iter.instr->r2));
      continue;
    }

    if (iter.instr->ty == X64_IDIV && iter.instr->r1->ty == X64_OP_IMM) {
      // idiv isn't allowed with immediate args
      // instead, move the arg into a register then idiv on that
      push_instr(ret->instructions, mov(iter.instr->r1, reg(REG_R10)));
      push_instr(ret->instructions, instr1(X64_IDIV, reg(REG_R10)));
      continue;
    }

    if (iter.instr->ty == X64_MUL && iter.instr->r2->ty == X64_OP_STACK) {
      // mul can't use a stack location as its r2
      push_instr(ret->instructions, mov(iter.instr->r2, reg(REG_R11)));
      push_instr(ret->instructions,
                 instr2(X64_MUL, iter.instr->r1, reg(REG_R11)));
      push_instr(ret->instructions, mov(reg(REG_R11), iter.instr->r2));
      continue;
    }

    push_instr(ret->instructions, *iter.instr);
  }
  return ret;
}

typedef struct {
  x64_Function* function;
  int stack;
} ReplacePseudoregsReturn;
static ReplacePseudoregsReturn replace_pseudoregs(x64_Function* input) {
  x64_Function* ret = function(input->name);

  // maps from pseudoreg name -> x64_Operand(stack)
  Hashmap* stack_map = hashmap_new();
  int stack_pos = 0;
  vec_for_each(input->instructions, x64_Instruction, instr) {
    x64_Operand* r1 = fixup_pseudoreg(stack_map, iter.instr->r1, &stack_pos);
    x64_Operand* r2 = fixup_pseudoreg(stack_map, iter.instr->r2, &stack_pos);
    push_instr(ret->instructions, instr2(iter.instr->ty, r1, r2));
  }

  return (ReplacePseudoregsReturn){.function = ret, .stack = stack_pos};
}

static x64_Function* convert_function(IrFunction* ir_function) {
  x64_Function* ret = function(ir_function->name);
  vec_for_each(ir_function->instructions, IrInstruction, ir_instr) {
    IrInstruction* ir = iter.ir_instr;
    switch (ir->ty) {
      case IR_RET: {
        // mov $val, %rax
        push_instr(ret->instructions, mov(to_x64_op(ir->r1), reg(REG_AX)));
        push_instr(ret->instructions, instr0(X64_RET));
        break;
      }
      case IR_UNARY_COMPLEMENT: {
        unary(X64_NOT, ir, ret->instructions);
        break;
      }
      case IR_UNARY_NEG: {
        unary(X64_NEG, ir, ret->instructions);
        break;
      }
      case IR_ADD: {
        binary(X64_ADD, ir, ret->instructions);
        break;
      }
      case IR_SUB: {
        binary(X64_SUB, ir, ret->instructions);
        break;
      }
      case IR_MUL: {
        binary(X64_MUL, ir, ret->instructions);
        break;
      }
      case IR_DIV: {
        // do Idiv and return ax
        idiv(ir->r1, ir->r2, ret->instructions);
        x64_Operand* dst = to_x64_op(ir->dst);
        push_instr(ret->instructions, mov(reg(REG_AX), dst));
        break;
      }
      case IR_REM: {
        // do Idiv and return dx
        idiv(ir->r1, ir->r2, ret->instructions);
        x64_Operand* dst = to_x64_op(ir->dst);
        push_instr(ret->instructions, mov(reg(REG_DX), dst));
        break;
      }
      default:
        panic("Unexpected IR instruction type: %lu", iter.ir_instr->ty);
    }
  }
  return ret;
}

x64_Program* generate_x86(IrProgram* ast_program) {
  x64_Program* x64_prog = calloc(1, sizeof(x64_Program));

  ReplacePseudoregsReturn ret =
      replace_pseudoregs(convert_function(ast_program->function));

  x64_prog->function = fixup_instructions(ret.function, ret.stack);

  return x64_prog;
}
