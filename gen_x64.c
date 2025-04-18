#include <assert.h>
#include <stdlib.h>
#include <vcc/errors.h>
#include <vcc/gen_x64.h>
#include <vcc/hashmap.h>

static x64_Operand ZERO = {
    .ty = X64_OP_IMM,
    .imm = 0,
};

//
// x64_Operand helpers
//
static x64_Operand* imm(int val) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_IMM;
  ret->imm = val;
  ret->size = 4;
  return ret;
}

static inline x64_Operand* reg(x64_RegType ty, int size) {
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
  ret->size = 4;
  return ret;
}

static x64_Operand* stack(int val) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_STACK;
  ret->stack = val;
  ret->size = 4;
  return ret;
}

static x64_Operand* label_op(String* label) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_LABEL;
  ret->ident = label;
  ret->size = 0;
  return ret;
}

static x64_Operand* data(String* ident) {
  x64_Operand* ret = calloc(1, sizeof(x64_Operand));
  ret->ty = X64_OP_DATA;
  ret->ident = ident;
  ret->size = 4;
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

static inline x64_Instruction alloc_stack(int stack) {
  return (x64_Instruction){.ty = X64_ALLOC_STACK, .stack = stack};
}

static inline x64_Instruction label(String* label) {
  return (x64_Instruction){.ty = X64_LABEL, .r1 = label_op(label)};
}

static inline x64_Instruction setcc(x64_ConditionCode cc, x64_Operand* r1) {
  x64_Instruction ret = instr1(X64_SETCC, r1);
  ret.cc = cc;
  return ret;
}

static inline x64_Instruction jmp(String* label) {
  return (x64_Instruction){.ty = X64_JMP, .r1 = label_op(label)};
}

static inline x64_Instruction jmpcc(x64_ConditionCode cc, String* label) {
  return (x64_Instruction){.ty = X64_JMPCC, .cc = cc, .r1 = label_op(label)};
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

static void comparison(x64_ConditionCode cc, IrVal* ir_r1, IrVal* ir_r2,
                       IrVal* ir_dst, Vec* out) {
  x64_Operand* r1 = to_x64_op(ir_r1);
  x64_Operand* r2 = to_x64_op(ir_r2);
  x64_Operand* dst = to_x64_op(ir_dst);

  // cmp r2, r1
  push_instr(out, instr2(X64_CMP, r2, r1));
  // mov 0, dst
  push_instr(out, mov(imm(0), dst));
  // setcc(cc, dst)
  push_instr(out, setcc(cc, dst));
}

static void idiv(IrVal* ir_r1, IrVal* ir_r2, Vec* out) {
  x64_Operand* r1 = to_x64_op(ir_r1);
  x64_Operand* r2 = to_x64_op(ir_r2);

  push_instr(out, mov(r1, reg(REG_AX, 4)));
  push_instr(out, instr0(X64_CDQ));
  push_instr(out, instr1(X64_IDIV, r2));
}

// Returns the fixed-up x64_Operand for |operand|.
// If |operand| is not a pseudoreg, this does nothing and returns |operand|.
// If |operand| is a pseudoreg, then it finds or inserts its position in |h|.
// This changes |stack_pos| if this is the first time we encounter |operand|.
static x64_Operand* fixup_pseudoreg(SymbolTable* st, Hashmap* stackmap,
                                    x64_Operand* operand, int* stack_pos) {
  if (!operand || !is_pseudo(operand)) {
    return operand;
  }

  x64_Operand* stack_operand = hashmap_get(stackmap, operand->pseudo);
  if (stack_operand) {
    return stack_operand;
  }

  // If we find a pseudoreg not in |stackmap|, check the symbol table if it's a
  // static variable.
  SymbolTableEntry* st_entry = hashmap_get(st->map, operand->pseudo);
  if (st_entry) {
    assert(st_entry->ty != ST_FN);

    // Emit data operands for static variables.
    if (st_entry->ty == ST_STATIC_VAR) {
      return data(operand->pseudo);
    }
    // Allocate local variables on stack.
  }

  *stack_pos += 4;

  // allocate a new stack operand if one doesn't exist
  stack_operand = stack(*stack_pos * -1);
  hashmap_put(stackmap, operand->pseudo, stack_operand);
  return stack_operand;
}

static inline bool op_is_stack_or_data(x64_Operand* op) {
  return op->ty == X64_OP_STACK || op->ty == X64_OP_DATA;
}

static inline bool requires_intermediate_register_mov(x64_Instruction* instr) {
  bool is_affected_instr = instr->ty == X64_MOV || instr->ty == X64_ADD ||
                           instr->ty == X64_SUB || instr->ty == X64_CMP;
  if (!is_affected_instr) {
    return false;
  }

  assert(instr->r1 && instr->r2);
  return op_is_stack_or_data(instr->r1) && op_is_stack_or_data(instr->r2);
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

  push_instr(ret->instructions, alloc_stack(input->stack_size));
  vec_for_each(input->instructions, x64_Instruction, instr) {
    if (requires_intermediate_register_mov(iter.instr)) {
      // split up stack->stack ops into
      // mov r1, %r10d
      // {op} %r10d, r2
      x64_Operand* r10 = reg(REG_R10, 4);
      push_instr(ret->instructions, mov(iter.instr->r1, r10));
      push_instr(ret->instructions,
                 instr2(iter.instr->ty, r10, iter.instr->r2));
      continue;
    } else if (iter.instr->ty == X64_IDIV && iter.instr->r1->ty == X64_OP_IMM) {
      // idiv isn't allowed with immediate args
      // instead, move the arg into a register then idiv on that
      x64_Operand* r10 = reg(REG_R10, 4);
      push_instr(ret->instructions, mov(iter.instr->r1, r10));
      push_instr(ret->instructions, instr1(X64_IDIV, r10));
    } else if (iter.instr->ty == X64_MUL &&
               op_is_stack_or_data(iter.instr->r2)) {
      // mul can't use a stack location as its r2
      x64_Operand* r11 = reg(REG_R11, 4);
      push_instr(ret->instructions, mov(iter.instr->r2, r11));
      push_instr(ret->instructions, instr2(X64_MUL, iter.instr->r1, r11));
      push_instr(ret->instructions, mov(r11, iter.instr->r2));
    } else if (iter.instr->ty == X64_CMP && iter.instr->r2->ty == X64_OP_IMM) {
      // cmp can't have an imm as its r2
      x64_Operand* r11 = reg(REG_R11, 4);
      push_instr(ret->instructions, mov(iter.instr->r2, r11));
      push_instr(ret->instructions, instr2(X64_CMP, iter.instr->r1, r11));
    } else {
      push_instr(ret->instructions, *iter.instr);
    }
  }
  return ret;
}

static x64_Function* replace_pseudoregs(x64_Function* input, SymbolTable* st) {
  x64_Function* ret = function(input->name);
  ret->global = input->global;

  // maps from pseudoreg name -> x64_Operand(stack)
  Hashmap* stack_map = hashmap_new();
  int stack_pos = input->stack_size;
  vec_for_each(input->instructions, x64_Instruction, instr) {
    x64_Instruction cp = *iter.instr;
    cp.r1 = fixup_pseudoreg(st, stack_map, iter.instr->r1, &stack_pos);
    cp.r2 = fixup_pseudoreg(st, stack_map, iter.instr->r2, &stack_pos);
    push_instr(ret->instructions, cp);
  }

  ret->stack_size = stack_pos;
  return ret;
}

static x64_Function* convert_function(IrFunction* ir_function) {
  x64_Function* ret = function(ir_function->name);
  ret->global = ir_function->global;

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
      arg = reg(kArgumentRegs[n], 4);
    } else {
      // arguments are always passed as 8 bytes on the stack.
      int stack_offset = (8 * (n - kNumArgumentRegs)) + 16;
      arg = stack(stack_offset);
    }
    n++;
    push_instr(ret->instructions, mov(arg, pseudo(iter.param)));

    // TODO: correct sizing.
    // Note: this size corresponds to the pseudoreg that the argument is moved
    // into, not the size of the argument passed on the stack (which is always 8
    // bytes currently).
    ret->stack_size += 4;
  }

  // Handle instructions in the function.
  vec_for_each(ir_function->instructions, IrInstruction, ir_instr) {
    IrInstruction* ir = iter.ir_instr;
    switch (ir->ty) {
      case IR_RET: {
        // mov $val, %rax
        push_instr(ret->instructions, mov(to_x64_op(ir->r1), reg(REG_AX, 4)));
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
      case IR_UNARY_NOT: {
        IrVal zero = {
            .ty = IR_VAL_CONST,
            .constant = 0,
        };
        comparison(CC_E, &zero, ir->r1, ir->dst, ret->instructions);
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
      case IR_GT: {
        comparison(CC_G, ir->r1, ir->r2, ir->dst, ret->instructions);
        break;
      }
      case IR_GTEQ: {
        comparison(CC_GE, ir->r1, ir->r2, ir->dst, ret->instructions);
        break;
      }
      case IR_LT: {
        comparison(CC_L, ir->r1, ir->r2, ir->dst, ret->instructions);
        break;
      }
      case IR_LTEQ: {
        comparison(CC_LE, ir->r1, ir->r2, ir->dst, ret->instructions);
        break;
      }
      case IR_EQ: {
        comparison(CC_E, ir->r1, ir->r2, ir->dst, ret->instructions);
        break;
      }
      case IR_NEQ: {
        comparison(CC_NE, ir->r1, ir->r2, ir->dst, ret->instructions);
        break;
      }
      case IR_DIV: {
        // do Idiv and return ax
        idiv(ir->r1, ir->r2, ret->instructions);
        x64_Operand* dst = to_x64_op(ir->dst);
        push_instr(ret->instructions, mov(reg(REG_AX, 4), dst));
        break;
      }
      case IR_REM: {
        // do Idiv and return dx
        idiv(ir->r1, ir->r2, ret->instructions);
        x64_Operand* dst = to_x64_op(ir->dst);
        push_instr(ret->instructions, mov(reg(REG_DX, 4), dst));
        break;
      }
      case IR_JMP: {
        push_instr(ret->instructions, jmp(ir->label));
        break;
      }
      case IR_JZ: {
        push_instr(ret->instructions,
                   instr2(X64_CMP, &ZERO, to_x64_op(ir->r1)));
        push_instr(ret->instructions, jmpcc(CC_E, ir->label));
        break;
      }
      case IR_JNZ: {
        push_instr(ret->instructions,
                   instr2(X64_CMP, &ZERO, to_x64_op(ir->r1)));
        push_instr(ret->instructions, jmpcc(CC_NE, ir->label));
        break;
      }
      case IR_LABEL: {
        push_instr(ret->instructions, label(ir->label));
        break;
      }
      case IR_COPY: {
        push_instr(ret->instructions,
                   mov(to_x64_op(ir->r1), to_x64_op(ir->dst)));
        break;
      }
      case IR_FN_CALL: {
        int stack_to_dealloc = 0;
        // adjust stack if we have an odd number of arguments.
        // The x64 stack must be 16 byte aligned.
        if (ir->args->len > kNumArgumentRegs && (ir->args->len % 2)) {
          push_instr(ret->instructions, alloc_stack(8));
          stack_to_dealloc += 8;
        }

        // pass first 6 arguments in registers
        for (size_t i = 0; (i < kNumArgumentRegs) && (i < ir->args->len); i++) {
          x64_Operand* arg = to_x64_op(vec_get(ir->args, i));
          x64_Operand* x64_reg = reg(kArgumentRegs[i], 4);
          push_instr(ret->instructions, mov(arg, x64_reg));
        }

        // pass remaining arguments onto the stack in reverse.
        if (ir->args->len > kNumArgumentRegs) {
          for (size_t i = ir->args->len - 1; i >= kNumArgumentRegs; i--) {
            x64_Operand* arg = to_x64_op(vec_get(ir->args, i));
            if (arg->ty == X64_OP_IMM || arg->ty == X64_OP_REG) {
              push_instr(ret->instructions, instr1(X64_PUSH, arg));
            } else {
              x64_Operand* rax = reg(REG_AX, arg->size);
              push_instr(ret->instructions, mov(arg, rax));
              push_instr(ret->instructions, instr1(X64_PUSH, rax));
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
        push_instr(ret->instructions, call);

        // Deallocate stack if necessary.
        if (stack_to_dealloc) {
          x64_Instruction dealloc_stack = {
              .ty = X64_DEALLOC_STACK,
              .stack = stack_to_dealloc,
          };
          push_instr(ret->instructions, dealloc_stack);
        }

        // Move the return value in RAX to the call's destination.
        x64_Operand* dst = to_x64_op(ir->dst);
        push_instr(ret->instructions, mov(reg(REG_AX, 4), dst));
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
  return ret;
}

x64_Program* generate_x86(IrProgram* ast_program) {
  x64_Program* x64_prog = calloc(1, sizeof(x64_Program));
  x64_prog->functions = vec_new(sizeof(x64_Function));
  x64_prog->static_variables = vec_new(sizeof(x64_StaticVariable));
  vec_for_each(ast_program->functions, IrFunction, ir_func) {
    x64_Function* f = fixup_instructions(replace_pseudoregs(
        convert_function(iter.ir_func), ast_program->symbol_table));
    vec_push(x64_prog->functions, f);
  }

  vec_for_each(ast_program->static_variables, IrStaticVariable,
               ir_static_variable) {
    vec_push(x64_prog->static_variables,
             convert_static_variable(iter.ir_static_variable));
  }
  return x64_prog;
}
