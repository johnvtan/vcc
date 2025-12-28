#include <assert.h>
#include <vcc/dump.h>

#define X(n) \
  case n:    \
    return #n;

static const char* c_type_to_string(CType type) {
  switch (type) {
    X(TYPE_NONE);
    X(TYPE_INT);
    X(TYPE_UINT);
    X(TYPE_ULONG);
    X(TYPE_DOUBLE);
    X(TYPE_LONG);
  }
}

static const char* ir_type_to_string(IrType type) {
  switch (type) {
    X(IR_UNKNOWN);
    X(IR_RET);

    X(IR_SIGN_EXTEND);
    X(IR_TRUNCATE);
    X(IR_ZERO_EXTEND);
    X(IR_DOUBLE_TO_INT);
    X(IR_DOUBLE_TO_UINT);
    X(IR_INT_TO_DOUBLE);
    X(IR_UINT_TO_DOUBLE);

    X(IR_UNARY_COMPLEMENT);
    X(IR_UNARY_NEG);

    X(IR_ADD);
    X(IR_SUB);
    X(IR_MUL);
    X(IR_DIV);
    X(IR_REM);
    X(IR_EQ);
    X(IR_NEQ);
    X(IR_LT);
    X(IR_LTEQ);
    X(IR_GT);
    X(IR_GTEQ);

    X(IR_COPY);
    X(IR_JMP);
    X(IR_JZ);
    X(IR_JNZ);
    X(IR_LABEL);

    X(IR_FN_CALL);
  }
}

static void dump_numeric(CType type, NumericValue val) {
  printf("%s, val=", c_type_to_string(type));
  switch (type) {
    case TYPE_INT:
      printf("%d", (int)val.int_);
      break;
    case TYPE_UINT:
      printf("%u", (unsigned int)val.int_);
      break;
    case TYPE_LONG:
      printf("%ld", (long)val.int_);
      break;
    case TYPE_ULONG:
      printf("%lu", (unsigned long)val.int_);
      break;
    case TYPE_DOUBLE:
      printf("%.10f, hex=%a", val.double_, val.double_);
      break;
    default:
      assert(false);
  }
}

static void dump_ir_val(SymbolTable* symbol_table, IrVal* val) {
  if (val->ty == IR_VAL_CONST) {
    printf("{ const=");
    dump_numeric(val->constant.c_type, val->constant.numeric);
    printf(" }");
    return;
  }

  assert(val->ty == IR_VAL_VAR);
  SymbolTableEntry* entry = hashmap_get(symbol_table->map, val->var);
  switch (entry->ty) {
    case ST_LOCAL_VAR:
      printf("{ local=%s type=%s }", cstring(val->var),
             c_type_to_string(entry->local.c_type));
      break;
    case ST_STATIC_VAR:
      printf("{ static=%s type=%s global=%u }", cstring(val->var),
             c_type_to_string(entry->static_.c_type), entry->static_.global);
      break;
    case ST_FN:
      printf("{ fn=%s ret_type=%s }", cstring(val->var),
             c_type_to_string(entry->fn.return_type));
      break;
  }
}

static void dump_ir_fn(IrFunction* fn, SymbolTable* symbol_table) {
  printf("fn %s, global=%u\n", cstring(fn->name), fn->global);
  if (fn->params->len) {
    printf("params: ");
    vec_for_each(fn->params, String, param) {
      printf("%s\n", cstring(iter.param));
    }
  } else {
    printf("no params\n");
  }

  printf("{\n");

  vec_for_each(fn->instructions, IrInstruction, instr) {
    printf("\t%s", ir_type_to_string(iter.instr->ty));
    if (iter.instr->r1) {
      printf(" r1=");
      dump_ir_val(symbol_table, iter.instr->r1);
    }
    if (iter.instr->r2) {
      printf(" r2=");
      dump_ir_val(symbol_table, iter.instr->r2);
    }
    if (iter.instr->dst) {
      printf(" dst=");
      dump_ir_val(symbol_table, iter.instr->dst);
    }
    if (iter.instr->label) {
      printf(" label=%s", cstring(iter.instr->label));
    }

    if (iter.instr->args) {
      for (size_t i = 0; i < iter.instr->args->len; i++) {
        printf(" param%lu=", i);
        IrVal* param = vec_get(iter.instr->args, i);
        dump_ir_val(symbol_table, param);
      }
    }
    printf("\n");
  }
  printf("}\n\n");
}

static const char* x64_instr_type_to_string(x64_InstructionType type) {
  switch (type) {
    X(X64_MOV);
    X(X64_MOVSX);
    X(X64_RET);
    X(X64_NEG);
    X(X64_NOT);
    X(X64_ADD);
    X(X64_SUB);
    X(X64_MUL);
    X(X64_DIV);
    X(X64_IDIV);
    X(X64_CDQ);
    X(X64_CMP);
    X(X64_JMP);
    X(X64_JMPCC);
    X(X64_SETCC);
    X(X64_LABEL);
    X(X64_PUSH);
    X(X64_CALL);
    X(X64_CVTTSD2SI);
    X(X64_CVTSI2SD);
    X(X64_DIV_DOUBLE);
    X(X64_SHR);
    X(X64_XOR);
    X(X64_AND);
    X(X64_OR);
  }
}

static const char* asm_type_to_string(x64_Type type) {
  switch (type) {
    X(X64_TY_QUADWORD);
    X(X64_TY_LONGWORD);
    X(X64_TY_DOUBLE);
  }
}

static const char* reg_to_string(x64_RegType type) {
  switch (type) {
    X(REG_AX);
    X(REG_CX);
    X(REG_DX);
    X(REG_DI);
    X(REG_SI);
    X(REG_R8);
    X(REG_R9);
    X(REG_R10);
    X(REG_R11);
    X(REG_SP);
    X(REG_XMM0);
    X(REG_XMM1);
    X(REG_XMM2);
    X(REG_XMM3);
    X(REG_XMM4);
    X(REG_XMM5);
    X(REG_XMM6);
    X(REG_XMM7);
    X(REG_XMM14);
    X(REG_XMM15);
  }
}

static const char* cc_to_string(x64_ConditionCode cc) {
  switch (cc) {
    X(CC_E);
    X(CC_NE);
    X(CC_G);
    X(CC_GE);
    X(CC_L);
    X(CC_LE);
    X(CC_A);
    X(CC_AE);
    X(CC_B);
    X(CC_BE);
  }
}

void dump_operand(x64_Operand* op) {
  switch (op->ty) {
    case X64_OP_IMM: {
      printf("{ IMM val=%lu sign=%u }", op->imm, op->sign);
      break;
    }
    case X64_OP_REG: {
      printf("{ %s }", reg_to_string(op->reg));
      break;
    }
    case X64_OP_STACK: {
      printf("{ STACK pos=%d }", op->stack);
      break;
    }
    case X64_OP_LABEL: {
      printf("{ LABEL %s }", cstring(op->ident));
      break;
    }
    case X64_OP_DATA: {
      printf("{ DATA %s }", cstring(op->ident));
      break;
    }
  }
}

static void dump_x64_fn(x64_Function* fn) {
  printf("fn %s, global=%u, stack_size=%d {\n", cstring(fn->name), fn->global,
         fn->stack_size);
  vec_for_each(fn->instructions, x64_Instruction, inst) {
    printf("\t%s type=%s", x64_instr_type_to_string(iter.inst->ty),
           asm_type_to_string(iter.inst->asm_type));

    if (iter.inst->ty == X64_SETCC || iter.inst->ty == X64_JMPCC) {
      printf(" cc=%s", cc_to_string(iter.inst->cc));
    }
    if (iter.inst->r1) {
      printf(" r1=");
      dump_operand(iter.inst->r1);
    }
    if (iter.inst->r2) {
      printf(" r2=");
      dump_operand(iter.inst->r2);
    }
    printf("\n");
  }
  printf("}\n\n");
}

#undef X

void dump_ir(IrProgram* ir) {
  printf("=====DUMP IR======\n\n");
  if (ir->static_variables->len) {
    printf("Static variables:\n\n");
    vec_for_each(ir->static_variables, IrStaticVariable, static_var) {
      printf("Name: %s, global=%u, init=", cstring(iter.static_var->name),
             iter.static_var->global);
      switch (iter.static_var->init.ty) {
        case INIT_NONE:
          printf("none");
          break;
        case INIT_TENTATIVE:
          printf("tentative");
          break;
        case INIT_HAS_VALUE:
          dump_numeric(iter.static_var->init.c_type,
                       iter.static_var->init.numeric);
          break;
      }
      printf("\n");
    }
    printf("\n");
  }

  printf("Functions:\n\n");
  vec_for_each(ir->functions, IrFunction, fn) {
    dump_ir_fn(iter.fn, ir->symbol_table);
  }
}

void dump_x64(x64_Program* prog) {
  printf("=====DUMP X64=======\n\n");
  if (prog->static_variables->len) {
    printf("Static variables:\n\n");
    vec_for_each(prog->static_variables, x64_StaticVariable, static_var) {
      printf("Name: %s, global=%u, align=%u, init=",
             cstring(iter.static_var->name), iter.static_var->global,
             iter.static_var->alignment);
      switch (iter.static_var->init.ty) {
        case INIT_NONE:
          printf("none");
          break;
        case INIT_TENTATIVE:
          printf("tentative");
          break;
        case INIT_HAS_VALUE:
          dump_numeric(iter.static_var->init.c_type,
                       iter.static_var->init.numeric);
          break;
      }
      printf("\n");
    }
    printf("\n");
  }

  if (prog->static_constants->len) {
    printf("Static constants:\n\n");
    vec_for_each(prog->static_constants, x64_StaticConst, static_const) {
      printf("Name: %s, align=%u, init=", cstring(iter.static_const->name),
             iter.static_const->alignment);
      switch (iter.static_const->init.ty) {
        case INIT_NONE:
          printf("none");
          break;
        case INIT_TENTATIVE:
          printf("tentative");
          break;
        case INIT_HAS_VALUE:
          dump_numeric(iter.static_const->init.c_type,
                       iter.static_const->init.numeric);
          break;
      }
      printf("\n");
    }
    printf("\n");
  }

  vec_for_each(prog->functions, x64_Function, fn) { dump_x64_fn(iter.fn); }
}
