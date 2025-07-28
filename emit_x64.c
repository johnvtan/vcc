#include <assert.h>
#include <stdarg.h>
#include <vcc/emit_x64.h>
#include <vcc/errors.h>
#include <vcc/string.h>

//
// Platform specific defines.
//
#if __APPLE__
#define ASM_SYMBOL_PREFIX "_"
#define LOCAL_LABEL_PREFIX "L"
#elif __linux__
#define ASM_SYMBOL_PREFIX ""
#define LOCAL_LABEL_PREFIX ".L"
#else
#error "Only MacOS and linux are supported"
#endif

//
// Context for emitting code.
//
typedef struct {
  FILE* fp;
} Context;

static void emit(Context* cx, const char* fmt, ...) {
  va_list args;
  va_start(args, fmt);
  vfprintf(cx->fp, fmt, args);
  va_end(args);
}

static void emit_operand(Context* cx, const x64_Operand* op) {
  switch (op->ty) {
    case X64_OP_IMM: {
      if (op->sign) {
        emit(cx, "$%ld", op->imm);
      } else {
        emit(cx, "$%lu", op->imm);
      }
      // switch (op->size) {
      //   case QUADWORD:
      //     emit(cx, "$%ld", (long)op->imm);
      //     break;
      //   case LONGWORD:
      //     emit(cx, "$%d", (int)op->imm);
      //     break;
      //   default:
      //     assert(false);
      // }
      break;
    }
    case X64_OP_REG: {
      const char* reg_str = NULL;
      if (op->size == QUADWORD) {
        static const char* reg_map[] = {
            [REG_AX] = "rax", [REG_DX] = "rdx",  [REG_DI] = "rdi",
            [REG_CX] = "rcx", [REG_SI] = "rsi",  [REG_R8] = "r8",
            [REG_R9] = "r9",  [REG_R10] = "r10", [REG_R11] = "r11",
            [REG_SP] = "rsp",
        };
        reg_str = reg_map[op->reg];
      } else if (op->size == LONGWORD) {
        static const char* reg_map[] = {
            [REG_AX] = "eax", [REG_DX] = "edx",   [REG_DI] = "edi",
            [REG_CX] = "ecx", [REG_SI] = "esi",   [REG_R8] = "r8d",
            [REG_R9] = "r9d", [REG_R10] = "r10d", [REG_R11] = "r11d",
            [REG_SP] = "rsp",
        };
        reg_str = reg_map[op->reg];
      } else {
        panic("Unexpected reg op size %u", op->size);
      }
      emit(cx, "%%%s", reg_str);
      break;
    }
    case X64_OP_STACK: {
      emit(cx, "%d(%%rbp)", op->stack);
      break;
    }
    case X64_OP_LABEL: {
      emit(cx, LOCAL_LABEL_PREFIX "%s", cstring(op->ident));
      break;
    }
    case X64_OP_DATA: {
      emit(cx, ASM_SYMBOL_PREFIX "%s(%%rip)", cstring(op->ident));
      break;
    }
    default:
      panic("Unrecognized x64 operand %lu", op->ty);
  }
}

static void emit2(Context* cx, const char* inst, const x64_Operand* src,
                  const x64_Operand* dst, const x64_Size size) {
  emit(cx, "\t%s%c ", inst, size);
  emit_operand(cx, src);
  emit(cx, ", ");
  emit_operand(cx, dst);
  emit(cx, "\n");
}

static void emit1(Context* cx, const char* inst, const x64_Operand* arg,
                  const x64_Size size) {
  emit(cx, "\t%s%c ", inst, size);
  emit_operand(cx, arg);
  emit(cx, "\n");
}

static void emit_jump(Context* cx, const char* inst, const x64_Operand* arg) {
  emit(cx, "\t%s ", inst);
  emit_operand(cx, arg);
  emit(cx, "\n");
}

static void emit_label(Context* cx, const String* label) {
  emit(cx, LOCAL_LABEL_PREFIX "%s:\n", cstring(label));
}

static void emit_function_label(Context* cx, const String* label, bool global) {
  if (global) {
    emit(cx, "\t.globl " ASM_SYMBOL_PREFIX "%s\n", cstring(label));
  }
  emit(cx, "\t.text\n");
  emit(cx, ASM_SYMBOL_PREFIX "%s:\n", cstring(label));
}

//
// Helpers for formatting instructions
//
static String* format_cc(const char* prefix, x64_ConditionCode cc) {
  static const char* cc_to_str[] = {
      [CC_E] = "e", [CC_NE] = "ne", [CC_L] = "l", [CC_LE] = "le",
      [CC_G] = "g", [CC_GE] = "ge", [CC_A] = "a", [CC_AE] = "ae",
      [CC_B] = "b", [CC_BE] = "be",
  };

  return string_format("%s%s", prefix, cc_to_str[cc]);
}

static void emit_inst(Context* cx, x64_Instruction* inst) {
  switch (inst->ty) {
    case X64_RET: {
      // Function epilogue
      emit(cx, "\tmovq %%rbp, %%rsp\n");
      emit(cx, "\tpopq %%rbp\n");
      emit(cx, "\tret\n");
      break;
    }
    case X64_MOV: {
      emit2(cx, "mov", inst->r1, inst->r2, inst->size);
      break;
    }
    case X64_NEG: {
      emit1(cx, "neg", inst->r1, inst->size);
      break;
    }
    case X64_NOT: {
      emit1(cx, "not", inst->r1, inst->size);
      break;
    }
    case X64_ADD: {
      emit2(cx, "add", inst->r1, inst->r2, inst->size);
      break;
    }
    case X64_SUB: {
      emit2(cx, "sub", inst->r1, inst->r2, inst->size);
      break;
    }
    case X64_MUL: {
      emit2(cx, "imul", inst->r1, inst->r2, inst->size);
      break;
    }
    case X64_CMP: {
      emit2(cx, "cmp", inst->r1, inst->r2, inst->size);
      break;
    }
    case X64_IDIV: {
      emit1(cx, "idiv", inst->r1, inst->size);
      break;
    }
    case X64_DIV: {
      emit1(cx, "div", inst->r1, inst->size);
      break;
    }
    case X64_CDQ: {
      if (inst->size == QUADWORD) {
        emit(cx, "\tcqo\n");
      } else {
        emit(cx, "\tcdq\n");
      }
      break;
    }
    case X64_JMP: {
      emit_jump(cx, "jmp", inst->r1);
      break;
    }
    case X64_JMPCC: {
      emit_jump(cx, cstring(format_cc("j", inst->cc)), inst->r1);
      break;
    }
    case X64_SETCC: {
      emit_jump(cx, cstring(format_cc("set", inst->cc)), inst->r1);
      break;
    }
    case X64_LABEL: {
      if (inst->r1->ty != X64_OP_LABEL) {
        panic("Expected label operand but got %u", inst->r1->ty);
      }
      emit_label(cx, inst->r1->ident);
      break;
    }
    case X64_CALL: {
      if (inst->r1->ty != X64_OP_LABEL) {
        panic("Expected label operand but got %u", inst->r1->ty);
      }
      emit(cx, "\tcall " ASM_SYMBOL_PREFIX "%s\n", cstring(inst->r1->ident));
      break;
    }
    case X64_PUSH: {
      // TODO(johntan): cleanup? Just hardcoding QUADWORD rn.
      inst->r1->size = QUADWORD;
      emit1(cx, "push", inst->r1, QUADWORD);
      break;
    }
    case X64_MOVSX: {
      assert(inst->r1->size);
      assert(inst->r2->size);

      // TODO(johntan): refactor
      emit(cx, "\tmovslq ");
      emit_operand(cx, inst->r1);
      emit(cx, ", ");
      emit_operand(cx, inst->r2);
      emit(cx, "\n");
      break;
    }
    default:
      emit_error_no_pos("Unrecognized x64 instruction %lu", inst->ty);
      assert(false);
  }
}

static void emit_function(Context* cx, x64_Function* fn) {
  // Function prologue
  emit(cx, "\n");
  emit_function_label(cx, fn->name, fn->global);
  emit(cx, "\tpushq %%rbp\n");
  emit(cx, "\tmovq %%rsp, %%rbp\n");
  vec_for_each(fn->instructions, x64_Instruction, instr) {
    emit_inst(cx, iter.instr);
  }
}

static void emit_static_variable(Context* cx, x64_StaticVariable* sv) {
  if (sv->global) {
    emit(cx, "\t.globl " ASM_SYMBOL_PREFIX "%s\n", cstring(sv->name));
  }

  if (sv->init.storage_ == 0) {
    emit(cx, ".bss\n");
    emit(cx, "\t.balign %d\n", sv->alignment);
    emit(cx, ASM_SYMBOL_PREFIX "%s:\n", cstring(sv->name));
    emit(cx, "\t.zero %d\n", sv->alignment);
    return;
  }

  emit(cx, ".data\n");
  emit(cx, "\t.balign %d\n", sv->alignment);
  emit(cx, ASM_SYMBOL_PREFIX "%s:\n", cstring(sv->name));
  switch (sv->init.c_type) {
    case TYPE_INT:
      emit(cx, "\t.long %d\n", (int)sv->init.storage_);
      break;
    case TYPE_LONG:
      emit(cx, "\t.quad %ld\n", (long)sv->init.storage_);
      break;
    case TYPE_UINT:
      emit(cx, "\t.long %u\n", (unsigned int)sv->init.storage_);
      break;
    case TYPE_ULONG:
      emit(cx, "\t.quad %lu\n", (unsigned long)sv->init.storage_);
      break;
    default:
      assert(false);
  }
}

int emit_x64(x64_Program* program, const char* outfile) {
  FILE* fp = fopen(outfile, "w+");
  assert(fp);
  Context cx = {.fp = fp};

  vec_for_each(program->functions, x64_Function, fn) {
    emit_function(&cx, iter.fn);
  }

  vec_for_each(program->static_variables, x64_StaticVariable, static_variable) {
    emit_static_variable(&cx, iter.static_variable);
  }

#if __linux__
  emit(&cx, "\t.section .note.GNU-stack,\"\",@progbits\n");
#endif
  return 0;
}
