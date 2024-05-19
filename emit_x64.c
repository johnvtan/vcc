#include <assert.h>
#include <stdarg.h>
#include <vcc/emit_x64.h>
#include <vcc/errors.h>
#include <vcc/string.h>

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
      emit(cx, "$%d", op->imm);
      break;
    }
    case X64_OP_REG: {
      static const char* reg_map[] = {
          [REG_AX] = "eax",
          [REG_R10] = "r10d",
      };

      emit(cx, "%%%s", reg_map[op->reg]);
      break;
    }
    case X64_OP_STACK: {
      emit(cx, "%d(%%rbp)", op->stack);
      break;
    }
    default:
      panic("Unrecognized x64 operand %lu", op->ty);
  }
}

static void emit2(Context* cx, const char* inst, const x64_Operand* src,
                  const x64_Operand* dst) {
  emit(cx, "\t%s ", inst);
  emit_operand(cx, src);
  emit(cx, ", ");
  emit_operand(cx, dst);
  emit(cx, "\n");
}

static void emit1(Context* cx, const char* inst, const x64_Operand* arg) {
  emit(cx, "\t%s ", inst);
  emit_operand(cx, arg);
  emit(cx, "\n");
}

static void emit0(Context* cx, const char* inst) { emit(cx, "\t%s\n", inst); }

static void emit_inst(Context* cx, x64_Instruction* inst) {
  switch (inst->ty) {
    case X64_RET: {
      // Function epilogue
      emit(cx, "\tmovq %%rbp, %%rsp\n");
      emit(cx, "\tpopq %%rbp\n");
      emit0(cx, "ret");
      break;
    }
    case X64_MOV: {
      emit2(cx, "movl", inst->r1, inst->r2);
      break;
    }
    case X64_NEG: {
      emit1(cx, "negl", inst->r1);
      break;
    }
    case X64_NOT: {
      emit1(cx, "notl", inst->r1);
      break;
    }
    case X64_ALLOC_STACK: {
      emit(cx, "\tsubq $%d, %%rsp\n", inst->stack);
      break;
    }
    default:
      emit_error_no_pos("Unrecognized x64 instruction %lu", inst->ty);
      assert(false);
  }
}

static void emit_label(Context* cx, const String* label, bool global) {
  if (global) {
    emit(cx, "\t.globl %s\n", cstring(label));
  }
  emit(cx, "%s:\n", cstring(label));
}

static void emit_function(Context* cx, x64_Function* fn) {
  // Function prologue
  emit_label(cx, fn->name, true);
  emit(cx, "\tpushq %%rbp\n");
  emit(cx, "\tmovq %%rsp, %%rbp\n");
  vec_for_each(fn->instructions, x64_Instruction, instr) {
    emit_inst(cx, iter.instr);
  }
}

int emit_x64(x64_Program* program, const char* outfile) {
  FILE* fp = fopen(outfile, "w+");
  assert(fp);
  Context cx = {.fp = fp};
  emit_function(&cx, program->function);
  emit(&cx, "\t.section .note.GNU-stack,\"\",@progbits\n");
  return 0;
}