#include <assert.h>
#include <stdlib.h>
#include <vcc/errors.h>
#include <vcc/gen_x64.h>

//
// Forward declarations
//
// All expressions return an operand which holds the operand with the final
// value of the expression.
static x64_Operand gen_expr(AstExpr* expr, Vec* out);
static void gen_statement(AstStmt* stmt, Vec* out);

//
// Helpers for constructing instructions/operands.
//
static x64_Instruction mov(x64_Operand src, x64_Operand dst) {
  return (x64_Instruction){
      .ty = X64_MOV,
      .mov =
          {
              .src = src,
              .dst = dst,
          },
  };
}

static inline void push_inst(Vec* vec, x64_Instruction instr) {
  *(x64_Instruction*)vec_push_empty(vec) = instr;
}

static x64_Operand reg(void) { return (x64_Operand){.ty = X64_OP_REG}; }

static x64_Operand imm(int val) {
  return (x64_Operand){.ty = X64_OP_IMM, .imm = val};
}

static x64_Operand gen_expr(AstExpr* expr, Vec* out) {
  switch (expr->ty) {
    case EXPR_CONST: {
      return imm(expr->constant.imm);
    }
    default:
      emit_error_no_pos("Unexpected AstStmt type: %lu", expr->ty);
      assert(false);
  }
}

static void gen_statement(AstStmt* stmt, Vec* out) {
  switch (stmt->ty) {
    case STMT_RETURN: {
      push_inst(out, mov(gen_expr(stmt->ret.expr, out), reg()));
      push_inst(out, (x64_Instruction){.ty = X64_RET});
      break;
    }
    default:
      emit_error_no_pos("Unexpected AstStmt type: %lu", stmt->ty);
      assert(false);
  }
}

static x64_Function* gen_function(AstNode* node) {
  assert(node->ty == NODE_FN);

  x64_Function* fn = calloc(1, sizeof(x64_Function));
  fn->instructions = vec_new(sizeof(x64_Instruction));
  fn->name = node->fn.name;

  gen_statement(node->fn.body->stmt, fn->instructions);
  return fn;
}

x64_Program* generate_x86(AstProgram* ast_program) {
  x64_Program* x64_prog = calloc(1, sizeof(x64_Program));

  x64_prog->function = gen_function(ast_program->main_function);

  return x64_prog;
}