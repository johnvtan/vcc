#include <stdlib.h>
#include <vcc/errors.h>
#include <vcc/ir.h>

//
// Helpers for creating IrVal
//
static IrVal* var(String* name) {
  IrVal* v = calloc(1, sizeof(IrVal));
  v->ty = IR_VAL_VAR;
  v->var = name;
  return v;
}

// Generates a unique temporary IrVal with the name "tmp.n"
// This is guaranteed to be unique because n increments every time temp() is
// called. And C variable names aren't allowed to contain periods.
static IrVal* temp(void) {
  static int n = 0;
  return var(string_format("tmp.%d", n++));
}

static IrVal* constant(int val) {
  IrVal* v = calloc(1, sizeof(IrVal));
  v->ty = IR_VAL_CONST;
  v->constant = val;
  return v;
}

//
// Helpers for creating IrInstruction
//
static inline IrInstruction nullary(IrType ty) {
  return (IrInstruction){
      .ty = ty,
  };
}

static inline IrInstruction unary_no_dst(IrType ty, IrVal* src) {
  return (IrInstruction){
      .ty = ty,
      .r1 = src,
  };
}

static inline IrInstruction unary(IrType ty, IrVal* src, IrVal* dst) {
  return (IrInstruction){
      .ty = ty,
      .dst = dst,
      .r1 = src,
  };
}

static inline IrInstruction binary(IrType ty, IrVal* r1, IrVal* r2,
                                   IrVal* dst) {
  return (IrInstruction){
      .ty = ty,
      .dst = dst,
      .r1 = r1,
      .r2 = r2,
  };
}

//
// Helpers for pushing instructions
//
static inline void push_inst(Vec* out, IrInstruction instr) {
  *(IrInstruction*)vec_push_empty(out) = instr;
}

//
// Functions that walk the AST and generate IR instructions
//
static IrVal* gen_expr(AstExpr* expr, Vec* out);
static IrVal* gen_fact(AstFactor* f, Vec* out) {
  switch (f->ty) {
    case FACT_INT:
      return constant(f->int_const);
    case FACT_UNARY: {
      IrVal* operand = gen_expr(f->unary.expr, out);
      IrType unary_op = IR_UNKNOWN;
      switch (f->unary.op) {
        case UNARY_COMPLEMENT:
          unary_op = IR_UNARY_COMPLEMENT;
          break;
        case UNARY_NEG:
          unary_op = IR_UNARY_NEG;
          break;
        default:
          panic("Unexpected AstStmt type: %lu", f->unary.op);
      }
      IrVal* dst = temp();
      push_inst(out, unary(unary_op, operand, dst));
      return dst;
    }
  }
}
static IrVal* gen_expr(AstExpr* expr, Vec* out) {
  switch (expr->ty) {
    case EXPR_FACT:
      return gen_fact(expr->factor, out);
    case EXPR_BINARY: {
      IrVal* lhs = gen_expr(expr->binary.lhs, out);
      IrVal* rhs = gen_expr(expr->binary.rhs, out);
      IrVal* dst = temp();
      IrType op = IR_UNKNOWN;
      switch (expr->binary.op) {
        case BINARY_ADD:
          op = IR_ADD;
          break;
        case BINARY_SUB:
          op = IR_SUB;
          break;
        case BINARY_DIV:
          op = IR_DIV;
          break;
        case BINARY_MUL:
          op = IR_MUL;
          break;
        case BINARY_REM:
          op = IR_REM;
          break;
        default:
          panic("Unexpected binary op: %u", expr->binary.op);
      }
      push_inst(out, binary(op, lhs, rhs, dst));
      return dst;
    }
    default:
      panic("Unexpected AstStmt type: %lu", expr->ty);
  }
}

static void gen_statement(AstStmt* stmt, Vec* out) {
  switch (stmt->ty) {
    case STMT_RETURN: {
      IrVal* expr = gen_expr(stmt->ret.expr, out);
      push_inst(out, unary_no_dst(IR_RET, expr));
      break;
    }
    default:
      panic("Unexpected AstStmt type: %lu", stmt->ty);
  }
}

static IrFunction* gen_function(AstNode* ast_function) {
  IrFunction* ir_function = calloc(1, sizeof(IrFunction));
  ir_function->instructions = vec_new(sizeof(IrInstruction));
  ir_function->name = ast_function->fn.name;
  gen_statement(ast_function->fn.body->stmt, ir_function->instructions);
  return ir_function;
}

IrProgram* gen_ir(AstProgram* ast_program) {
  IrProgram* ir_program = calloc(1, sizeof(IrProgram));
  ir_program->function = gen_function(ast_program->main_function);
  return ir_program;
}