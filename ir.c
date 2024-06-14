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
// IR temps start with a period to ensure they don't conflict with temps created
// during variable resolution in parsing.
static IrVal* temp(void) {
  static int n = 0;
  return var(string_format(".tmp.%d", n++));
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

// Generates a unique label by appending an incrementing count to the label
// name.
static inline IrInstruction label(const char* label) {
  static int n = 0;
  return (IrInstruction){
      .ty = IR_LABEL,
      .label = string_format("%s_%d", label, n++),
  };
}

static inline IrInstruction jmp(String* label) {
  return (IrInstruction){
      .ty = IR_JMP,
      .label = label,
  };
}

static inline IrInstruction jmp_cnd(IrType ty, IrVal* cnd, String* label) {
  return (IrInstruction){
      .ty = ty,
      .r1 = cnd,
      .label = label,
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

static IrVal* gen_binary(AstExpr* expr, Vec* out) {
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
    case BINARY_EQ:
      op = IR_EQ;
      break;
    case BINARY_NEQ:
      op = IR_NEQ;
      break;
    case BINARY_LT:
      op = IR_LT;
      break;
    case BINARY_LTEQ:
      op = IR_LTEQ;
      break;
    case BINARY_GT:
      op = IR_GT;
      break;
    case BINARY_GTEQ:
      op = IR_GTEQ;
      break;

    default:
      panic("Unexpected binary op: %u", expr->binary.op);
  }
  push_inst(out, binary(op, lhs, rhs, dst));
  return dst;
}

static IrVal* gen_expr(AstExpr* expr, Vec* out) {
  switch (expr->ty) {
    case EXPR_BINARY: {
      // AND and OR are special because they have to short circuit.
      if (expr->binary.op == BINARY_AND) {
        IrInstruction false_label = label(".AND_FALSE");
        IrInstruction end_label = label(".AND_END");

        IrVal* result = temp();

        // <instructions for e1
        IrVal* e1 = gen_expr(expr->binary.lhs, out);

        // jz e1, AND_FALSE
        push_inst(out, jmp_cnd(IR_JZ, e1, false_label.label));

        // <instructions for e2>
        IrVal* e2 = gen_expr(expr->binary.rhs, out);

        // jz e2, AND_FALSE
        push_inst(out, jmp_cnd(IR_JZ, e2, false_label.label));

        // result = 1
        push_inst(out, unary(IR_COPY, constant(1), result));

        // jmp AND_END
        push_inst(out, jmp(end_label.label));

        // AND_FALSE:
        push_inst(out, false_label);

        // result = 0
        push_inst(out, unary(IR_COPY, constant(0), result));

        // AND_END
        push_inst(out, end_label);

        return result;
      } else if (expr->binary.op == BINARY_OR) {
        IrInstruction true_label = label(".OR_TRUE");
        IrInstruction end_label = label(".OR_END");

        IrVal* result = temp();

        // <instructions for e1
        IrVal* e1 = gen_expr(expr->binary.lhs, out);

        // jnz e1, OR_TRUE
        push_inst(out, jmp_cnd(IR_JNZ, e1, true_label.label));

        // <instructions for e2>
        IrVal* e2 = gen_expr(expr->binary.rhs, out);

        // jnz e2, OR_TRUE
        push_inst(out, jmp_cnd(IR_JNZ, e2, true_label.label));

        // result = 0
        push_inst(out, unary(IR_COPY, constant(0), result));

        // jmp OR_END
        push_inst(out, jmp(end_label.label));

        // OR_TRUE:
        push_inst(out, true_label);

        // result = 1
        push_inst(out, unary(IR_COPY, constant(1), result));

        // OR_END
        push_inst(out, end_label);

        return result;

      } else {
        return gen_binary(expr, out);
      }
    }
    case EXPR_INT_CONST:
      return constant(expr->int_const);
    case EXPR_UNARY: {
      IrVal* operand = gen_expr(expr->unary.expr, out);
      IrType unary_op = IR_UNKNOWN;
      switch (expr->unary.op) {
        case UNARY_COMPLEMENT:
          unary_op = IR_UNARY_COMPLEMENT;
          break;
        case UNARY_NEG:
          unary_op = IR_UNARY_NEG;
          break;
        case UNARY_NOT:
          unary_op = IR_UNARY_NOT;
          break;
        default:
          panic("Unexpected AstFact type: %lu", expr->unary.op);
      }
      IrVal* dst = temp();
      push_inst(out, unary(unary_op, operand, dst));
      return dst;
    }
    default:
      panic("Unexpected AstStmt type: %lu", expr->ty);
  }
}

static void gen_statement(AstStmt* stmt, Vec* out) {
  switch (stmt->ty) {
    case STMT_RETURN: {
      IrVal* expr = gen_expr(stmt->expr, out);
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
  // gen_statement(ast_function->fn.body->stmt, ir_function->instructions);
  return ir_function;
}

IrProgram* gen_ir(AstProgram* ast_program) {
  IrProgram* ir_program = calloc(1, sizeof(IrProgram));
  ir_program->function = gen_function(ast_program->main_function);
  return ir_program;
}
