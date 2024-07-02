#include <assert.h>
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

static inline IrInstruction label(String* name) {
  return (IrInstruction){
      .ty = IR_LABEL,
      .label = name,
  };
}

// Generates a unique label by appending an incrementing count to the label
// name.
static inline IrInstruction internal_label(const char* name) {
  static int n = 0;
  return label(string_format("%s_%d", name, n++));
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

static inline IrInstruction copy(IrVal* src, IrVal* dst) {
  return unary(IR_COPY, src, dst);
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
static IrVal* gen_unary(AstExpr* expr, Vec* out) {
  IrVal* operand = gen_expr(expr->unary.expr, out);

  // Handle pre/postinc unary functions
  if (expr->unary.op == UNARY_PREINC) {
    push_inst(out, binary(IR_ADD, operand, constant(1), operand));
    return operand;
  }

  if (expr->unary.op == UNARY_PREDEC) {
    push_inst(out, binary(IR_SUB, operand, constant(1), operand));
    return operand;
  }

  if (expr->unary.op == UNARY_POSTINC) {
    IrVal* ret = temp();
    push_inst(out, copy(operand, ret));
    push_inst(out, binary(IR_ADD, operand, constant(1), operand));
    return ret;
  }

  if (expr->unary.op == UNARY_POSTDEC) {
    IrVal* ret = temp();
    push_inst(out, copy(operand, ret));
    push_inst(out, binary(IR_SUB, operand, constant(1), operand));
    return ret;
  }

  // General case for unary --> generate an IR unary
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

static inline bool is_assign(int bin_op) { return bin_op >= BINARY_ASSIGN; }

static IrVal* gen_assign(AstExpr* expr, Vec* out) {
  if (expr->binary.lhs->ty != EXPR_VAR) {
    panic("Expected var LHS but got %u", expr->binary.lhs->ty);
  }

  // lhs is ultimately where the result of the expression goes
  IrVal* lhs = gen_expr(expr->binary.lhs, out);

  // rhs is on the right hand of the assign
  IrVal* rhs = gen_expr(expr->binary.rhs, out);

  // Handle op, which stores the result in lhs
  switch (expr->binary.op) {
    case BINARY_ASSIGN:
      push_inst(out, copy(rhs, lhs));
      break;
    case BINARY_ADD_ASSIGN:
      push_inst(out, binary(IR_ADD, lhs, rhs, lhs));
      break;
    case BINARY_SUB_ASSIGN:
      push_inst(out, binary(IR_SUB, lhs, rhs, lhs));
      break;
    case BINARY_MUL_ASSIGN:
      push_inst(out, binary(IR_MUL, lhs, rhs, lhs));
      break;
    case BINARY_DIV_ASSIGN:
      push_inst(out, binary(IR_DIV, lhs, rhs, lhs));
      break;
    case BINARY_REM_ASSIGN:
      push_inst(out, binary(IR_REM, lhs, rhs, lhs));
      break;
    default:
      panic("Unexpected bin op %u in assign", expr->binary.op);
  }

  return lhs;
}

// The caller generates then/else into separate vectors of IR instructions.
// This function arranges them with the appropriate jumps and puts them in
// |out|. This assumes that |cond| has already been put into |out|.
static void arrange_conditional(IrVal* cond, Vec* then, Vec* else_, Vec* out) {
  IrInstruction else_label = else_ ? internal_label(".COND_ELSE")
                                   : internal_label(".THIS_SHOULDNT_BE_HERE");
  IrInstruction end_label = internal_label(".COND_END");

  push_inst(out,
            jmp_cnd(IR_JZ, cond, else_ ? else_label.label : end_label.label));
  vec_concat(out, then);
  if (else_) {
    push_inst(out, jmp(end_label.label));
    push_inst(out, else_label);
    vec_concat(out, else_);
  }

  push_inst(out, end_label);
}

static IrVal* gen_expr(AstExpr* expr, Vec* out) {
  switch (expr->ty) {
    case EXPR_TERNARY: {
      IrVal* cond = gen_expr(expr->ternary.cond, out);
      IrVal* ternary_result = temp();

      // Generate then/else into separate vectors, which get arranged
      // later in call to arrange_conditional.
      Vec* then_ir = vec_new(sizeof(IrInstruction));
      IrVal* then_result = gen_expr(expr->ternary.then, then_ir);
      push_inst(then_ir, copy(then_result, ternary_result));

      Vec* else_ir = vec_new(sizeof(IrInstruction));
      IrVal* else_result = gen_expr(expr->ternary.else_, else_ir);
      push_inst(else_ir, copy(else_result, ternary_result));

      arrange_conditional(cond, then_ir, else_ir, out);

      return ternary_result;
    }
    case EXPR_BINARY: {
      // AND and OR are special because they have to short circuit.
      if (expr->binary.op == BINARY_AND) {
        IrInstruction false_label = internal_label(".AND_FALSE");
        IrInstruction end_label = internal_label(".AND_END");

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
        push_inst(out, copy(constant(1), result));

        // jmp AND_END
        push_inst(out, jmp(end_label.label));

        // AND_FALSE:
        push_inst(out, false_label);

        // result = 0
        push_inst(out, copy(constant(0), result));

        // AND_END
        push_inst(out, end_label);

        return result;
      } else if (expr->binary.op == BINARY_OR) {
        IrInstruction true_label = internal_label(".OR_TRUE");
        IrInstruction end_label = internal_label(".OR_END");

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
        push_inst(out, copy(constant(0), result));

        // jmp OR_END
        push_inst(out, jmp(end_label.label));

        // OR_TRUE:
        push_inst(out, true_label);

        // result = 1
        push_inst(out, copy(constant(1), result));

        // OR_END
        push_inst(out, end_label);

        return result;
      } else if (is_assign(expr->binary.op)) {
        return gen_assign(expr, out);
      } else {
        return gen_binary(expr, out);
      }
    }
    case EXPR_INT_CONST:
      return constant(expr->int_const);
    case EXPR_UNARY:
      return gen_unary(expr, out);
    case EXPR_VAR:
      return var(expr->ident);
    default:
      panic("Unexpected AstStmt type: %lu", expr->ty);
  }
}

static void gen_statement(AstStmt* stmt, Vec* out) {
  switch (stmt->ty) {
    case STMT_RETURN: {
      IrVal* expr = gen_expr(stmt->expr, out);
      push_inst(out, unary_no_dst(IR_RET, expr));
      return;
    }
    case STMT_EXPR:
      gen_expr(stmt->expr, out);
      return;
    case STMT_NULL:
      return;
    case STMT_GOTO:
      push_inst(out, jmp(stmt->ident));
      return;
    case STMT_LABELED: {
      push_inst(out, label(stmt->labeled.label));
      gen_statement(stmt->labeled.stmt, out);
      return;
    }
    case STMT_IF: {
      IrVal* cond = gen_expr(stmt->if_.cond, out);

      Vec* then_ir = vec_new(sizeof(IrInstruction));
      gen_statement(stmt->if_.then, then_ir);

      Vec* else_ir = NULL;
      if (stmt->if_.else_) {
        else_ir = vec_new(sizeof(IrInstruction));
        gen_statement(stmt->if_.else_, else_ir);
      }

      arrange_conditional(cond, then_ir, else_ir, out);
      return;
    }
    default:
      panic("Unexpected AstStmt type: %lu", stmt->ty);
  }
}

static void gen_decl(AstDecl* decl, Vec* out) {
  if (!decl->init) {
    return;
  }

  if (decl->init->ty != EXPR_BINARY && decl->init->binary.op != BINARY_ASSIGN) {
    panic("Invalid init decl expr ty %u", decl->init->ty);
  }

  gen_assign(decl->init, out);
}

static void gen_block_item(AstBlockItem* block_item, Vec* out) {
  if (block_item->ty == BLOCK_DECL) {
    gen_decl(block_item->decl, out);
  } else {
    gen_statement(block_item->stmt, out);
  }
}

static IrFunction* gen_function(AstNode* ast_function) {
  IrFunction* ir_function = calloc(1, sizeof(IrFunction));
  ir_function->instructions = vec_new(sizeof(IrInstruction));
  ir_function->name = ast_function->fn.name;

  vec_for_each(ast_function->fn.body, AstBlockItem, block_item) {
    gen_block_item(iter.block_item, ir_function->instructions);
  }

  // Always return 0 from every function
  push_inst(ir_function->instructions, unary_no_dst(IR_RET, constant(0)));
  return ir_function;
}

IrProgram* gen_ir(AstProgram* ast_program) {
  IrProgram* ir_program = calloc(1, sizeof(IrProgram));
  ir_program->function = gen_function(ast_program->main_function);
  return ir_program;
}
