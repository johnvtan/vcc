#include <assert.h>
#include <stdlib.h>
#include <string.h>  // for memset
#include <vcc/errors.h>
#include <vcc/ir.h>

typedef struct {
  SymbolTable* symbol_table;
  Vec* out;
} Context;

static void gen_block_item(Context* cx, AstBlockItem* block_item);
static void gen_decl(Context* cx, AstDecl* decl);

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
// This is guaranteed to be unique because n increments every time temp(cx) is
// called. And C variable names aren't allowed to contain periods.
// IR temps start with a period to ensure they don't conflict with temps created
// during variable resolution in parsing.
//
// This will also add the temporary variable to the symbol table.
static IrVal* temp(Context* cx, CType c_type) {
  static int n = 0;
  String* name = string_format(".tmp.%d", n++);

  SymbolTableEntry* st_entry = calloc(1, sizeof(SymbolTableEntry));
  st_entry->ty = ST_LOCAL_VAR;
  st_entry->local.c_type = c_type;
  hashmap_put(cx->symbol_table->map, name, st_entry);

  // TODO: necessary?
  vec_push(cx->symbol_table->symbols, name);

  return var(name);
}

IrVal* constant(CompTimeConst c) {
  IrVal* v = calloc(1, sizeof(IrVal));
  v->ty = IR_VAL_CONST;
  v->constant = c;
  return v;
}

//
// Helpers for creating IrInstruction
//
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
  return label(string_format(".IR_%s_%d", name, n++));
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
static IrVal* gen_expr(Context* cx, AstExpr* expr);

static CompTimeConst one(CType c_type) {
  CompTimeConst ret;
  ret.c_type = c_type;
  ret.storage_ = 1;
  return ret;
}

CompTimeConst zero(CType c_type) {
  CompTimeConst ret;
  ret.c_type = c_type;
  ret.storage_ = 0;
  return ret;
}

static IrVal* gen_unary(Context* cx, AstExpr* expr) {
  IrVal* operand = gen_expr(cx, expr->unary.expr);

  // Handle pre/postinc unary functions
  if (expr->unary.op == UNARY_PREINC) {
    push_inst(cx->out,
              binary(IR_ADD, operand, constant(one(expr->c_type)), operand));
    return operand;
  }

  if (expr->unary.op == UNARY_PREDEC) {
    push_inst(cx->out,
              binary(IR_SUB, operand, constant(one(expr->c_type)), operand));
    return operand;
  }

  if (expr->unary.op == UNARY_POSTINC) {
    IrVal* ret = temp(cx, expr->c_type);
    push_inst(cx->out, copy(operand, ret));
    push_inst(cx->out,
              binary(IR_ADD, operand, constant(one(expr->c_type)), operand));
    return ret;
  }

  if (expr->unary.op == UNARY_POSTDEC) {
    IrVal* ret = temp(cx, expr->c_type);
    push_inst(cx->out, copy(operand, ret));
    push_inst(cx->out,
              binary(IR_SUB, operand, constant(one(expr->c_type)), operand));
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
  IrVal* dst = temp(cx, expr->c_type);
  push_inst(cx->out, unary(unary_op, operand, dst));
  return dst;
}

static IrVal* gen_binary(Context* cx, AstExpr* expr) {
  IrVal* lhs = gen_expr(cx, expr->binary.lhs);
  IrVal* rhs = gen_expr(cx, expr->binary.rhs);
  IrVal* dst = temp(cx, expr->c_type);
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
  push_inst(cx->out, binary(op, lhs, rhs, dst));
  return dst;
}

static IrVal* ir_cast(Context* cx, IrVal* val, CType from, CType to) {
  if (from == to) {
    return val;
  }

  IrVal* dst = temp(cx, to);
  if (to == TYPE_LONG) {
    push_inst(cx->out, unary(IR_SIGN_EXTEND, val, dst));
  } else {
    push_inst(cx->out, unary(IR_TRUNCATE, val, dst));
  }

  return dst;
}

static inline bool is_assign(int bin_op) { return bin_op >= BINARY_ASSIGN; }
static IrVal* gen_assign(Context* cx, AstExpr* expr) {
  if (expr->binary.lhs->ty != EXPR_VAR) {
    panic("Expected var LHS but got %u", expr->binary.lhs->ty);
  }

  if (expr->binary.op == BINARY_ASSIGN) {
    // Handle simple assignment.
    IrVal* lhs = gen_expr(cx, expr->binary.lhs);
    IrVal* rhs = gen_expr(cx, expr->binary.rhs);
    push_inst(cx->out, copy(rhs, lhs));
    return lhs;
  }

  // Compound assignment is a little more complicated.
  // If there's a cast in the rhs of a compound assign, we need to
  // do the binary operation into a temp of the common type before
  // moving the result into the lhs (with a cast or sign extend).

  IrType ir_ty;
  switch (expr->binary.op) {
    case BINARY_ADD_ASSIGN:
      ir_ty = IR_ADD;
      break;
    case BINARY_SUB_ASSIGN:
      ir_ty = IR_SUB;
      break;
    case BINARY_MUL_ASSIGN:
      ir_ty = IR_MUL;
      break;
    case BINARY_DIV_ASSIGN:
      ir_ty = IR_DIV;
      break;
    case BINARY_REM_ASSIGN:
      ir_ty = IR_REM;
      break;
    default:
      panic("Unexpected bin op %u in assign", expr->binary.op);
  }

  // lhs is ultimately where the result of the expression goes
  IrVal* lhs = gen_expr(cx, expr->binary.lhs);
  IrVal* rhs = gen_expr(cx, expr->binary.rhs);

  CType lhs_type = expr->binary.lhs->c_type;
  CType rhs_type = expr->binary.rhs->c_type;

  if (lhs_type != rhs_type) {
    CType common_type = get_common_type(lhs_type, rhs_type);

    IrVal* intermediate_dst = temp(cx, common_type);
    IrVal* intermediate_lhs = ir_cast(cx, lhs, lhs_type, common_type);
    IrVal* intermediate_rhs = ir_cast(cx, rhs, rhs_type, common_type);
    push_inst(cx->out, binary(ir_ty, intermediate_lhs, intermediate_rhs,
                              intermediate_dst));

    // Convert intermediate_dst back to lhs's original type.
    // Note: I think we could cast directly into lhs here.
    IrVal* intermediate_dst_casted =
        ir_cast(cx, intermediate_dst, common_type, lhs_type);
    push_inst(cx->out, copy(intermediate_dst_casted, lhs));
  } else {
    push_inst(cx->out, binary(ir_ty, lhs, rhs, lhs));
  }

  return lhs;
}

// The caller generates then/else into separate vectors of IR instructions.
// This function arranges them with the appropriate jumps and puts them in
// |out|. This assumes that |cond| has already been put into |out|.
static void arrange_conditional(Context* cx, IrVal* cond, Vec* then,
                                Vec* else_) {
  IrInstruction else_label = else_ ? internal_label(".COND_ELSE")
                                   : internal_label(".THIS_SHOULDNT_BE_HERE");
  IrInstruction end_label = internal_label(".COND_END");

  push_inst(cx->out,
            jmp_cnd(IR_JZ, cond, else_ ? else_label.label : end_label.label));
  vec_concat(cx->out, then);
  if (else_) {
    push_inst(cx->out, jmp(end_label.label));
    push_inst(cx->out, else_label);
    vec_concat(cx->out, else_);
  }

  push_inst(cx->out, end_label);
}

static IrVal* gen_expr(Context* cx, AstExpr* expr) {
  switch (expr->ty) {
    case EXPR_TERNARY: {
      IrVal* cond = gen_expr(cx, expr->ternary.cond);
      IrVal* ternary_result = temp(cx, expr->c_type);

      // Generate then/else into separate vectors, which get arranged
      // later in call to arrange_conditional.
      Vec* then_ir = vec_new(sizeof(IrInstruction));
      {
        Context cx2 = {
            .symbol_table = cx->symbol_table,
            .out = then_ir,
        };
        IrVal* then_result = gen_expr(&cx2, expr->ternary.then);
        push_inst(then_ir, copy(then_result, ternary_result));
      }

      Vec* else_ir = vec_new(sizeof(IrInstruction));
      {
        Context cx2 = {
            .symbol_table = cx->symbol_table,
            .out = else_ir,
        };
        IrVal* else_result = gen_expr(&cx2, expr->ternary.else_);
        push_inst(else_ir, copy(else_result, ternary_result));
      }

      arrange_conditional(cx, cond, then_ir, else_ir);

      return ternary_result;
    }
    case EXPR_BINARY: {
      // AND and OR are special because they have to short circuit.
      if (expr->binary.op == BINARY_AND) {
        IrInstruction false_label = internal_label(".AND_FALSE");
        IrInstruction end_label = internal_label(".AND_END");

        IrVal* result = temp(cx, expr->c_type);

        // <instructions for e1
        IrVal* e1 = gen_expr(cx, expr->binary.lhs);

        // jz e1, AND_FALSE
        push_inst(cx->out, jmp_cnd(IR_JZ, e1, false_label.label));

        // <instructions for e2>
        IrVal* e2 = gen_expr(cx, expr->binary.rhs);

        // jz e2, AND_FALSE
        push_inst(cx->out, jmp_cnd(IR_JZ, e2, false_label.label));

        // result = 1
        push_inst(cx->out, copy(constant(one(expr->c_type)), result));

        // jmp AND_END
        push_inst(cx->out, jmp(end_label.label));

        // AND_FALSE:
        push_inst(cx->out, false_label);

        // result = 0
        push_inst(cx->out, copy(constant(zero(expr->c_type)), result));

        // AND_END
        push_inst(cx->out, end_label);

        return result;
      } else if (expr->binary.op == BINARY_OR) {
        IrInstruction true_label = internal_label(".OR_TRUE");
        IrInstruction end_label = internal_label(".OR_END");

        IrVal* result = temp(cx, expr->c_type);

        // <instructions for e1
        IrVal* e1 = gen_expr(cx, expr->binary.lhs);

        // jnz e1, OR_TRUE
        push_inst(cx->out, jmp_cnd(IR_JNZ, e1, true_label.label));

        // <instructions for e2>
        IrVal* e2 = gen_expr(cx, expr->binary.rhs);

        // jnz e2, OR_TRUE
        push_inst(cx->out, jmp_cnd(IR_JNZ, e2, true_label.label));

        // result = 0
        push_inst(cx->out, copy(constant(zero(expr->c_type)), result));

        // jmp OR_END
        push_inst(cx->out, jmp(end_label.label));

        // OR_TRUE:
        push_inst(cx->out, true_label);

        // result = 1
        push_inst(cx->out, copy(constant(one(expr->c_type)), result));

        // OR_END
        push_inst(cx->out, end_label);

        return result;
      } else if (is_assign(expr->binary.op)) {
        return gen_assign(cx, expr);
      } else {
        return gen_binary(cx, expr);
      }
    }
    case EXPR_CONST:
      return constant(expr->const_);
    case EXPR_UNARY:
      return gen_unary(cx, expr);
    case EXPR_VAR:
      return var(expr->ident);
    case EXPR_FN_CALL: {
      // Generate instructions to evaluate each argument.
      Vec* ir_args = vec_new(sizeof(IrVal));
      vec_for_each(expr->fn_call.args, AstExpr, arg) {
        IrVal* ir_arg = gen_expr(cx, iter.arg);
        vec_push(ir_args, ir_arg);
      }

      IrVal* dst = temp(cx, expr->c_type);
      IrInstruction ir_fn_call = {
          .ty = IR_FN_CALL,
          .dst = dst,
          .label = expr->fn_call.ident,
          .args = ir_args,
      };

      push_inst(cx->out, ir_fn_call);
      return dst;
    }
    case EXPR_CAST: {
      IrVal* inner = gen_expr(cx, expr->cast.expr);
      return ir_cast(cx, inner, expr->cast.expr->c_type,
                     expr->cast.target_type);
    }
    default:
      panic("Unexpected AstExpr type: %lu", expr->ty);
  }
}

static void gen_statement(Context* cx, AstStmt* stmt) {
  switch (stmt->ty) {
    case STMT_RETURN: {
      IrVal* expr = gen_expr(cx, stmt->expr);
      push_inst(cx->out, unary_no_dst(IR_RET, expr));
      return;
    }
    case STMT_EXPR:
      gen_expr(cx, stmt->expr);
      return;
    case STMT_NULL:
      return;
    case STMT_GOTO:
      push_inst(cx->out, jmp(stmt->ident));
      return;
    case STMT_LABELED: {
      push_inst(cx->out, label(stmt->labeled.label));
      gen_statement(cx, stmt->labeled.stmt);
      return;
    }
    case STMT_COMPOUND: {
      vec_for_each(stmt->block, AstBlockItem, block_item) {
        gen_block_item(cx, iter.block_item);
      }
      return;
    }
    case STMT_IF: {
      IrVal* cond = gen_expr(cx, stmt->if_.cond);

      Vec* then_ir = vec_new(sizeof(IrInstruction));
      {
        Context cx2 = {
            .symbol_table = cx->symbol_table,
            .out = then_ir,
        };
        gen_statement(&cx2, stmt->if_.then);
      }

      Vec* else_ir = NULL;
      if (stmt->if_.else_) {
        else_ir = vec_new(sizeof(IrInstruction));
        Context cx2 = {
            .symbol_table = cx->symbol_table,
            .out = else_ir,
        };
        gen_statement(&cx2, stmt->if_.else_);
      }

      arrange_conditional(cx, cond, then_ir, else_ir);
      return;
    }
    case STMT_WHILE: {
      // .CONTINUE_LABEL:
      // tmp = <instructions for cond>
      // jz tmp, .BREAK_LABEL
      // <instructions for body>
      // jmp .CONTINUE_LABEL
      // .BREAK_LABEL:
      push_inst(cx->out, label(stmt->while_.continue_label));
      IrVal* cond = gen_expr(cx, stmt->while_.cond);
      push_inst(cx->out, jmp_cnd(IR_JZ, cond, stmt->while_.break_label));
      gen_statement(cx, stmt->while_.body);
      push_inst(cx->out, jmp(stmt->while_.continue_label));
      push_inst(cx->out, label(stmt->while_.break_label));
      return;
    }
    case STMT_DOWHILE: {
      // .DOWHILE.START:
      // <instructions for body>
      // .CONTINUE_LABEL:
      // tmp = <instructions for cond>
      // jnz tmp, .DOWHILE.START
      // .BREAK_LABEL:
      IrInstruction start = internal_label(".DOWHILE.START");
      push_inst(cx->out, start);

      gen_statement(cx, stmt->while_.body);
      push_inst(cx->out, label(stmt->while_.continue_label));
      IrVal* cond = gen_expr(cx, stmt->while_.cond);
      push_inst(cx->out, jmp_cnd(IR_JNZ, cond, start.label));
      push_inst(cx->out, label(stmt->while_.break_label));
      return;
    }
    case STMT_FOR: {
      // <instructions for init>
      // .FOR.START:
      // tmp = <instructions for cond>
      // jz tmp, .BREAK_LABEL
      // <instructions for body>
      // .CONTINUE_LABEL:
      // <instructions for post>
      // jmp .FOR.START
      // .BREAK_LABEL:

      // This is a union; just checking that an init exists.
      if (stmt->for_.init.ty != FOR_INIT_NONE) {
        if (stmt->for_.init.ty == FOR_INIT_DECL) {
          gen_decl(cx, stmt->for_.init.decl);
        } else {
          gen_expr(cx, stmt->for_.init.expr);
        }
      }

      IrInstruction start = internal_label(".FOR.START");
      push_inst(cx->out, start);

      if (stmt->for_.cond) {
        IrVal* cond = gen_expr(cx, stmt->for_.cond);
        push_inst(cx->out, jmp_cnd(IR_JZ, cond, stmt->for_.break_label));
      }

      gen_statement(cx, stmt->for_.body);
      push_inst(cx->out, label(stmt->for_.continue_label));
      if (stmt->for_.post) {
        gen_expr(cx, stmt->for_.post);
      }
      push_inst(cx->out, jmp(start.label));
      push_inst(cx->out, label(stmt->for_.break_label));
      return;
    }
    case STMT_SWITCH: {
      IrVal* cond = gen_expr(cx, stmt->switch_.cond);
      IrVal* cmp_result = temp(cx, stmt->switch_.cond->c_type);

      AstCaseJump* default_case = NULL;
      vec_for_each(stmt->switch_.case_jumps, AstCaseJump, case_jump) {
        if (iter.case_jump->is_default) {
          default_case = iter.case_jump;
          continue;
        }
        // if stmt->switch_.cond == iter.case_jump->const_expr:
        //   jmp iter.case_jump->label.
        push_inst(cx->out,
                  binary(IR_EQ, cond, constant(iter.case_jump->const_expr),
                         cmp_result));
        push_inst(cx->out, jmp_cnd(IR_JNZ, cmp_result, iter.case_jump->label));
      }

      if (default_case) {
        // no condition for default: jump to default
        // jmp default_case->label
        push_inst(cx->out, jmp(default_case->label));
      } else {
        // No default case -- just skip the body
        push_inst(cx->out, jmp(stmt->switch_.break_label));
      }

      gen_statement(cx, stmt->switch_.body);
      push_inst(cx->out, label(stmt->switch_.break_label));
      return;
    }
    default:
      panic("Unexpected AstStmt type: %lu", stmt->ty);
  }
}

static void gen_decl(Context* cx, AstDecl* decl) {
  if (decl->ty != AST_DECL_VAR) {
    // Ignore function declarations in IR stage.
    return;
  }

  if (decl->storage_class == SC_STATIC) {
    // Ignore static variable declarations. These get generated from the symbol
    // table.
    return;
  }

  if (!decl->var.init) {
    return;
  }

  // Rewrite initialization as an assignment.
  IrVal* lhs = var(decl->var.name);
  IrVal* rhs = gen_expr(cx, decl->var.init);
  push_inst(cx->out, copy(rhs, lhs));
}

static void gen_block_item(Context* cx, AstBlockItem* block_item) {
  if (block_item->ty == BLOCK_DECL) {
    gen_decl(cx, block_item->decl);
  } else {
    gen_statement(cx, block_item->stmt);
  }
}

static IrFunction* gen_function(AstDecl* ast_function, SymbolTable* st) {
  IrFunction* ir_function = calloc(1, sizeof(IrFunction));
  ir_function->instructions = vec_new(sizeof(IrInstruction));
  ir_function->name = ast_function->fn.name;
  ir_function->params = vec_new(sizeof(String));

  SymbolTableEntry* st_entry = hashmap_get(st->map, ast_function->fn.name);
  assert(st_entry && st_entry->ty == ST_FN);
  ir_function->global = st_entry->fn.global;

  vec_for_each(ast_function->fn.params, AstFnParam, param) {
    vec_push(ir_function->params, iter.param->ident);
  }

  Context cx = {
      .symbol_table = st,
      .out = ir_function->instructions,
  };
  vec_for_each(ast_function->fn.body, AstBlockItem, block_item) {
    gen_block_item(&cx, iter.block_item);
  }

  // Always return 0 from every function
  push_inst(ir_function->instructions,
            unary_no_dst(IR_RET, constant(zero(st_entry->fn.return_type))));
  return ir_function;
}

IrStaticVariable* gen_static_variable(String* var, SymbolTable* st) {
  SymbolTableEntry* st_entry = hashmap_get(st->map, var);
  assert(st_entry);
  if (st_entry->ty != ST_STATIC_VAR) {
    return NULL;
  }
  if (st_entry->static_.init.ty == INIT_NONE) {
    return NULL;
  }

  // have static variable with initializer.
  IrStaticVariable* ir_static_variable = calloc(1, sizeof(IrStaticVariable));
  ir_static_variable->name = var;
  ir_static_variable->global = st_entry->static_.global;
  ir_static_variable->init = st_entry->static_.init;

  // Handle tentative initialization here. Next pass should never have to deal
  // with INIT_TENTATIVE.
  if (ir_static_variable->init.ty == INIT_TENTATIVE) {
    // zero it out to ensure that the value is zerod.
    memset(&ir_static_variable->init, 0, sizeof(ir_static_variable->init));
    ir_static_variable->init.ty = INIT_HAS_VALUE;
    ir_static_variable->init.c_type = st_entry->static_.c_type;
  }

  return ir_static_variable;
}

IrProgram* gen_ir(AstProgram* ast_program, SymbolTable* symbol_table) {
  IrProgram* ir_program = calloc(1, sizeof(IrProgram));
  ir_program->functions = vec_new(sizeof(IrFunction));
  ir_program->symbol_table = symbol_table;

  vec_for_each(ast_program->decls, AstDecl, decl) {
    if (iter.decl->ty != AST_DECL_FN || iter.decl->fn.body == NULL) {
      continue;
    }
    IrFunction* f = gen_function(iter.decl, symbol_table);
    vec_push(ir_program->functions, f);
  }

  ir_program->static_variables = vec_new(sizeof(IrStaticVariable));
  vec_for_each(symbol_table->symbols, String, symbol) {
    String* symbol = iter.symbol;
    IrStaticVariable* static_variable =
        gen_static_variable(symbol, symbol_table);
    if (static_variable) {
      vec_push(ir_program->static_variables, static_variable);
    }
  }
  return ir_program;
}
