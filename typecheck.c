#include <assert.h>
#include <stdlib.h>
#include <vcc/errors.h>
#include <vcc/typecheck.h>

// Context struct for the typecheck pass.
typedef struct {
  SymbolTable* symbol_table;
  CType* curr_fn_return_type;
} Context;

// forward declarations
static void typecheck_function(Context* cx, AstDecl* decl);
static void typecheck_local_variable_decl(Context* cx, AstDecl* decl);
static void typecheck_block_item(Context* cx, AstBlockItem* block_item);
static void typecheck_expr(Context* cx, AstExpr* expr);

//
// Type conversion helpers.
//

static void check_conversion_allowed(CType* from, CType* to) {
  if (is_float(from) && to->ty == CTYPE_PTR) {
    panic("Casting double to pointer is illegal", 1);
  }

  if (from->ty == CTYPE_PTR && is_float(to)) {
    panic("Casting pointer to double is illegal", 1);
  }
}
static AstExpr* convert_to(AstExpr* e, CType* target_type) {
  assert(e->c_type->ty != CTYPE_NONE);
  if (c_type_eq(e->c_type, target_type)) {
    return e;
  }

  check_conversion_allowed(e->c_type, target_type);

  AstExpr* cast_expr = calloc(1, sizeof(AstExpr));
  assert(!c_type_eq(e->c_type, target_type));
  cast_expr->ty = EXPR_CAST;
  cast_expr->cast.expr = e;

  // TODO: this seems redundant.
  cast_expr->cast.target_type = target_type;
  cast_expr->c_type = target_type;
  return cast_expr;
}

static NumericValue cast_numeric_value(NumericValue val, CType* from,
                                       CType* to) {
  if (c_type_eq(from, to)) {
    return val;
  }

  if (is_integer(from)) {
    switch (to->ty) {
      case CTYPE_INT:
        return (NumericValue){.int_ = (int)val.int_};
      case CTYPE_LONG:
        return (NumericValue){.int_ = (long)val.int_};
      case CTYPE_UINT:
        return (NumericValue){.int_ = (unsigned int)val.int_};
      case CTYPE_ULONG:
        return (NumericValue){.int_ = (unsigned long)val.int_};
      case CTYPE_DOUBLE:
        return (NumericValue){.double_ = (double)val.int_};
      case CTYPE_PTR: {
        if (val.int_ != 0) {
          panic("Cannot cast non-zero numeric value to pointer.", 1)
        }
        return val;
      }
      case CTYPE_FN:
      case CTYPE_NONE:
        assert(false);
    }
  } else {
    assert(from->ty == CTYPE_DOUBLE);
    switch (to->ty) {
      case CTYPE_INT:
        return (NumericValue){.int_ = (int)val.double_};
      case CTYPE_LONG:
        return (NumericValue){.int_ = (long)val.double_};
      case CTYPE_UINT:
        return (NumericValue){.int_ = (unsigned int)val.double_};
      case CTYPE_ULONG:
        return (NumericValue){.int_ = (unsigned long)val.double_};
      case CTYPE_DOUBLE:
        return (NumericValue){.double_ = (double)val.double_};
      case CTYPE_FN:
      case CTYPE_PTR:
      case CTYPE_NONE:
        assert(false);
    }
  }

  panic("Unhandled cast of numeric value: from=%u, to=%u", from, to);
}

static CompTimeConst convert_comptime_const_to(CompTimeConst c,
                                               CType* target_type) {
  if (c_type_eq(c.c_type, target_type)) {
    return c;
  }

  CompTimeConst ret = {
      .c_type = target_type,
      .numeric = cast_numeric_value(c.numeric, c.c_type, target_type)};
  return ret;
}

static StaticInit convert_static_init_to(StaticInit init, CType* target_type) {
  if (c_type_eq(init.c_type, target_type)) {
    return init;
  }

  return (StaticInit){
      .c_type = target_type,
      .numeric = cast_numeric_value(init.numeric, init.c_type, target_type)};
}

static StaticInit to_static_init(AstExpr* e) {
  assert(e->ty == EXPR_CONST);
  StaticInit ret = {
      .ty = INIT_HAS_VALUE,
      .c_type = e->c_type,
      .numeric = e->const_.numeric,
  };
  return ret;
}

static bool is_null_pointer(AstExpr* e) {
  if (e->ty != EXPR_CONST) {
    return false;
  }

  if (!is_integer(e->const_.c_type)) {
    return false;
  }

  return e->const_.numeric.int_ == 0;
}

static CType* get_common_pointer_type(AstExpr* e1, AstExpr* e2) {
  assert(e1->c_type->ty == CTYPE_PTR || e2->c_type->ty == CTYPE_PTR);
  if (c_type_eq(e1->c_type, e2->c_type)) {
    return e1->c_type;
  }

  if (is_null_pointer(e1)) {
    return e2->c_type;
  }

  if (is_null_pointer(e2)) {
    return e1->c_type;
  }

  panic("Cannot get common pointer type for %u %u", e1->c_type->ty,
        e2->c_type->ty);
}

static CType* get_common_expr_type(AstExpr* e1, AstExpr* e2) {
  if (e1->c_type->ty == CTYPE_PTR || e2->c_type->ty == CTYPE_PTR) {
    return get_common_pointer_type(e1, e2);
  }

  return get_common_type(e1->c_type, e2->c_type);
}

static AstExpr* convert_by_assignment(AstExpr* e, CType* target_type);

//
// Symbol table helpers
//

static void symbol_table_put(SymbolTable* st, String* name,
                             SymbolTableEntry e) {
  SymbolTableEntry* copy = calloc(1, sizeof(SymbolTableEntry));
  vec_push(st->symbols, name);
  *copy = e;
  hashmap_put(st->map, name, copy);
}

static void typecheck_file_scope_variable_decl(Context* cx, AstDecl* decl) {
  assert(decl && decl->ty == AST_DECL_VAR);
  SymbolTable* symbol_table = cx->symbol_table;

  // Build up new symbol table entry in case we have to add it to the symbol
  // table or to check against the old entry if it exists.
  SymbolTableEntry new_entry = {
      .ty = ST_STATIC_VAR,
      .c_type = decl->c_type,
      .static_ = {.global = decl->storage_class != SC_STATIC, .init = {}}};

  // check against old entry if it exists
  SymbolTableEntry* st_entry = hashmap_get(symbol_table->map, decl->var.name);
  if (!st_entry) {
    symbol_table_put(symbol_table, decl->var.name, new_entry);
    st_entry = hashmap_get(symbol_table->map, decl->var.name);
  } else {
    // compiler bug -- local variables shoulnd't appear at top level.
    assert(st_entry->ty != ST_LOCAL_VAR);

    // Check new_entry against st_entry.
    if (st_entry->ty != ST_STATIC_VAR) {
      panic("Function redeclared as variable %s", cstring(decl->var.name));
    }

    // Extern declarations take on the value for global from the old
    // declaration, so we can skip this check for extern declarations.
    if (decl->storage_class != SC_EXTERN &&
        (st_entry->static_.global != new_entry.static_.global)) {
      panic(
          "Static variable declaration follows non-static declaration for var "
          "%s",
          cstring(decl->var.name));
    }

    if (!c_type_eq(st_entry->c_type, decl->c_type)) {
      panic("File scope variable %s has conflicting types %u vs %u",
            cstring(decl->var.name), st_entry->c_type, decl->c_type);
    }
  }

  // Typecheck init expression

  // Build up new symbol table entry in case we have to add it to the symbol
  // table or to check against the old entry if it exists.
  StaticVariableSymbol static_var = {.global = decl->storage_class != SC_STATIC,
                                     .init = {}};

  if (decl->var.init) {
    if (decl->var.init->ty != EXPR_CONST) {
      panic(
          "File scope var initializers may only be constant expressions, but "
          "found %d",
          decl->var.init->ty);
    }
    static_var.init =
        convert_static_init_to(to_static_init(decl->var.init), decl->c_type);
    static_var.init.ty = INIT_HAS_VALUE;
  } else if (decl->storage_class == SC_EXTERN) {
    static_var.init.ty = INIT_NONE;
  } else {
    static_var.init.ty = INIT_TENTATIVE;
  }

  // Check for redefinitions.
  if (st_entry->static_.init.ty == INIT_HAS_VALUE &&
      static_var.init.ty == INIT_HAS_VALUE) {
    panic("File scope variable %s redefined", cstring(decl->var.name));
  }

  // Now decide who's initializer to take. Previous or new one?
  // Take on new init value if it has higher priority over the older one.
  // INIT_HAS_VALUE > INIT_TENTATIVE > INIT_NONE.
  //
  // This updates |st_entry| in place.
  if (static_var.init.ty > st_entry->static_.init.ty) {
    st_entry->static_.init = static_var.init;
  }
}

// Typecheck a local variable declaration.
static void typecheck_local_variable_decl(Context* cx, AstDecl* decl) {
  assert(decl && decl->ty == AST_DECL_VAR);

  SymbolTable* symbol_table = cx->symbol_table;
  SymbolTableEntry* st_entry = hashmap_get(symbol_table->map, decl->var.name);

  if (decl->storage_class == SC_EXTERN) {
    if (st_entry) {
      // compiler bug -- local non-extern variables should have unique names and
      // therefore no existing entry in the symbol table before their
      // declaration.
      assert(st_entry->ty != ST_LOCAL_VAR);
      if (st_entry->ty == ST_FN) {
        panic("Function redeclared as variable %s", cstring(decl->var.name));
      }

      if (!c_type_eq(st_entry->c_type, decl->c_type)) {
        panic("Variable %s has conflicting types: %u vs %u",
              cstring(decl->var.name), st_entry->c_type, decl->c_type);
      }
      return;
    }

    if (decl->var.init) {
      panic("Initializer for extern variable %s not allowed",
            cstring(decl->var.name));
    }

    // First declaration for extern variable.
    SymbolTableEntry new_entry = {
        .ty = ST_STATIC_VAR,
        .c_type = decl->c_type,
        .static_ = {// extern variables are global even if they're declared at
                    // block scope
                    .global = true,
                    .init = {
                        .ty = INIT_NONE,
                    }}};
    symbol_table_put(symbol_table, decl->var.name, new_entry);
    return;
  }

  // local variables (both static and other) should have unique names
  // with no previous entries in the symbol table by this point.
  assert(!st_entry);
  if (decl->storage_class == SC_STATIC) {
    SymbolTableEntry new_entry = {
        .ty = ST_STATIC_VAR,
        .c_type = decl->c_type,
        .static_ = {.global = false,
                    .init = {
                        .ty = INIT_HAS_VALUE,
                        // TODO: should this be decl->c_type?
                        .c_type = basic_data_type(CTYPE_INT),
                        .numeric = {0},
                    }}};

    if (decl->var.init) {
      if (decl->var.init->ty != EXPR_CONST) {
        panic(
            "Static block scope variables must have int constant initializers "
            "but found %d",
            decl->var.init->ty);
      }
      new_entry.static_.init = to_static_init(decl->var.init);
    }

    symbol_table_put(symbol_table, decl->var.name, new_entry);
    return;
  }

  // local variable with no storage class.
  // local variables should have a unique name, meaning that no previous symbol
  // table entry should exist.
  SymbolTableEntry new_entry = {.ty = ST_LOCAL_VAR, .c_type = decl->c_type};
  symbol_table_put(symbol_table, decl->var.name, new_entry);
  if (decl->var.init) {
    typecheck_expr(cx, decl->var.init);
    decl->var.init = convert_by_assignment(decl->var.init, decl->c_type);
  }
}

static void check_lvalue(const AstExpr* expr) {
  switch (expr->ty) {
    case EXPR_VAR:
      break;
    case EXPR_UNARY: {
      if (expr->unary.op != UNARY_DEREF) {
        panic("Expected deref but got ty %u", expr->unary.op);
      }
      break;
    }
    default:
      panic("Expected lvalue but got ty %u", expr->ty);
  }
}

static AstExpr* convert_by_assignment(AstExpr* e, CType* target_type) {
  if (c_type_eq(e->c_type, target_type)) {
    return e;
  }

  if (is_arithmetic(e->c_type) && is_arithmetic(target_type)) {
    return convert_to(e, target_type);
  }

  if (is_null_pointer(e) && target_type->ty == CTYPE_PTR) {
    return convert_to(e, target_type);
  }

  panic("Cannot convert type for assignment", 1);
}

static void typecheck_expr(Context* cx, AstExpr* expr) {
  switch (expr->ty) {
    case EXPR_VAR: {
      SymbolTableEntry* st_entry =
          hashmap_get(cx->symbol_table->map, expr->ident);
      if (!st_entry) {
        panic("Variable %s used before declaration", cstring(expr->ident));
      }

      if (st_entry->ty == ST_FN) {
        panic("%s is a variable but has a function type", cstring(expr->ident));
      }

      // propagate type into expr
      expr->c_type = st_entry->c_type;
      assert(expr->c_type && expr->c_type->ty != CTYPE_NONE);
      return;
    }
    case EXPR_UNARY: {
      // TODO: when implementing bitwise, need to enforce that bitwise
      // complement (~) only accepts integer arguments.
      typecheck_expr(cx, expr->unary.expr);

      // By default, set the type of the unary op to the operand's type.
      // Some unary operators, like AddrOf and Deref, will change expr->c_type.
      expr->c_type = expr->unary.expr->c_type;
      switch (expr->unary.op) {
        case UNARY_POSTINC:
        case UNARY_POSTDEC:
        case UNARY_PREINC:
        case UNARY_PREDEC:
          check_lvalue(expr->unary.expr);
          break;
        case UNARY_COMPLEMENT:
          if (!is_integer(expr->unary.expr->c_type)) {
            panic("Unary complement operand must be an integer", 1);
          }
          break;
        case UNARY_NEG: {
          if (!is_arithmetic(expr->unary.expr->c_type)) {
            panic("Unary neg operand must be arithmetic", 1);
          }
          break;
        }
        case UNARY_ADDROF: {
          const AstExpr* lvalue = expr->unary.expr;
          check_lvalue(lvalue);
          expr->c_type = pointer_to(lvalue->c_type);
          break;
        }
        case UNARY_DEREF: {
          const AstExpr* ref = expr->unary.expr;
          if (ref->c_type->ty != CTYPE_PTR) {
            panic("Deref must operate on pointer type, but got %u.",
                  ref->c_type->ty);
          }

          // The type of the deref expression is the type being pointed to.
          expr->c_type = ref->c_type->ptr_ref;
          break;
        }
        case UNARY_NOT:
          expr->c_type = basic_data_type(CTYPE_INT);
          break;
      }

      return;
    }
    case EXPR_BINARY: {
      typecheck_expr(cx, expr->binary.lhs);
      assert(expr->binary.lhs->c_type->ty != CTYPE_NONE);
      typecheck_expr(cx, expr->binary.rhs);
      assert(expr->binary.rhs->c_type->ty != CTYPE_NONE);

      if (expr->binary.op == BINARY_REM ||
          expr->binary.op == BINARY_REM_ASSIGN) {
        // Remainder operator is only valid on integer operands.
        if (!is_integer(expr->binary.lhs->c_type) ||
            !is_integer(expr->binary.rhs->c_type)) {
          panic("Remainder operator is only valid for integer operands.", 1);
        }
      }
      switch (expr->binary.op) {
        case BINARY_ADD_ASSIGN:
        case BINARY_SUB_ASSIGN:
        case BINARY_MUL_ASSIGN:
        case BINARY_DIV_ASSIGN:
        case BINARY_REM_ASSIGN:
          assert(false);
        case BINARY_ASSIGN: {
          // For assigns, implicitly convert rhs to lhs type.
          check_lvalue(expr->binary.lhs);
          expr->binary.rhs =
              convert_by_assignment(expr->binary.rhs, expr->binary.lhs->c_type);
          expr->c_type = expr->binary.lhs->c_type;
          return;
        }
        case BINARY_AND:
        case BINARY_OR: {
          // AND and OR don't need to convert operands.
          expr->c_type = basic_data_type(CTYPE_INT);
          return;
        }
        default: {
          // For all other types, implicitly perform conversion to the common
          // type.
          CType* common_type =
              get_common_expr_type(expr->binary.lhs, expr->binary.rhs);

          expr->binary.lhs = convert_to(expr->binary.lhs, common_type);
          expr->binary.rhs = convert_to(expr->binary.rhs, common_type);
          switch (expr->binary.op) {
            case BINARY_REM:
            case BINARY_MUL:
            case BINARY_DIV: {
              // rem/mul/div don't allow pointer operands
              if (common_type->ty == CTYPE_PTR) {
                panic("Binary operator does not allow pointer operands.", 1);
              }
            }
            case BINARY_ADD:
            case BINARY_SUB:
              // Arithmetic operations get the common type
              expr->c_type = common_type;
              return;
            default:
              // All other comparison operations are always an integer.
              expr->c_type = basic_data_type(CTYPE_INT);
              return;
          }
        }
      }
      return;
    }
    case EXPR_FN_CALL: {
      // typecheck function call against declaration
      SymbolTableEntry* st_entry =
          hashmap_get(cx->symbol_table->map, expr->fn_call.ident);
      if (!st_entry) {
        panic("No function declaration found for %s",
              cstring(expr->fn_call.ident));
      }
      if (st_entry->ty != ST_FN) {
        panic("Variable %s called as a function", cstring(expr->fn_call.ident));
      }

      assert(st_entry->c_type && st_entry->c_type->ty == CTYPE_FN);

      CType* return_type = st_entry->c_type->fn.return_type;
      Vec* param_types = st_entry->c_type->fn.param_types;

      if (param_types->len != expr->fn_call.args->len) {
        panic("Function %s expected %u params but got %u",
              cstring(expr->fn_call.ident), param_types->len,
              expr->fn_call.args->len);
      }

      Vec* converted_args = vec_new(sizeof(AstExpr));
      size_t i = 0;
      vec_for_each(expr->fn_call.args, AstExpr, arg) {
        typecheck_expr(cx, iter.arg);
        CType* param_type = vec_get(param_types, i++);
        vec_push(converted_args, convert_by_assignment(iter.arg, param_type));
      }

      expr->fn_call.args = converted_args;
      expr->c_type = return_type;
      return;
    }
    case EXPR_TERNARY: {
      typecheck_expr(cx, expr->ternary.cond);
      typecheck_expr(cx, expr->ternary.then);
      typecheck_expr(cx, expr->ternary.else_);
      assert(expr->ternary.cond->c_type->ty != CTYPE_NONE);
      assert(expr->ternary.then->c_type->ty != CTYPE_NONE);
      assert(expr->ternary.else_->c_type->ty != CTYPE_NONE);

      CType* common_type =
          get_common_expr_type(expr->ternary.then, expr->ternary.else_);
      expr->ternary.then = convert_to(expr->ternary.then, common_type);
      expr->ternary.else_ = convert_to(expr->ternary.else_, common_type);
      expr->c_type = common_type;
      return;
    }
    case EXPR_CONST: {
      // Constants have their types populated during parsing.
      assert(expr->c_type->ty != CTYPE_NONE);
      assert(c_type_eq(expr->c_type, expr->const_.c_type));
      return;
    }
    case EXPR_CAST: {
      // TODO: check if this is a viable cast?
      typecheck_expr(cx, expr->cast.expr);
      check_conversion_allowed(expr->cast.expr->c_type, expr->cast.target_type);
      expr->c_type = expr->cast.target_type;
      return;
    }
    default:
      // unhandled
      assert(false);
  }
}

static String* comptime_const_to_string(CompTimeConst c) {
  switch (c.c_type->ty) {
    case CTYPE_INT:
      return string_format("%d", c.numeric.int_);
    case CTYPE_LONG:
      return string_format("%ldL", c.numeric.int_);
    case CTYPE_UINT:
      return string_format("%uU", c.numeric.int_);
    case CTYPE_ULONG:
      return string_format("%uUL", c.numeric.int_);
    default:
      assert(false);
  }
}

static void typecheck_statement(Context* cx, AstStmt* stmt) {
  switch (stmt->ty) {
    case STMT_RETURN: {
      typecheck_expr(cx, stmt->expr);
      assert(cx->curr_fn_return_type != NULL);
      stmt->expr = convert_by_assignment(stmt->expr, cx->curr_fn_return_type);
      return;
    }
    case STMT_EXPR: {
      typecheck_expr(cx, stmt->expr);
      return;
    }
    case STMT_LABELED: {
      typecheck_statement(cx, stmt->labeled.stmt);
      return;
    }
    case STMT_COMPOUND: {
      vec_for_each(stmt->block, AstBlockItem, block_item) {
        typecheck_block_item(cx, iter.block_item);
      }
      return;
    }
    case STMT_IF: {
      typecheck_expr(cx, stmt->if_.cond);
      typecheck_statement(cx, stmt->if_.then);
      if (stmt->if_.else_) {
        typecheck_statement(cx, stmt->if_.else_);
      }
      return;
    }
    case STMT_DOWHILE:
    case STMT_WHILE: {
      typecheck_expr(cx, stmt->while_.cond);
      typecheck_statement(cx, stmt->while_.body);
      return;
    }
    case STMT_FOR: {
      if (stmt->for_.init.ty == FOR_INIT_DECL) {
        typecheck_local_variable_decl(cx, stmt->for_.init.decl);
      } else if (stmt->for_.init.ty == FOR_INIT_EXPR) {
        typecheck_expr(cx, stmt->for_.init.expr);
      }

      if (stmt->for_.cond) {
        typecheck_expr(cx, stmt->for_.cond);
      }

      if (stmt->for_.post) {
        typecheck_expr(cx, stmt->for_.post);
      }

      typecheck_statement(cx, stmt->for_.body);
      return;
    }
    case STMT_SWITCH: {
      typecheck_expr(cx, stmt->switch_.cond);
      typecheck_statement(cx, stmt->switch_.body);

      // check case statements and jumps
      Hashmap* case_conds = hashmap_new();
      bool has_default = false;
      CType* switch_cond_ty = stmt->switch_.cond->c_type;
      assert(switch_cond_ty->ty != CTYPE_NONE);
      vec_for_each(stmt->switch_.case_jumps, AstCaseJump, case_) {
        if (iter.case_->is_default) {
          if (has_default) {
            panic("Found duplicate default in switch statement", 1);
          }
          has_default = true;
          continue;
        }

        if (!is_integer(iter.case_->const_expr.c_type)) {
          panic("Cases must be integer constants", 1);
        }

        // Convert each case expression to the type used in the switch
        // condition.
        iter.case_->const_expr =
            convert_comptime_const_to(iter.case_->const_expr, switch_cond_ty);
        String* stringified_cond =
            comptime_const_to_string(iter.case_->const_expr);
        if (hashmap_get(case_conds, stringified_cond) != NULL) {
          panic("Found duplicate cond in switch statement", 1);
        }

        hashmap_put(case_conds, stringified_cond, (void*)1);
      }
      return;
    }
    case STMT_GOTO:
    case STMT_NULL:
      return;
  }
}

static void typecheck_block_item(Context* cx, AstBlockItem* block_item) {
  if (block_item->ty == BLOCK_STMT) {
    typecheck_statement(cx, block_item->stmt);
    return;
  }

  assert(block_item->ty == BLOCK_DECL);
  AstDecl* decl = block_item->decl;
  if (decl->ty == AST_DECL_VAR) {
    // in block scope, we can be sure we're not at top level.
    typecheck_local_variable_decl(cx, decl);
  } else {
    typecheck_function(cx, decl);
  }
}

static void typecheck_function(Context* cx, AstDecl* decl) {
  // Typechecks the function signature in |decl| against a previous declaration
  // if it exists.
  assert(decl->ty == AST_DECL_FN);
  SymbolTable* symbol_table = cx->symbol_table;

  assert(decl->c_type->ty == CTYPE_FN);

  SymbolTableEntry* st_entry = hashmap_get(symbol_table->map, decl->fn.name);

  if (!st_entry) {
    // declared type doesn't exist in type table, so insert
    // No need to type check against previous declaration.
    bool global = decl->storage_class != SC_STATIC;
    assert(decl->c_type->fn.return_type->ty != CTYPE_NONE);
    SymbolTableEntry e = {
        .ty = ST_FN,
        .c_type = decl->c_type,
        .fn =
            {
                .defined = decl->fn.body != NULL,
                .global = global,
            },
    };
    symbol_table_put(symbol_table, decl->fn.name, e);
  } else {
    // have previous declaration, so check against it.
    if (st_entry->ty != ST_FN) {
      panic(
          "Found function declaration for ident %s but previously declared "
          "as "
          "a variable.",
          cstring(decl->fn.name));
    }

    assert(st_entry->c_type->ty == CTYPE_FN);
    if (!c_type_eq(st_entry->c_type, decl->c_type)) {
      panic("Function %s does not match previous declaration",
            cstring(decl->fn.name));
    }

    if (st_entry->fn.global && decl->storage_class == SC_STATIC) {
      panic("Static function declaration for %s follows non-static",
            cstring(decl->fn.name));
    }

    if (st_entry->fn.defined && decl->fn.body) {
      panic("Function %s has more than one definition", cstring(decl->fn.name));
    }
  }

  // Add all parameters to the symbol table.
  // Each function parameter is treated as a local variable that gets
  // its own unique name in the symbol table.
  assert(decl->fn.param_names->len == decl->c_type->fn.param_types->len);
  for (size_t i = 0; i < decl->fn.param_names->len; i++) {
    CType* param_type = vec_get(decl->c_type->fn.param_types, i);
    String* param_name = vec_get(decl->fn.param_names, i);
    SymbolTableEntry e = {.ty = ST_LOCAL_VAR, .c_type = param_type};
    symbol_table_put(cx->symbol_table, param_name, e);
  }

  if (decl->fn.body && decl->fn.body->len) {
    // Setup context for parsing the body.
    // Since we can't have nested function bodies, it should be okay that
    // cx->curr_fn_return_type is a single value instead of a stack.
    assert(cx->curr_fn_return_type == NULL);

    // Set curr_fn_return_type to the declaration's return type. This is used
    // when typechecking and casting return statements.
    cx->curr_fn_return_type = decl->c_type->fn.return_type;
    vec_for_each(decl->fn.body, AstBlockItem, block_item) {
      typecheck_block_item(cx, iter.block_item);
    }

    // When we leave the function body, we can reset this to CTYPE_NONE which
    // indicates that we're no longer in a function body.
    cx->curr_fn_return_type = NULL;
  }
}

SymbolTable* typecheck_ast(AstProgram* prog) {
  Context cx;
  cx.symbol_table = calloc(1, sizeof(SymbolTable));
  cx.symbol_table->map = hashmap_new();
  cx.symbol_table->symbols = vec_new(sizeof(String));
  cx.curr_fn_return_type = NULL;

  vec_for_each(prog->decls, AstDecl, decl) {
    if (iter.decl->ty == AST_DECL_FN) {
      typecheck_function(&cx, iter.decl);
    } else {
      typecheck_file_scope_variable_decl(&cx, iter.decl);
    }
  }

  return cx.symbol_table;
}
