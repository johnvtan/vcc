#include <assert.h>
#include <stdlib.h>
#include <vcc/errors.h>
#include <vcc/typecheck.h>

// Context struct for the typecheck pass.
typedef struct {
  SymbolTable* symbol_table;
} Context;

// forward declarations
static void typecheck_function(Context* cx, AstDecl* decl);
static void typecheck_local_variable_decl(Context* cx, AstDecl* decl);
static void typecheck_block_item(Context* cx, AstBlockItem* block_item);
static void typecheck_expr(Context* cx, AstExpr* expr);

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
      .static_ = {.c_type = decl->var.c_type,
                  .global = decl->storage_class != SC_STATIC,
                  .init = {}}};

  // check against old entry if it exists
  SymbolTableEntry* st_entry = hashmap_get(symbol_table->map, decl->var.name);
  if (!st_entry) {
    symbol_table_put(symbol_table, decl->var.name, new_entry);
    st_entry = hashmap_get(symbol_table->map, decl->var.name);
  } else {
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
  }

  // Typecheck init expression

  // Build up new symbol table entry in case we have to add it to the symbol
  // table or to check against the old entry if it exists.
  StaticVariableSymbol static_var = {.c_type = decl->var.c_type,
                                     .global = decl->storage_class != SC_STATIC,
                                     .init = {}};

  if (decl->var.init) {
    if (decl->var.init->ty != EXPR_INT_CONST) {
      panic(
          "File scope var initializers may only be constant expressions, but "
          "found %d",
          decl->var.init->ty);
    }
    static_var.init.ty = INIT_HAS_VALUE;
    static_var.init.val = decl->var.init->int_const;
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
      // compiler bug -- local non-extern variables should have unique names.
      assert(st_entry->ty != ST_LOCAL_VAR);
      if (st_entry->ty == ST_FN) {
        panic("Function redeclared as variable %s", cstring(decl->var.name));
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
        .static_ = {.c_type = decl->var.c_type,

                    // extern variables are global even if they're declared at
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
    SymbolTableEntry new_entry = {.ty = ST_STATIC_VAR,
                                  .static_ = {.c_type = decl->var.c_type,
                                              .global = false,
                                              .init = {
                                                  .ty = INIT_HAS_VALUE,
                                                  .val = 0,
                                              }}};

    if (decl->var.init) {
      if (decl->var.init->ty != EXPR_INT_CONST) {
        panic(
            "Static block scope variables must have int constant initializers "
            "but found %d",
            decl->var.init->ty);
      }
      new_entry.static_.init.val = decl->var.init->int_const;
    }

    symbol_table_put(symbol_table, decl->var.name, new_entry);
    return;
  }

  // local variable with no storage class.
  // local variables should have a unique name, meaning that no previous symbol
  // table entry should exist.
  SymbolTableEntry new_entry = {.ty = ST_LOCAL_VAR,
                                .local = {
                                    .c_type = decl->var.c_type,
                                }};
  symbol_table_put(symbol_table, decl->var.name, new_entry);
  if (decl->var.init) {
    typecheck_expr(cx, decl->var.init);
  }
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
      if (st_entry->ty == ST_LOCAL_VAR) {
        expr->c_type = st_entry->local.c_type;
      } else {
        expr->c_type = st_entry->static_.c_type;
      }
      return;
    }
    case EXPR_UNARY: {
      typecheck_expr(cx, expr->unary.expr);
      return;
    }
    case EXPR_BINARY: {
      typecheck_expr(cx, expr->binary.lhs);
      typecheck_expr(cx, expr->binary.rhs);
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

      if (st_entry->fn.num_params != expr->fn_call.args->len) {
        panic("Function %s expected %u params but got %u",
              cstring(expr->fn_call.ident), st_entry->fn.num_params,
              expr->fn_call.args->len);
      }

      vec_for_each(expr->fn_call.args, AstExpr, arg) {
        typecheck_expr(cx, iter.arg);
      }
      return;
    }
    case EXPR_TERNARY: {
      typecheck_expr(cx, expr->ternary.cond);
      typecheck_expr(cx, expr->ternary.then);
      typecheck_expr(cx, expr->ternary.else_);
      return;
    }
    case EXPR_INT_CONST: {
      return;
    }
  }
}

static void typecheck_statement(Context* cx, AstStmt* stmt) {
  switch (stmt->ty) {
    case STMT_RETURN:
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
  // if
  assert(decl->ty == AST_DECL_FN);
  SymbolTable* symbol_table = cx->symbol_table;

  size_t num_params = decl->fn.params->len;
  SymbolTableEntry* st_entry = hashmap_get(symbol_table->map, decl->fn.name);

  if (!st_entry) {
    // declared type doesn't exist in type table, so insert
    // No need to type check against previous declaration.
    bool global = decl->storage_class != SC_STATIC;
    SymbolTableEntry e = {
        .ty = ST_FN,
        .fn =
            {
                .num_params = num_params,
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
    if (st_entry->fn.num_params != num_params) {
      panic(
          "Function declaration %s conflicts with mismatching parameter list. "
          "Expected %d but got %d parameters.",
          cstring(decl->fn.name), decl->fn.params->len,
          st_entry->fn.num_params);
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
  if (decl->fn.params && decl->fn.params->len) {
    vec_for_each(decl->fn.params, AstFnParam, param) {
      SymbolTableEntry e = {.ty = ST_LOCAL_VAR,
                            .local = {
                                .c_type = iter.param->c_type,
                            }};
      symbol_table_put(cx->symbol_table, iter.param->ident, e);
    }
  }

  if (decl->fn.body && decl->fn.body->len) {
    vec_for_each(decl->fn.body, AstBlockItem, block_item) {
      typecheck_block_item(cx, iter.block_item);
    }
  }
}

SymbolTable* typecheck_ast(AstProgram* prog) {
  Context cx;
  cx.symbol_table = calloc(1, sizeof(SymbolTable));
  cx.symbol_table->map = hashmap_new();
  cx.symbol_table->symbols = vec_new(sizeof(String));

  vec_for_each(prog->decls, AstDecl, decl) {
    if (iter.decl->ty == AST_DECL_FN) {
      typecheck_function(&cx, iter.decl);
    } else {
      typecheck_file_scope_variable_decl(&cx, iter.decl);
    }
  }

  return cx.symbol_table;
}
