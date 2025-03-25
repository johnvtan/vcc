#include <assert.h>
#include <stdlib.h>
#include <vcc/ast.h>
#include <vcc/hashmap.h>
#include <vcc/lex.h>

//
// Forward declarations
//
typedef struct ParseContext ParseContext;
static AstDecl* parse_variable_decl(ParseContext* cx);
static AstDecl* parse_decl(ParseContext* cx);
static AstStmt* parse_stmt(ParseContext* cx);

//
// Parsing Context definition
//

// Identifier resolution
typedef struct IdentifierScope IdentifierScope;
typedef struct IdentifierInfo {
  // Internal name, could be different from the key
  // This should be a unique name that can be used
  // as the key to the TypeTable.
  String* name;

  enum {
    NO_LINKAGE = 0,    // local variables
    INTERNAL_LINKAGE,  // static variables
    EXTERNAL_LINKAGE,  // global variables
  } linkage;
} IdentifierInfo;

static IdentifierInfo* new_ident_info(String* name, int linkage) {
  IdentifierInfo* info = calloc(1, sizeof(IdentifierInfo));
  info->name = name;
  info->linkage = linkage;
  return info;
}

struct IdentifierScope {
  Hashmap* map;  // Hashmap<String, IdentifierInfo>
  IdentifierScope* parent;
};

typedef struct {
  IdentifierInfo* info;
  bool in_current_scope;
} ResolvedIdentifier;

static ResolvedIdentifier resolve_identifier(IdentifierScope* curr_scope,
                                             String* ident) {
  for (IdentifierScope* scope = curr_scope; scope; scope = scope->parent) {
    IdentifierInfo* info = hashmap_get(scope->map, ident);
    if (info) {
      return (ResolvedIdentifier){info, scope == curr_scope};
    }
  }

  return (ResolvedIdentifier){NULL, false};
}

//
// Type checking
// Note: type checking is handled separately from identifier resolution.
// The TypeTable is a flat map where each identifier has a unique name.
//

// Hashmap<String, TypeTableEntry>
typedef Hashmap TypeTable;
typedef struct TypeTableEntry {
  enum {
    TT_FN,
    TT_VAR,
  } ty;

  // TT_VAR
  CType var_type;

  // TT_FN
  struct {
    size_t num_params;
    bool defined;
  } fn;
} TypeTableEntry;

static TypeTableEntry* type_table_get(TypeTable* tt, String* unique_name) {
  return hashmap_get(tt, unique_name);
}

static void type_table_put_var(TypeTable* tt, String* name, CType var_type) {
  TypeTableEntry* e = calloc(1, sizeof(TypeTableEntry));
  e->ty = TT_VAR;
  e->var_type = var_type;
  hashmap_put(tt, name, e);
}

static void type_table_put_fn(TypeTable* tt, String* name, size_t num_params,
                              bool defined) {
  TypeTableEntry* e = calloc(1, sizeof(TypeTableEntry));
  e->ty = TT_FN;
  e->fn.num_params = num_params;
  e->fn.defined = defined;
  hashmap_put(tt, name, e);
}

// This is basically an iterator through the token list.
// Vec is essentially a stack and only supports pushing to/popping from the
// back.
struct ParseContext {
  const Vec* tokens;
  size_t idx;
  bool err;

  // Used to create unique labels within functions.
  String* curr_fn;

  size_t var_count;
  IdentifierScope* scope;  // per block

  // global -- each identifier should use its unique name.
  TypeTable* type_table;

  // defined labels
  Hashmap* labels;  // Hashmap<string, string>, per functtion --> really a set

  // labels that goto points to
  // We compare gone_to_labels to labels at the end of each function to see
  // that each goto points to a valid label
  Vec* gone_to_labels;

  // Used for parsing break/continue/case statements
  size_t internal_label_count;

  // To avoid copies, these are all vectors of pointers
  Vec* break_stack;     // Vec<String*>
  Vec* continue_stack;  // Vec<String*>
  Vec* case_stack;  // Vec<Vec<AstCaseJump>*> --> collects case statements per
                    // switch is a stack for nested switch statements.
};

static inline bool at_top_level(ParseContext* cx) {
  return cx->scope->parent == NULL;
}

static String* function_unique_label(ParseContext* cx, String* label) {
  return string_format("%s.%s", cstring(cx->curr_fn), cstring(label));
}

// Peeks ahead n+1 tokens
static Token peek_ahead(ParseContext* cx, size_t n) {
  if (cx->idx + n >= cx->tokens->len) {
    emit_error_no_pos("Expected token but got EOF");
    // vec_get will abort the program if this is true.
  }
  return *(Token*)(vec_get(cx->tokens, cx->idx + n));
}

// Peek the next token.
static inline Token peek(ParseContext* cx) { return peek_ahead(cx, 0); }

// Note this makes a temp in case we pass in an rvalue (e.g., &cx).
// We shouldn't have scoping issues because this is wrapped in its own scope.
#define emit_error_at(cx, args...) \
  do {                             \
    ParseContext* cx_tmp = cx;     \
    Token t = peek(cx_tmp);        \
    emit_error(&t.pos, args);      \
    cx_tmp->err = true;            \
    cx_tmp->idx++;                 \
  } while (0);

// Return the current token and advances |cx|.
static Token consume(ParseContext* cx) {
  Token t = peek(cx);
  cx->idx++;
  return t;
}

static bool match(ParseContext* cx, TokenType ty) { return peek(cx).ty == ty; }

// Emits an error if the current token doesn't match |ty|.
// If there
static Token expect(ParseContext* cx, TokenType ty) {
  Token curr = peek(cx);
  if (curr.ty != ty) {
    emit_error_at(cx, "Expected token %lu but got %lu", ty, curr.ty)
  }
  cx->idx++;
  return curr;
}

static inline void assert_lvalue(ParseContext* cx, AstExpr* val) {
  if (val->ty != EXPR_VAR) {
    emit_error_at(cx, "LHS of assign not an lvalue: %u", val->ty);
    exit(-1);
  }

  if (val->c_type != TYPE_INT) {
    emit_error_at(cx, "LHS of assign not an lvalue: %u", val->ty);
    exit(-1);
  }
}

//
// AST type parsing
//

// Parses a type of any expr (i.e., not a function definition).
static CType parse_expr_type(ParseContext* cx) {
  expect(cx, TK_INT);
  return TYPE_INT;
}

//
// Ast expr helper funcs
//

static AstExpr* parse_expr(ParseContext* cx, int min_prec);

static AstExpr* expr(AstExprType ty) {
  AstExpr* e = calloc(1, sizeof(AstExpr));
  e->ty = ty;
  e->c_type = TYPE_INT;
  return e;
}

static AstExpr* expr_binary(int op, AstExpr* lhs, AstExpr* rhs) {
  AstExpr* e = expr(EXPR_BINARY);
  e->binary.op = op;
  e->binary.lhs = lhs;
  e->binary.rhs = rhs;

  // TODO: typechecking needs to be improved
  if (lhs->c_type != TYPE_INT || rhs->c_type != TYPE_INT) {
    panic("binary ops only work on integer types", 1);
  }
  return e;
}

static AstExpr* expr_ternary(AstExpr* cond, AstExpr* then, AstExpr* else_) {
  AstExpr* e = expr(EXPR_TERNARY);
  e->ternary.cond = cond;
  e->ternary.then = then;
  e->ternary.else_ = else_;
  return e;
}

//
// Recursive descent parsing functions
//
#define PREC_MIN (15)
#define PREC_MAX (1)

// These are the highest precedence operators, i.e.
// they correspond to precedence 2/1/0 in
// https://en.cppreference.com/w/c/language/operator_precedence
static AstExpr* parse_prefix_unary(ParseContext* cx);
static AstExpr* parse_function_call(ParseContext* cx) {
  AstExpr* e = expr(EXPR_FN_CALL);
  Token t = expect(cx, TK_IDENT);

  ResolvedIdentifier r = resolve_identifier(cx->scope, t.content);
  if (r.info == NULL) {
    panic("Function %s called before definition", cstring(t.content));
  }

  // typecheck function call against declaration
  TypeTableEntry* tt_entry = type_table_get(cx->type_table, r.info->name);
  assert(tt_entry);
  if (tt_entry->ty != TT_FN) {
    panic("Cannot call non-function", 1);
  }

  e->fn_call.ident = r.info->name;
  e->fn_call.args = vec_new(sizeof(AstExpr));

  expect(cx, TK_OPEN_PAREN);

  if (!match(cx, TK_CLOSE_PAREN)) {
    // Parse fn args if any exist.
    while (true) {
      AstExpr* arg = parse_expr(cx, PREC_MIN);
      vec_push(e->fn_call.args, arg);

      if (match(cx, TK_CLOSE_PAREN)) {
        break;
      }
      expect(cx, TK_COMMA);
    }
  }

  expect(cx, TK_CLOSE_PAREN);

  // Verify fn_call has correct number of arguments.
  if (tt_entry->fn.num_params != e->fn_call.args->len) {
    panic("Mismatching number of parameters to %s", cstring(e->fn_call.ident));
  }

  return e;
}

static AstExpr* parse_variable(ParseContext* cx) {
  AstExpr* e = expr(EXPR_VAR);
  Token t = expect(cx, TK_IDENT);
  IdentifierInfo* info = resolve_identifier(cx->scope, t.content).info;
  if (!info) {
    emit_error_at(cx, "Undeclared variable: %s", cstring(t.content));
    exit(-1);
  }
  e->ident = info->name;

  // Propagate type into expr
  TypeTableEntry* tt_entry = type_table_get(cx->type_table, e->ident);
  if (!tt_entry) {
    panic("Variable %s has no type", cstring(e->ident));
  }

  if (tt_entry->ty != TT_VAR) {
    panic("%s is a variable but has a function type", cstring(e->ident));
  }

  e->c_type = tt_entry->var_type;
  return e;
}

static AstExpr* parse_primary(ParseContext* cx) {
  if (match(cx, TK_NUM_CONST)) {
    Token t = consume(cx);
    AstExpr* int_const = expr(EXPR_INT_CONST);
    int_const->int_const = strtol(cstring(t.content), NULL, 10);
    return int_const;
  }

  if (match(cx, TK_IDENT)) {
    if (peek_ahead(cx, 1).ty == TK_OPEN_PAREN) {
      return parse_function_call(cx);
    }
    return parse_variable(cx);
  }

  if (match(cx, TK_OPEN_PAREN)) {
    consume(cx);
    AstExpr* e = parse_expr(cx, PREC_MIN);
    expect(cx, TK_CLOSE_PAREN);
    return e;
  }

  emit_error_at(cx, "Unexpected token when parsing primary: %s, %u",
                cstring(peek(cx).content), peek(cx).ty);
  exit(-1);
}

static inline bool is_postfix_op(TokenType ty) {
  switch (ty) {
    case TK_PLUSPLUS:
    case TK_DASHDASH:
      return true;
    default:
      return false;
  }
}

static AstExpr* parse_postfix_unary(ParseContext* cx) {
  AstExpr* e = parse_primary(cx);

  // Avoid left recursion by turning this into a loop
  // postfix rule is something like:
  // postfix_unary := postfix_unary postfix_op | primary
  while (is_postfix_op(peek(cx).ty)) {
    if (match(cx, TK_PLUSPLUS)) {
      consume(cx);
      assert_lvalue(cx, e);
      AstExpr* postfix = expr(EXPR_UNARY);
      postfix->unary.op = UNARY_POSTINC;
      postfix->unary.expr = e;
      e = postfix;
      continue;
    }

    if (match(cx, TK_DASHDASH)) {
      consume(cx);
      assert_lvalue(cx, e);
      AstExpr* postfix = expr(EXPR_UNARY);
      postfix->unary.op = UNARY_POSTDEC;
      postfix->unary.expr = e;
      e = postfix;
      continue;
    }
  }

  return e;
}

static AstExpr* parse_prefix_unary(ParseContext* cx) {
  if (match(cx, TK_TILDE)) {
    consume(cx);
    AstExpr* e = expr(EXPR_UNARY);
    e->unary.op = UNARY_COMPLEMENT;
    e->unary.expr = parse_prefix_unary(cx);
    return e;
  }

  if (match(cx, TK_DASH)) {
    consume(cx);
    AstExpr* e = expr(EXPR_UNARY);
    e->unary.op = UNARY_NEG;
    e->unary.expr = parse_prefix_unary(cx);
    return e;
  }

  if (match(cx, TK_BANG)) {
    consume(cx);
    AstExpr* e = expr(EXPR_UNARY);
    e->unary.op = UNARY_NOT;
    e->unary.expr = parse_prefix_unary(cx);
    return e;
  }

  if (match(cx, TK_PLUSPLUS)) {
    consume(cx);
    AstExpr* e = expr(EXPR_UNARY);
    e->unary.op = UNARY_PREINC;
    e->unary.expr = parse_prefix_unary(cx);
    assert_lvalue(cx, e->unary.expr);
    return e;
  }

  if (match(cx, TK_DASHDASH)) {
    consume(cx);
    AstExpr* e = expr(EXPR_UNARY);
    e->unary.op = UNARY_PREDEC;
    e->unary.expr = parse_prefix_unary(cx);
    assert_lvalue(cx, e->unary.expr);
    return e;
  }

  return parse_postfix_unary(cx);
}

typedef struct {
  int prec;
  int op;
  bool is_assign;
} BinaryInfo;

// For binary operators, returns the BinaryInfo.
//
// Returns {-1, -1} if not a binary operator.
static inline BinaryInfo binary_info(TokenType ty) {
  switch (ty) {
    case TK_STAR:
      return (BinaryInfo){3, BINARY_MUL, false};
    case TK_SLASH:
      return (BinaryInfo){3, BINARY_DIV, false};
    case TK_PERCENT:
      return (BinaryInfo){3, BINARY_REM, false};
    case TK_PLUS:
      return (BinaryInfo){4, BINARY_ADD, false};
    case TK_DASH:
      return (BinaryInfo){4, BINARY_SUB, false};
    case TK_LT:
      return (BinaryInfo){6, BINARY_LT, false};
    case TK_LTEQ:
      return (BinaryInfo){6, BINARY_LTEQ, false};
    case TK_GT:
      return (BinaryInfo){6, BINARY_GT, false};
    case TK_GTEQ:
      return (BinaryInfo){6, BINARY_GTEQ, false};
    case TK_EQEQ:
      return (BinaryInfo){7, BINARY_EQ, false};
    case TK_BANGEQ:
      return (BinaryInfo){7, BINARY_NEQ, false};
    case TK_AMPAMP:
      return (BinaryInfo){11, BINARY_AND, false};
    case TK_PIPEPIPE:
      return (BinaryInfo){12, BINARY_OR, false};
    case TK_QUESTION:
      // This is a ternary, so the operator field isn't used
      return (BinaryInfo){13, -1, false};
    case TK_EQ:
      return (BinaryInfo){14, BINARY_ASSIGN, true};
    case TK_PLUSEQ:
      return (BinaryInfo){14, BINARY_ADD_ASSIGN, true};
    case TK_DASHEQ:
      return (BinaryInfo){14, BINARY_SUB_ASSIGN, true};
    case TK_STAREQ:
      return (BinaryInfo){14, BINARY_MUL_ASSIGN, true};
    case TK_SLASHEQ:
      return (BinaryInfo){14, BINARY_DIV_ASSIGN, true};
    case TK_PERCENTEQ:
      return (BinaryInfo){14, BINARY_REM_ASSIGN, true};
    default:
      return (BinaryInfo){-1, -1, false};
  }
}

static AstExpr* parse_expr(ParseContext* cx, int min_prec) {
  AstExpr* lhs = parse_prefix_unary(cx);
  Token next = peek(cx);
  BinaryInfo info = binary_info(next.ty);
  while (info.prec > 0 && info.prec <= min_prec) {
    consume(cx);  // consume the token because it is a bin op
    if (info.is_assign) {
      assert_lvalue(cx, lhs);

      // assigns are right associative
      AstExpr* rhs = parse_expr(cx, info.prec);
      lhs = expr_binary(info.op, lhs, rhs);
    } else if (next.ty == TK_QUESTION) {
      // parse ternary
      // Question mark was already consumed

      AstExpr* then = parse_expr(cx, PREC_MIN);
      expect(cx, TK_COLON);

      // Ternary is right associative
      AstExpr* else_ = parse_expr(cx, info.prec);

      // Existing lhs is the condition
      lhs = expr_ternary(lhs, then, else_);

    } else {
      AstExpr* rhs = parse_expr(cx, info.prec - 1);
      lhs = expr_binary(info.op, lhs, rhs);
    }

    next = peek(cx);
    info = binary_info(next.ty);
  }
  return lhs;
}

static void parse_block_item(ParseContext* cx, Vec* out) {
  AstBlockItem* b = vec_push_empty(out);
  if (peek(cx).ty == TK_INT) {
    b->ty = BLOCK_DECL;
    b->decl = parse_decl(cx);
  } else {
    b->ty = BLOCK_STMT;
    b->stmt = parse_stmt(cx);
  }
}

// Returns Vec<AstBlockItem>.
// Parsing includes consuming { and } tokens.
static Vec* parse_block_with_ident_map(ParseContext* cx, Hashmap* h) {
  IdentifierScope scope = {
      .map = h,
      .parent = cx->scope,
  };

  cx->scope = &scope;

  expect(cx, TK_OPEN_BRACE);
  Vec* block = vec_new(sizeof(AstBlockItem));
  while (peek(cx).ty != TK_CLOSE_BRACE) {
    parse_block_item(cx, block);
  }

  expect(cx, TK_CLOSE_BRACE);
  cx->scope = cx->scope->parent;
  return block;
}

static Vec* parse_block(ParseContext* cx) {
  return parse_block_with_ident_map(cx, hashmap_new());
}

static AstStmt* parse_stmt(ParseContext* cx) {
  AstStmt* s = calloc(1, sizeof(AstStmt));

  if (match(cx, TK_RETURN)) {
    consume(cx);
    s->ty = STMT_RETURN;
    s->expr = parse_expr(cx, PREC_MIN);
    expect(cx, TK_SEMICOLON);
    return s;
  }

  if (match(cx, TK_SEMICOLON)) {
    s->ty = STMT_NULL;
    expect(cx, TK_SEMICOLON);
    return s;
  }

  if (match(cx, TK_IF)) {
    s->ty = STMT_IF;

    consume(cx);
    expect(cx, TK_OPEN_PAREN);
    s->if_.cond = parse_expr(cx, PREC_MIN);
    expect(cx, TK_CLOSE_PAREN);

    s->if_.then = parse_stmt(cx);
    if (match(cx, TK_ELSE)) {
      consume(cx);
      s->if_.else_ = parse_stmt(cx);
    }
    return s;
  }

  if (match(cx, TK_GOTO)) {
    consume(cx);
    s->ty = STMT_GOTO;

    Token t = expect(cx, TK_IDENT);
    s->ident = function_unique_label(cx, t.content);
    vec_push(cx->gone_to_labels, s->ident);

    expect(cx, TK_SEMICOLON);
    return s;
  }

  if (match(cx, TK_OPEN_BRACE)) {
    s->ty = STMT_COMPOUND;
    s->block = parse_block(cx);
    return s;
  }

  if (match(cx, TK_BREAK)) {
    consume(cx);
    if (cx->break_stack->len == 0) {
      panic("In break but no break label %d", 1);
    }

    // Break is rewritten as a goto to the break_label.
    // Note that the break_label doesn't exist in the AST.
    // We'll insert the appropriate label in IR generation.
    s->ty = STMT_GOTO;
    s->ident = *(String**)vec_back(cx->break_stack);
    expect(cx, TK_SEMICOLON);
    return s;
  }

  if (match(cx, TK_CONTINUE)) {
    consume(cx);
    if (cx->continue_stack->len == 0) {
      panic("In continue but no continue labels %d", 1);
    }

    // Continue is rewritten as a goto to the break_label.
    // Note that the break_label doesn't exist in the AST.
    // We'll insert the appropriate label in IR generation.
    s->ty = STMT_GOTO;
    s->ident = *(String**)vec_back(cx->continue_stack);
    expect(cx, TK_SEMICOLON);
    return s;
  }

  if (match(cx, TK_SWITCH)) {
    consume(cx);
    s->ty = STMT_SWITCH;

    s->switch_.break_label =
        string_format(".AST.SWITCH.BREAK.%d", cx->internal_label_count);
    s->switch_.case_jumps = vec_new(sizeof(AstCaseJump));
    cx->internal_label_count++;

    vec_push(cx->break_stack, &s->while_.break_label);
    vec_push(cx->case_stack, &s->switch_.case_jumps);

    expect(cx, TK_OPEN_PAREN);
    s->switch_.cond = parse_expr(cx, PREC_MIN);
    CType cond_type = s->switch_.cond->c_type;
    if (cond_type != TYPE_INT) {
      panic("Cannot switch on non-integer", 1);
    }
    expect(cx, TK_CLOSE_PAREN);

    s->switch_.body = parse_stmt(cx);

    vec_pop(cx->break_stack);
    vec_pop(cx->case_stack);

    // Verify cases (e.g., no duplicates).
    Hashmap* case_conds = hashmap_new();
    bool has_default = false;
    vec_for_each(s->switch_.case_jumps, AstCaseJump, case_) {
      if (iter.case_->is_default) {
        if (has_default) {
          panic("Found duplicate default in switch statement", 1);
        }
        has_default = true;
        continue;
      }

      String* stringified_cond =
          string_format("%d", iter.case_->const_expr->int_const);
      if (hashmap_get(case_conds, stringified_cond) != NULL) {
        panic("Found duplicate cond in switch statement", 1);
      }

      hashmap_put(case_conds, stringified_cond, (void*)1);
    }

    return s;
  }

  if (match(cx, TK_CASE) || match(cx, TK_DEFAULT)) {
    if (cx->case_stack->len == 0) {
      panic("Not in switch statement", 1);
    }

    // Under the hood case/default are labeled statements
    s->ty = STMT_LABELED;
    s->labeled.label =
        string_format(".AST.SWITCH.TARGET.%d", cx->internal_label_count++);

    // Update case jumps in switch statement
    Vec** case_stack = vec_back(cx->case_stack);
    AstCaseJump* case_jump = vec_push_empty(*case_stack);
    case_jump->is_default = consume(cx).ty == TK_DEFAULT;
    if (!case_jump->is_default) {
      case_jump->const_expr = parse_primary(cx);
      if (case_jump->const_expr->ty != EXPR_INT_CONST) {
        panic("Expected constant expression in case but got %d",
              case_jump->const_expr->ty);
      }
    }
    case_jump->label = string_copy(s->labeled.label);

    expect(cx, TK_COLON);

    s->labeled.stmt = parse_stmt(cx);
    return s;
  }

  if (match(cx, TK_WHILE)) {
    consume(cx);
    s->ty = STMT_WHILE;

    s->while_.break_label =
        string_format(".AST.WHILE.BREAK.%d", cx->internal_label_count);
    s->while_.continue_label =
        string_format(".AST.WHILE.CONTINUE.%d", cx->internal_label_count);
    cx->internal_label_count++;

    vec_push(cx->break_stack, &s->while_.break_label);
    vec_push(cx->continue_stack, &s->while_.continue_label);

    expect(cx, TK_OPEN_PAREN);
    s->while_.cond = parse_expr(cx, PREC_MIN);
    expect(cx, TK_CLOSE_PAREN);
    s->while_.body = parse_stmt(cx);

    vec_pop(cx->break_stack);
    vec_pop(cx->continue_stack);
    return s;
  }

  if (match(cx, TK_DO)) {
    consume(cx);
    s->ty = STMT_DOWHILE;

    s->while_.break_label =
        string_format(".AST.DOWHILE.BREAK.%d", cx->internal_label_count);
    s->while_.continue_label =
        string_format(".AST.DOWHILE.CONTINUE.%d", cx->internal_label_count);
    cx->internal_label_count++;

    vec_push(cx->break_stack, &s->while_.break_label);
    vec_push(cx->continue_stack, &s->while_.continue_label);

    s->while_.body = parse_stmt(cx);

    expect(cx, TK_WHILE);
    expect(cx, TK_OPEN_PAREN);
    s->while_.cond = parse_expr(cx, PREC_MIN);
    expect(cx, TK_CLOSE_PAREN);
    expect(cx, TK_SEMICOLON);

    vec_pop(cx->break_stack);
    vec_pop(cx->continue_stack);
    return s;
  }

  if (match(cx, TK_FOR)) {
    consume(cx);
    s->ty = STMT_FOR;

    // for stmt gets new scope
    IdentifierScope scope = {
        .map = hashmap_new(),
        .parent = cx->scope,
    };
    cx->scope = &scope;

    s->for_.break_label =
        string_format(".AST.FOR.BREAK.%d", cx->internal_label_count);
    s->for_.continue_label =
        string_format(".AST.FOR.CONTINUE.%d", cx->internal_label_count);
    cx->internal_label_count++;

    vec_push(cx->break_stack, &s->for_.break_label);
    vec_push(cx->continue_stack, &s->for_.continue_label);

    expect(cx, TK_OPEN_PAREN);

    if (match(cx, TK_SEMICOLON)) {
      s->for_.init.ty = FOR_INIT_NONE;
      consume(cx);
    } else if (match(cx, TK_INT)) {
      s->for_.init.ty = FOR_INIT_DECL;
      s->for_.init.decl = parse_variable_decl(cx);  // consumes semicolon
      if (s->for_.init.decl->ty != AST_DECL_VAR) {
        panic("Only variable declarations allowed in for init", 1);
      }
    } else if (!match(cx, TK_SEMICOLON)) {
      s->for_.init.ty = FOR_INIT_EXPR;
      s->for_.init.expr = parse_expr(cx, PREC_MIN);
      expect(cx, TK_SEMICOLON);
    }

    if (!match(cx, TK_SEMICOLON)) {
      s->for_.cond = parse_expr(cx, PREC_MIN);
    }
    expect(cx, TK_SEMICOLON);

    if (!match(cx, TK_CLOSE_PAREN)) {
      s->for_.post = parse_expr(cx, PREC_MIN);
    }
    expect(cx, TK_CLOSE_PAREN);

    s->for_.body = parse_stmt(cx);

    vec_pop(cx->break_stack);
    vec_pop(cx->continue_stack);
    cx->scope = cx->scope->parent;
    return s;
  }

  if (match(cx, TK_IDENT) && peek_ahead(cx, 1).ty == TK_COLON) {
    // Handle a label statement
    Token t = consume(cx);
    expect(cx, TK_COLON);

    // labels are unique for function so that there are no duplicate labels
    // across functions afer the IR is lowered into assembly. Assuming functions
    // are unique in the translation unit, and labels are unique per function,
    // then all labels should be unique.
    String* label = function_unique_label(cx, t.content);

    if (hashmap_get(cx->labels, label)) {
      panic("Redeclared label %s", t.content);
    }
    hashmap_put(cx->labels, label, (void*)1);

    s->ty = STMT_LABELED;
    s->labeled.label = label;
    s->labeled.stmt = parse_stmt(cx);
    return s;
  }

  // Anything else is an expression statement?
  s->ty = STMT_EXPR;
  s->expr = parse_expr(cx, PREC_MIN);
  expect(cx, TK_SEMICOLON);

  return s;
}

static Vec* parse_parameter_list(ParseContext* cx, Hashmap* ident_map) {
  expect(cx, TK_OPEN_PAREN);
  Vec* param_list = vec_new(sizeof(AstFnParam));
  if (match(cx, TK_VOID)) {
    consume(cx);
    expect(cx, TK_CLOSE_PAREN);
    return param_list;
  }

  while (true) {
    CType c_type = parse_expr_type(cx);
    Token t = expect(cx, TK_IDENT);

    AstFnParam* param = vec_push_empty(param_list);
    param->c_type = c_type;

    if (hashmap_get(ident_map, t.content) != NULL) {
      panic("Parameter %s redeclared", cstring(t.content));
    }

    String* unique_var_name =
        string_format("%s.%u", cstring(t.content), cx->var_count++);
    hashmap_put(ident_map, t.content,
                new_ident_info(unique_var_name, NO_LINKAGE));

    type_table_put_var(cx->type_table, unique_var_name, c_type);

    param->ident = unique_var_name;

    if (match(cx, TK_CLOSE_PAREN)) {
      break;
    }
    expect(cx, TK_COMMA);
  }

  expect(cx, TK_CLOSE_PAREN);
  return param_list;
}

static AstDecl* parse_function_signature(ParseContext* cx, Hashmap* ident_map) {
  parse_expr_type(cx);

  AstDecl* decl = calloc(1, sizeof(AstDecl));
  decl->ty = AST_DECL_FN;
  decl->fn.params = vec_new(sizeof(AstFnParam));

  Token t = expect(cx, TK_IDENT);
  decl->fn.name = t.content;
  decl->fn.params = parse_parameter_list(cx, ident_map);

  ResolvedIdentifier resolved = resolve_identifier(cx->scope, decl->fn.name);
  if (resolved.info) {
    if (resolved.in_current_scope && resolved.info->linkage == NO_LINKAGE) {
      panic("Function declaration %s conflicts with variable name",
            cstring(decl->fn.name));
    }
  }

  // Always add a new entry in the ident map at current scope if it doesn't
  // exist.
  if (!resolved.in_current_scope) {
    hashmap_put(cx->scope->map, decl->fn.name,
                new_ident_info(decl->fn.name, EXTERNAL_LINKAGE));
  }

  // typecheck the declaration
  TypeTableEntry* declared_type = type_table_get(cx->type_table, decl->fn.name);
  size_t num_params = decl->fn.params->len;
  if (declared_type) {
    if (declared_type->ty != TT_FN) {
      panic(
          "Found function declaration for ident %s but previously declared as "
          "a variable.",
          cstring(decl->fn.name));
    }
    if (declared_type->fn.num_params != num_params) {
      panic(
          "Function declaration %s conflicts with mismatching parameter list. "
          "Expected %d but got %d parameters.",
          cstring(decl->fn.name), decl->fn.params->len,
          declared_type->fn.num_params);
    }
  } else {
    // declared type doesn't exist in type table, so insert
    type_table_put_fn(cx->type_table, decl->fn.name, num_params, false);
  }

  return decl;
}

static AstDecl* parse_function(ParseContext* cx) {
  Hashmap* ident_map = hashmap_new();
  AstDecl* decl = parse_function_signature(cx, ident_map);
  if (match(cx, TK_SEMICOLON)) {
    consume(cx);
    return decl;
  }

  cx->curr_fn = decl->fn.name;

  // Handle function body
  if (!match(cx, TK_OPEN_BRACE)) {
    panic("Expected open brace for function body", 1);
  }
  if (!at_top_level(cx)) {
    panic("Nested function definition not allowed", 1);
  }

  TypeTableEntry* tt_entry = type_table_get(cx->type_table, decl->fn.name);
  assert(tt_entry);
  if (tt_entry->ty != TT_FN) {
    panic(
        "Found function declaration for %s, but previously declared as "
        "variable.",
        cstring(decl->fn.name));
  }
  if (tt_entry->fn.defined) {
    panic("Function %s redeclared", cstring(decl->fn.name));
  }
  tt_entry->fn.defined = true;

  cx->labels = hashmap_new();
  cx->gone_to_labels = vec_new(sizeof(String));

  decl->fn.body = parse_block_with_ident_map(cx, ident_map);

  // check all goto statements point to a valid label
  vec_for_each(cx->gone_to_labels, String, label) {
    if (hashmap_get(cx->labels, iter.label) == NULL) {
      panic("Goto to undeclared label %s", iter.label);
    }
  }

  cx->curr_fn = NULL;
  return decl;
}

static AstDecl* parse_variable_decl(ParseContext* cx) {
  CType var_type = parse_expr_type(cx);  // put in symbol table

  AstDecl* decl = calloc(1, sizeof(AstDecl));
  decl->ty = AST_DECL_VAR;

  Token t = expect(cx, TK_IDENT);
  if (hashmap_get(cx->scope->map, t.content) != NULL) {
    panic("Variable %s redefined", t.content);
  }

  // Variable renaming ensures all variable names are unique
  // Generated name should have a period to ensure they don't conflict
  // with user identifiers.
  String* unique_var_name =
      string_format("%s.%u", cstring(t.content), cx->var_count++);

  hashmap_put(cx->scope->map, t.content,
              new_ident_info(unique_var_name, NO_LINKAGE));
  assert(var_type == TYPE_INT);
  decl->var.name = unique_var_name;

  type_table_put_var(cx->type_table, unique_var_name, var_type);

  if (peek(cx).ty == TK_EQ) {
    consume(cx);

    // Under the hood, init expressions are rewritten to be
    // an assign expr.
    AstExpr* init_expr = parse_expr(cx, PREC_MIN);
    AstExpr* var = expr(EXPR_VAR);
    var->ident = decl->var.name;

    decl->var.init = expr_binary(BINARY_ASSIGN, var, init_expr);
    if (decl->var.init->c_type != TYPE_INT) {
      panic("Expected integer expression for variable init", 1);
    }
  }
  expect(cx, TK_SEMICOLON);
  return decl;
}

static AstDecl* parse_decl(ParseContext* cx) {
  if (peek_ahead(cx, 2).ty == TK_OPEN_PAREN) {
    return parse_function(cx);
  }

  return parse_variable_decl(cx);
}

AstProgram* parse_ast(Vec* tokens) {
  IdentifierScope global_scope = {
      .map = hashmap_new(),
      .parent = NULL,
  };
  ParseContext cx = {
      .tokens = tokens,
      .curr_fn = NULL,
      .idx = 0,
      .err = false,
      .var_count = 0,
      .scope = &global_scope,
      .internal_label_count = 0,
      .break_stack = vec_new(sizeof(String*)),
      .continue_stack = vec_new(sizeof(String*)),
      .case_stack = vec_new(sizeof(Vec*)),
      .type_table = hashmap_new(),
  };

  AstProgram* prog = calloc(1, sizeof(AstProgram));
  prog->decls = vec_new(sizeof(AstDecl));

  while (cx.idx < cx.tokens->len) {
    AstDecl* decl = parse_decl(&cx);
    if (decl->ty != AST_DECL_FN) {
      panic("Unexpected variable declaration at top level", 1);
    }
    vec_push(prog->decls, decl);
  }

  return cx.err ? NULL : prog;
}
