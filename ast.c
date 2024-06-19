#include <assert.h>
#include <stdlib.h>
#include <vcc/ast.h>
#include <vcc/hashmap.h>
#include <vcc/lex.h>

//
// Parsing Context definition
//

// This is basically an iterator through the token list.
// Vec is essentially a stack and only supports pushing to/popping from the
// back.
typedef struct {
  const Vec* tokens;
  size_t idx;
  bool err;

  // For variable resolution
  bool do_variable_resolution;
  size_t var_count;
  Hashmap* var_map;  // Hashmap<String, String>
} ParseContext;

// Peek the next token.
static Token peek(ParseContext* cx) {
  if (cx->idx >= cx->tokens->len) {
    emit_error_no_pos("Expected token but got EOF");
    // vec_get will abort the program if this is true.
  }
  return *(Token*)(vec_get(cx->tokens, cx->idx));
}

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
  if (cx->do_variable_resolution && val->ty != EXPR_VAR) {
    emit_error_at(cx, "LHS of assign not an lvalue: %u", val->ty);
    exit(-1);
  }
}

//
// Ast type helper funcs
//

static AstExpr* parse_expr(ParseContext* cx, int min_prec);

static AstNode* node(AstNodeType ty) {
  AstNode* n = calloc(1, sizeof(AstNode));
  n->ty = ty;
  return n;
}

static AstExpr* expr(AstExprType ty) {
  AstExpr* e = calloc(1, sizeof(AstExpr));
  e->ty = ty;
  return e;
}

static AstExpr* expr_binary(int op, AstExpr* lhs, AstExpr* rhs) {
  AstExpr* e = expr(EXPR_BINARY);
  e->binary.op = op;
  e->binary.lhs = lhs;
  e->binary.rhs = rhs;
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
static AstExpr* parse_primary(ParseContext* cx) {
  if (match(cx, TK_NUM_CONST)) {
    Token t = consume(cx);
    AstExpr* int_const = expr(EXPR_INT_CONST);
    int_const->int_const = strtol(cstring(t.content), NULL, 10);
    return int_const;
  }

  if (match(cx, TK_IDENT)) {
    Token t = consume(cx);
    String* unique_name = hashmap_get(cx->var_map, t.content);
    if (!unique_name) {
      if (cx->do_variable_resolution) {
        emit_error_at(cx, "Undeclared variable: %s", cstring(t.content));
        exit(-1);
      } else {
        // Hack to work around validate stage
        unique_name = t.content;
      }
    }
    AstExpr* e = expr(EXPR_VAR);
    e->ident = unique_name;
    return e;
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
    case TK_EQ:
      return (BinaryInfo){14, BINARY_ASSIGN, true};
    case TK_PLUSEQ:
      return (BinaryInfo){14, BINARY_ADD, true};
    case TK_DASHEQ:
      return (BinaryInfo){14, BINARY_SUB, true};
    case TK_STAREQ:
      return (BinaryInfo){14, BINARY_MUL, true};
    case TK_SLASHEQ:
      return (BinaryInfo){14, BINARY_DIV, true};
    case TK_PERCENTEQ:
      return (BinaryInfo){14, BINARY_REM, true};
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
      // rewrite compound assigns
      // e.g., a += 3 --> a = a + 3
      assert_lvalue(cx, lhs);

      // assigns are right associative
      AstExpr* rhs = parse_expr(cx, info.prec);
      if (info.op != BINARY_ASSIGN) {
        // e.g., lhs + rhs if compound assign
        rhs = expr_binary(info.op, lhs, rhs);
      }

      lhs = expr_binary(BINARY_ASSIGN, lhs, rhs);
    } else {
      AstExpr* rhs = parse_expr(cx, info.prec - 1);
      lhs = expr_binary(info.op, lhs, rhs);
    }

    next = peek(cx);
    info = binary_info(next.ty);
  }
  return lhs;
}

static AstStmt* parse_stmt(ParseContext* cx) {
  AstStmt* s = calloc(1, sizeof(AstStmt));

  if (match(cx, TK_RETURN)) {
    consume(cx);
    s->ty = STMT_RETURN;
    s->expr = parse_expr(cx, PREC_MIN);
  } else if (match(cx, TK_SEMICOLON)) {
    s->ty = STMT_NULL;
  } else {
    // Anything else is an expression statement?
    s->ty = STMT_EXPR;
    s->expr = parse_expr(cx, PREC_MIN);
  }

  expect(cx, TK_SEMICOLON);
  return s;
}

static AstDecl* parse_decl(ParseContext* cx) {
  expect(cx, TK_INT);
  Token t = expect(cx, TK_IDENT);
  AstDecl* decl = calloc(1, sizeof(AstDecl));

  if (cx->do_variable_resolution) {
    // Variable renaming ensures all variable names are unique
    // Generated name should have a period to ensure they don't conflict
    // with user identifiers.
    String* unique_var_name =
        string_format("%s.%u", cstring(t.content), cx->var_count++);
    if (hashmap_get(cx->var_map, t.content) != NULL) {
      emit_error_at(cx, "Variable %s redefined", t.content);
      exit(-1);
    }
    hashmap_put(cx->var_map, t.content, unique_var_name);
    decl->name = unique_var_name;
  } else {
    decl->name = t.content;
  }

  if (peek(cx).ty == TK_EQ) {
    consume(cx);
    decl->init = parse_expr(cx, PREC_MIN);
  }

  expect(cx, TK_SEMICOLON);
  return decl;
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

AstNode* parse_function(ParseContext* cx) {
  AstNode* fn = node(NODE_FN);

  expect(cx, TK_INT);
  Token name = expect(cx, TK_IDENT);
  fn->fn.name = name.content;

  expect(cx, TK_OPEN_PAREN);
  expect(cx, TK_VOID);
  expect(cx, TK_CLOSE_PAREN);
  expect(cx, TK_OPEN_BRACE);

  fn->fn.body = vec_new(sizeof(AstBlockItem));
  while (peek(cx).ty != TK_CLOSE_BRACE) {
    parse_block_item(cx, fn->fn.body);
  }

  expect(cx, TK_CLOSE_BRACE);

  return fn;
}

AstProgram* parse_ast(Vec* tokens, bool do_variable_resolution) {
  ParseContext cx = {.tokens = tokens,
                     .idx = 0,
                     .err = false,
                     .do_variable_resolution = do_variable_resolution,
                     .var_count = 0,
                     .var_map = hashmap_new()};
  AstProgram* prog = calloc(1, sizeof(AstProgram));

  prog->main_function = parse_function(&cx);

  // Emit error if we have leftover tokens.
  if (cx.idx < cx.tokens->len) {
    emit_error_at(&cx, "Expected EOF but found more tokens");
  }

  return cx.err ? NULL : prog;
}
