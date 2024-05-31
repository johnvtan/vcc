#include <stdlib.h>
#include <vcc/ast.h>
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

//
// Ast type helper funcs
//

static AstExpr* parse_expr(ParseContext* cx, int min_prec);
static AstExpr* parse_factor(ParseContext* cx);

static AstNode* node(AstNodeType ty) {
  AstNode* n = calloc(1, sizeof(AstNode));
  n->ty = ty;
  return n;
}

static AstStmt* stmt(AstStmtType ty) {
  AstStmt* s = calloc(1, sizeof(AstStmt));
  s->ty = ty;
  return s;
}

static AstExpr* expr(AstExprType ty) {
  AstExpr* e = calloc(1, sizeof(AstExpr));
  e->ty = ty;
  return e;
}

static AstExpr* expr_factor(AstFactor* f) {
  AstExpr* e = expr(EXPR_FACT);
  e->factor = f;
  return e;
}

static AstExpr* expr_binary(int op, AstExpr* lhs, AstExpr* rhs) {
  AstExpr* e = expr(EXPR_BINARY);
  e->binary.op = op;
  e->binary.lhs = lhs;
  e->binary.rhs = rhs;
  return e;
}

static AstFactor* factor(AstFactorType ty) {
  AstFactor* f = calloc(1, sizeof(AstFactor));
  f->ty = ty;
  return f;
}

//
// Recursive descent parsing functions
//
static AstExpr* parse_factor(ParseContext* cx) {
  if (match(cx, TK_NUM_CONST)) {
    Token t = consume(cx);
    AstFactor* f = factor(FACT_INT);
    f->int_const = strtol(cstring(t.content), NULL, 10);
    return expr_factor(f);
  }

  if (match(cx, TK_TILDE)) {
    consume(cx);
    AstFactor* f = factor(FACT_UNARY);
    f->unary.op = UNARY_COMPLEMENT;
    f->unary.expr = parse_factor(cx);
    return expr_factor(f);
  }

  if (match(cx, TK_DASH)) {
    consume(cx);
    AstFactor* f = factor(FACT_UNARY);
    f->unary.op = UNARY_NEG;
    f->unary.expr = parse_factor(cx);
    return expr_factor(f);
  }

  if (match(cx, TK_BANG)) {
    consume(cx);
    AstFactor* f = factor(FACT_UNARY);
    f->unary.op = UNARY_NOT;
    f->unary.expr = parse_factor(cx);
    return expr_factor(f);
  }

  if (match(cx, TK_OPEN_PAREN)) {
    consume(cx);
    AstExpr* e = parse_expr(cx, 0);
    expect(cx, TK_CLOSE_PAREN);
    return e;
  }

  emit_error_at(cx, "Unexpected token when parsing factor: %s",
                cstring(peek(cx).content));
  exit(-1);
}

typedef struct {
  int prec;
  int op;
} BinaryInfo;

// For binary operators, returns the BinaryInfo.
//
// Returns {-1, -1} if not a binary operator.
static inline BinaryInfo binary_info(TokenType ty) {
  switch (ty) {
    case TK_PLUS:
      return (BinaryInfo){45, BINARY_ADD};
    case TK_DASH:
      return (BinaryInfo){45, BINARY_SUB};
    case TK_STAR:
      return (BinaryInfo){50, BINARY_MUL};
    case TK_SLASH:
      return (BinaryInfo){50, BINARY_DIV};
    case TK_PERCENT:
      return (BinaryInfo){50, BINARY_REM};
    case TK_LT:
      return (BinaryInfo){35, BINARY_LT};
    case TK_LTEQ:
      return (BinaryInfo){35, BINARY_LTEQ};
    case TK_GT:
      return (BinaryInfo){35, BINARY_GT};
    case TK_GTEQ:
      return (BinaryInfo){35, BINARY_GTEQ};
    case TK_EQEQ:
      return (BinaryInfo){30, BINARY_EQ};
    case TK_BANGEQ:
      return (BinaryInfo){30, BINARY_NEQ};
    case TK_AMPAMP:
      return (BinaryInfo){10, BINARY_AND};
    case TK_PIPEPIPE:
      return (BinaryInfo){5, BINARY_OR};
    default:
      return (BinaryInfo){-1, -1};
  }
}
static AstExpr* parse_expr(ParseContext* cx, int min_prec) {
  AstExpr* lhs = parse_factor(cx);
  Token next = peek(cx);
  BinaryInfo info = binary_info(next.ty);
  while (info.prec > 0 && info.prec > min_prec) {
    consume(cx);  // consume the token because it is a bin op
    AstExpr* rhs = parse_expr(cx, info.prec + 1);
    lhs = expr_binary(info.op, lhs, rhs);
    next = peek(cx);
    info = binary_info(next.ty);
  }
  return lhs;
}

static AstStmt* parse_return(ParseContext* cx) {
  expect(cx, TK_RETURN);

  AstStmt* ret = stmt(STMT_RETURN);
  ret->ret.expr = parse_expr(cx, 0);

  return ret;
}

static AstNode* parse_stmt(ParseContext* cx) {
  AstNode* n = node(NODE_STMT);

  if (match(cx, TK_RETURN)) {
    n->stmt = parse_return(cx);
  } else {
    emit_error_at(cx, "Unexpected token when parsing statement");
    return NULL;
  }

  expect(cx, TK_SEMICOLON);
  return n;
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

  fn->fn.body = parse_stmt(cx);
  if (fn->fn.body && fn->fn.body->ty != NODE_STMT) {
    emit_error_at(cx, "Unexpected function body");
  }
  expect(cx, TK_CLOSE_BRACE);

  return fn;
}

AstProgram* parse_ast(Vec* tokens) {
  ParseContext cx = {.tokens = tokens, .idx = 0, .err = false};
  AstProgram* prog = calloc(1, sizeof(AstProgram));

  prog->main_function = parse_function(&cx);

  // Emit error if we have leftover tokens.
  if (cx.idx < cx.tokens->len) {
    emit_error_at(&cx, "Expected EOF but found more tokens");
  }

  return cx.err ? NULL : prog;
}
