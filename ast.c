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
  } while (0);

// Return the current token and advances |cx|.
// static Token consume(ParseContext* cx) {
//   Token t = peek(cx);
//   cx->idx++;
//   return t;
// }

static bool match(ParseContext* cx, TokenType ty) { return peek(cx).ty == ty; }

// Emits an error if the current token doesn't match |ty|.
// Advances |cx| and returns the current token either way.
static Token expect(ParseContext* cx, TokenType ty) {
  Token curr = peek(cx);
  if (curr.ty != ty) {
    emit_error(&curr.pos, "Expected token %lu but got %lu", ty, curr.ty);
    cx->err = true;
  }
  cx->idx++;
  return curr;
}

//
// Ast type helper funcs
//
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

//
// Recursive descent parsing functions
//
static AstExpr* parse_constant(ParseContext* cx) {
  Token t = expect(cx, TK_NUM_CONST);
  AstExpr* e = expr(EXPR_CONST);
  e->constant.imm = strtol(cstring(t.content), NULL, 10);
  return e;
}

static AstStmt* parse_return(ParseContext* cx) {
  expect(cx, TK_RETURN);

  AstStmt* ret = stmt(STMT_RETURN);
  ret->ret.expr = parse_constant(cx);

  return ret;
}

static AstNode* parse_stmt(ParseContext* cx) {
  AstNode* n = node(NODE_STMT);

  if (match(cx, TK_RETURN)) {
    n->stmt = parse_return(cx);
  } else {
    emit_error_at(cx, "Unexpected token when parsing statement");
    cx->err = true;
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
  if (fn->fn.body->ty != NODE_STMT) {
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