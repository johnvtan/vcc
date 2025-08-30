#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <vcc/ast.h>
#include <vcc/lex.h>
#include <vcc/string.h>

#define R(...) #__VA_ARGS__

#define TEST(name) printf("=== Test " #name " ===\n");

void lex_test(void) {
  TEST(double_kw) {
    Vec* tokens = lex(string_from("double"));
    assert(tokens);
    assert(tokens->len == 1);

    Token* tk = vec_get(tokens, 0);
    assert(tk->ty == TK_DOUBLE);
  }

  TEST(3.0) {
    Vec* tokens = lex(string_from("3.0"));
    assert(tokens);
    assert(tokens->len == 1);

    Token* tk = vec_get(tokens, 0);
    assert(tk->ty == TK_DOUBLE_CONST);
    assert(string_eq2(tk->content, "3.0"));
  }

  TEST(3.0234) {
    Vec* tokens = lex(string_from("3.0234"));
    assert(tokens);

    Token* tk = vec_get(tokens, 0);
    assert(tk->ty == TK_DOUBLE_CONST);
    assert(string_eq2(tk->content, "3.0234"));
  }

  TEST(.23) {
    Vec* tokens = lex(string_from(".23"));
    assert(tokens);

    Token* tk = vec_get(tokens, 0);
    assert(tk->ty == TK_DOUBLE_CONST);
    assert(string_eq2(tk->content, ".23"));
  }

  TEST(3e2) {
    Vec* tokens = lex(string_from("3e2"));
    assert(tokens);

    Token* tk = vec_get(tokens, 0);
    assert(tk->ty == TK_DOUBLE_CONST);
    assert(string_eq2(tk->content, "3e2"));
  }

  TEST(3.e2) {
    Vec* tokens = lex(string_from("3.e2"));
    assert(tokens);

    Token* tk = vec_get(tokens, 0);
    assert(tk->ty == TK_DOUBLE_CONST);
    assert(string_eq2(tk->content, "3.e2"));
  }

  TEST(3.1e-2) {
    Vec* tokens = lex(string_from("3.1e-2"));
    assert(tokens);

    Token* tk = vec_get(tokens, 0);
    assert(tk->ty == TK_DOUBLE_CONST);
    assert(string_eq2(tk->content, "3.1e-2"));
  }

  TEST(8.1e+2) {
    Vec* tokens = lex(string_from("8.1e+2"));
    assert(tokens);

    Token* tk = vec_get(tokens, 0);
    assert(tk->ty == TK_DOUBLE_CONST);
    assert(string_eq2(tk->content, "8.1e+2"));
  }

  TEST(123.456e+23) {
    Vec* tokens = lex(string_from("123.456e+23"));
    assert(tokens);

    Token* tk = vec_get(tokens, 0);
    assert(tk->ty == TK_DOUBLE_CONST);
    assert(string_eq2(tk->content, "123.456e+23"));
  }

  TEST(123.3. --invalid) {
    Vec* tokens = lex(string_from("123.3."));
    assert(!tokens);
  }

  TEST(123. - 3) {
    Vec* tokens = lex(string_from("123.-3"));
    assert(tokens);

    Token* tk = vec_get(tokens, 0);
    assert(tk->ty == TK_DOUBLE_CONST);
    assert(string_eq2(tk->content, "123."));
  }

  TEST(1.a) {
    Vec* tokens = lex(string_from("1.a"));
    assert(!tokens);
  }

  TEST(1..) {
    Vec* tokens = lex(string_from("1.."));
    assert(!tokens);
  }

  TEST(.23e4) {
    Vec* tokens = lex(string_from(".23e4"));
    assert(tokens);

    Token* tk = vec_get(tokens, 0);
    assert(tk->ty == TK_DOUBLE_CONST);
    assert(string_eq2(tk->content, ".23e4"));
  }
}

void simple_test(void) {
  const char* prog = R(int main(void) {
    \n double x = 3.0;
    \n return 0;
    \n
  });

  String* input = string_from(prog);
  Vec* tokens = lex(input);
  assert(tokens);

  AstProgram* ast = parse_ast(tokens);
  assert(ast);

  AstDecl* main_func = vec_get(ast->decls, 0);
  assert(main_func->ty == AST_DECL_FN);
  assert(string_eq2(main_func->fn.name, "main"));
  assert(main_func->fn.return_type == TYPE_INT);

  AstBlockItem* b = vec_get(main_func->fn.body, 0);
  assert(b->ty == BLOCK_DECL);

  AstDecl* double_x = b->decl;
  assert(double_x->ty == AST_DECL_VAR);
  assert(string_eq2(double_x->var.name, "x.0"));
  assert(double_x->var.c_type == TYPE_DOUBLE);

  AstExpr* init = double_x->var.init;
  assert(init);
  assert(init->ty == EXPR_CONST);
  assert(init->const_.c_type == TYPE_DOUBLE);
  assert(init->const_.double_storage_ == 3.0);
}

int main(void) {
  lex_test();
  simple_test();

  printf("Ch 13 pass\n");
  return 0;
}
