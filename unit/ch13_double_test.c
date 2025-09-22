#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <vcc/ast.h>
#include <vcc/lex.h>
#include <vcc/string.h>
#include <vcc/typecheck.h>

#define R(...) #__VA_ARGS__

#define TEST(name) printf("=== Test " #name " ===\n");

void all_tests(void) {
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

  TEST(simple_test) {
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

    const char* kUniqueVarName = "x.0";
    assert(string_eq2(double_x->var.name, kUniqueVarName));
    assert(double_x->var.c_type == TYPE_DOUBLE);

    AstExpr* init = double_x->var.init;
    assert(init);
    assert(init->ty == EXPR_CONST);
    assert(init->const_.c_type == TYPE_DOUBLE);
    assert(init->const_.numeric.double_ == 3.0);

    SymbolTable* symbol_table = typecheck_ast(ast);
    assert(symbol_table);

    SymbolTableEntry* entry =
        hashmap_get(symbol_table->map, string_from(kUniqueVarName));
    assert(entry);
    assert(entry->ty == ST_LOCAL_VAR);
    assert(entry->local.c_type == TYPE_DOUBLE);
  }

  TEST(implicit_conversion_to_double_test) {
    const char* prog = R(int main(void) {
      \n double x = 1u;
      \n return 0;
    });
    String* input = string_from(prog);
    Vec* tokens = lex(input);
    assert(tokens);

    AstProgram* ast = parse_ast(tokens);
    assert(ast);

    SymbolTable* symbol_table = typecheck_ast(ast);
    assert(symbol_table);
    SymbolTableEntry* entry =
        hashmap_get(symbol_table->map, string_from("x.0"));
    assert(entry);
    assert(entry->ty == ST_LOCAL_VAR);
    assert(entry->local.c_type == TYPE_DOUBLE);

    AstDecl* main_func = vec_get(ast->decls, 0);
    AstBlockItem* b = vec_get(main_func->fn.body, 0);
    assert(b->ty == BLOCK_DECL);

    AstDecl* var_decl = b->decl;
    assert(var_decl->ty == AST_DECL_VAR);
    assert(var_decl->var.c_type == TYPE_DOUBLE);
    assert(string_eq2(var_decl->var.name, "x.0"));

    AstExpr* init = var_decl->var.init;
    assert(init->ty == EXPR_CAST);
    assert(init->cast.target_type == TYPE_DOUBLE);

    AstExpr* const_init = init->cast.expr;
    assert(const_init->ty == EXPR_CONST);
    assert(const_init->const_.c_type == TYPE_UINT);
    assert(const_init->const_.numeric.int_ == 1);
  }

  TEST(double_static_init) {
    const char* prog = R(static double x = 3.0;);
    String* input = string_from(prog);
    Vec* tokens = lex(input);
    assert(tokens);

    AstProgram* ast = parse_ast(tokens);
    assert(ast);

    SymbolTable* symbol_table = typecheck_ast(ast);
    assert(symbol_table);

    AstDecl* static_x = vec_get(ast->decls, 0);
    assert(static_x->ty == AST_DECL_VAR);

    assert(static_x->storage_class == SC_STATIC);

    AstExpr* init = static_x->var.init;
    assert(init);
    assert(init->ty == EXPR_CONST);
    assert(init->const_.c_type == TYPE_DOUBLE);
    assert(init->const_.numeric.double_ == 3.0);

    SymbolTableEntry* entry = hashmap_get(symbol_table->map, string_from("x"));
    assert(entry);
    assert(entry->ty == ST_STATIC_VAR);

    assert(entry->static_.global == false);
    assert(entry->static_.init.ty == INIT_HAS_VALUE);
    assert(entry->static_.init.c_type == TYPE_DOUBLE);
    assert(entry->static_.init.numeric.double_ == 3.0);
  }
}

int main(void) {
  all_tests();

  printf("Ch 13 tests pass!\n");
  return 0;
}
