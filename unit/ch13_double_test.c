#include "test_helpers.h"

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
    assert(main_func->fn.return_type->ty == CTYPE_INT);

    AstBlockItem* b = vec_get(main_func->fn.body, 0);
    assert(b->ty == BLOCK_DECL);

    AstDecl* double_x = b->decl;
    assert(double_x->ty == AST_DECL_VAR);

    const char* kUniqueVarName = "x.0";
    assert(string_eq2(double_x->var.name, kUniqueVarName));
    assert(double_x->var.c_type->ty == CTYPE_DOUBLE);

    AstExpr* init = double_x->var.init;
    assert(init);
    assert(init->ty == EXPR_CONST);
    assert(init->const_.c_type->ty == CTYPE_DOUBLE);
    assert(init->const_.numeric.double_ == 3.0);

    SymbolTable* symbol_table = typecheck_ast(ast);
    assert(symbol_table);

    SymbolTableEntry* entry =
        hashmap_get(symbol_table->map, string_from(kUniqueVarName));
    assert(entry);
    assert(entry->ty == ST_LOCAL_VAR);
    assert(entry->local.c_type->ty == CTYPE_DOUBLE);

    IrProgram* ir = gen_ir(ast, symbol_table);
    x64_Program* asm_prog = generate_x64(ir);
    assert(asm_prog);
    assert(asm_prog->static_constants);
    assert(asm_prog->static_constants->len == 1);

    x64_StaticConst* sc = vec_get(asm_prog->static_constants, 0);
    assert(sc->alignment == 8);
    assert(sc->init_val.double_ == 3.0);
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
    assert(entry->local.c_type->ty == CTYPE_DOUBLE);

    AstDecl* main_func = vec_get(ast->decls, 0);
    AstBlockItem* b = vec_get(main_func->fn.body, 0);
    assert(b->ty == BLOCK_DECL);

    AstDecl* var_decl = b->decl;
    assert(var_decl->ty == AST_DECL_VAR);
    assert(var_decl->var.c_type->ty == CTYPE_DOUBLE);
    assert(string_eq2(var_decl->var.name, "x.0"));

    AstExpr* init = var_decl->var.init;
    assert(init->ty == EXPR_CAST);
    assert(init->cast.target_type->ty == CTYPE_DOUBLE);

    AstExpr* const_init = init->cast.expr;
    assert(const_init->ty == EXPR_CONST);
    assert(const_init->const_.c_type->ty == CTYPE_UINT);
    assert(const_init->const_.numeric.int_ == 1);

    // check generated IR for UINT_TO_DOUBLE instruction
    IrProgram* ir = gen_ir(ast, symbol_table);
    IrFunction* ir_main = vec_get(ir->functions, 0);
    bool found = false;
    vec_for_each(ir_main->instructions, IrInstruction, instr) {
      if (iter.instr->ty == IR_UINT_TO_DOUBLE) {
        found = true;
        IrVal* src = iter.instr->r1;
        assert(src->ty == IR_VAL_CONST);
        assert(src->constant.numeric.int_ == 1);
        break;
      }
    }
    assert(found);
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
    assert(init->const_.c_type->ty == CTYPE_DOUBLE);
    assert(init->const_.numeric.double_ == 3.0);

    SymbolTableEntry* entry = hashmap_get(symbol_table->map, string_from("x"));
    assert(entry);
    assert(entry->ty == ST_STATIC_VAR);

    assert(entry->static_.global == false);
    assert(entry->static_.init.ty == INIT_HAS_VALUE);
    assert(entry->static_.init.c_type->ty == CTYPE_DOUBLE);
    assert(entry->static_.init.numeric.double_ == 3.0);
  }

  // TEST(calling_convention) {
  //   const char* prog =
  //       R(double fn(double d1, double d2, int i1, double d3, double d4,
  //     \n double d5, double d6, unsigned int i2, long i3,
  //     \n double d7, double d8, unsigned long i4, double d9,
  //     \n int i5, double d10, int i6, int i7, double d11,
  //     \n int i8, int i9) { return 0.0; });
  //   AstProgram* ast = parse_ast(lex(string_from(prog)));
  //   SymbolTable* symbol_table = typecheck_ast(ast);
  //   IrProgram* ir = gen_ir(ast, symbol_table);
  //   x64_Program* x64_prog = generate_x86(ir);
  //   assert(x64_prog);
  //   assert(x64_prog->functions->len == 1);
  //   x64_Function* fn = vec_get(x64_prog->functions, 0);
  //   assert(fn);
  // }
}

int main(void) {
  all_tests();

  printf("Ch 13 tests pass!\n");
  return 0;
}
