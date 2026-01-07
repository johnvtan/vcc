#include "test_helpers.h"

int main(void) {
  TEST("parse int*") {
    const char* prog = R(int main(void) { int* x; });
    AstProgram* ast = parse_ast(lex(string_from(prog)));
    AstDecl* x = first_decl_from_first_fn(ast);
    assert(x->c_type->ty == CTYPE_PTR);

    CType* c_type = x->c_type;
    assert(c_type->ty == CTYPE_PTR);
    assert(c_type->ptr_ref != NULL);
    assert(c_type->ptr_ref->ty == CTYPE_INT);
  }

  TEST("parse int(*)") {
    const char* prog = R(int main(void) { int(*x); });
    AstProgram* ast = parse_ast(lex(string_from(prog)));
    AstDecl* x = first_decl_from_first_fn(ast);
    assert(x->c_type->ty == CTYPE_PTR);

    CType* c_type = x->c_type;
    assert(c_type->ty == CTYPE_PTR);
    assert(c_type->ptr_ref != NULL);
    assert(c_type->ptr_ref->ty == CTYPE_INT);
  }

  TEST("parse int**") {
    const char* prog = R(int main(void) { int** x; });
    AstProgram* ast = parse_ast(lex(string_from(prog)));
    AstDecl* x = first_decl_from_first_fn(ast);
    assert(x->c_type->ty == CTYPE_PTR);

    CType* first_ptr = x->c_type;
    assert(first_ptr->ty == CTYPE_PTR);
    assert(first_ptr->ptr_ref != NULL);
    assert(first_ptr->ptr_ref->ty == CTYPE_PTR);

    CType* second_ptr = first_ptr->ptr_ref;
    assert(second_ptr->ty == CTYPE_PTR);
    assert(second_ptr->ptr_ref != NULL);
    assert(second_ptr->ptr_ref->ty == CTYPE_INT);
  }

  TEST("parse int(*(*))") {
    const char* prog = R(int main(void) { int(*(*x)); });
    AstProgram* ast = parse_ast(lex(string_from(prog)));
    AstDecl* x = first_decl_from_first_fn(ast);
    assert(x->c_type->ty == CTYPE_PTR);

    CType* first_ptr = x->c_type;
    assert(first_ptr->ty == CTYPE_PTR);
    assert(first_ptr->ptr_ref != NULL);
    assert(first_ptr->ptr_ref->ty == CTYPE_PTR);

    CType* second_ptr = first_ptr->ptr_ref;
    assert(second_ptr->ty == CTYPE_PTR);
    assert(second_ptr->ptr_ref != NULL);
    assert(second_ptr->ptr_ref->ty == CTYPE_INT);
  }

  TEST("parse int* cast") {
    const char* prog = R(int main(void) { int x = (int*)32; });
    AstProgram* ast = parse_ast(lex(string_from(prog)));
    AstDecl* x = first_decl_from_first_fn(ast);

    AstExpr* cast = x->var.init;
    assert(cast);

    CType* c_type = cast->cast.target_type;
    assert(c_type->ty == CTYPE_PTR);
    assert(c_type->ptr_ref);
    assert(c_type->ptr_ref->ty == CTYPE_INT);
  }

  TEST("parse int(*) cast") {
    const char* prog = R(int main(void) { int x = (int(*))32; });
    AstProgram* ast = parse_ast(lex(string_from(prog)));
    AstDecl* x = first_decl_from_first_fn(ast);

    AstExpr* cast = x->var.init;
    assert(cast);

    CType* c_type = cast->cast.target_type;
    assert(c_type->ty == CTYPE_PTR);
    assert(c_type->ptr_ref);
    assert(c_type->ptr_ref->ty == CTYPE_INT);
  }

  TEST("parse int** cast") {
    const char* prog = R(int main(void) { int x = (int**)32; });
    AstProgram* ast = parse_ast(lex(string_from(prog)));
    AstDecl* x = first_decl_from_first_fn(ast);

    AstExpr* cast = x->var.init;
    assert(cast);

    CType* c_type = cast->cast.target_type;
    assert(c_type->ty == CTYPE_PTR);
    assert(c_type->ptr_ref);
    assert(c_type->ptr_ref->ty == CTYPE_PTR);

    c_type = c_type->ptr_ref;
    assert(c_type->ty == CTYPE_PTR);
    assert(c_type->ptr_ref);
    assert(c_type->ptr_ref->ty == CTYPE_INT);
  }

  TEST("parse int(*(*)) cast") {
    const char* prog = R(int main(void) { int x = (int(*(*)))32; });
    AstProgram* ast = parse_ast(lex(string_from(prog)));
    AstDecl* x = first_decl_from_first_fn(ast);

    AstExpr* cast = x->var.init;
    assert(cast);

    CType* c_type = cast->cast.target_type;
    assert(c_type->ty == CTYPE_PTR);
    assert(c_type->ptr_ref);
    assert(c_type->ptr_ref->ty == CTYPE_PTR);

    c_type = c_type->ptr_ref;
    assert(c_type->ty == CTYPE_PTR);
    assert(c_type->ptr_ref);
    assert(c_type->ptr_ref->ty == CTYPE_INT);
  }

  TEST("parse addrof/deref") {
    const char* prog = R(int main(void) {
      int x;
      int* y = &x;
      return *y;
    });
    AstProgram* ast = parse_ast(lex(string_from(prog)));
    AstDecl* main_func = first_func(ast);

    {
      // check addrof
      AstBlockItem* b = vec_get(main_func->fn.body, 1);
      assert(b->ty == BLOCK_DECL);
      AstDecl* y = b->decl;
      assert(y->ty == AST_DECL_VAR);
      AstExpr* addrof = y->var.init;
      assert(addrof->ty == EXPR_UNARY);
      assert(addrof->unary.op == UNARY_ADDROF);
    }

    {
      // check deref
      AstBlockItem* b = vec_get(main_func->fn.body, 2);
      assert(b->ty == BLOCK_STMT);
      AstStmt* ret = b->stmt;
      AstExpr* deref = ret->expr;
      assert(deref->ty == EXPR_UNARY);
      assert(deref->unary.op == UNARY_DEREF);
    }
  }

  TEST("validate binary ok") {
    const char* prog = R(int main(void) {
      int* x;
      int* y;
      x == y;
      x != y;
      !x;
      !y;
      x&& y;
      x || y;
      x == 0;
      y != 0;
      x = 1 ? y : 0;
    });
    AstProgram* ast = parse_ast(lex(string_from(prog)));
    SymbolTable* st = typecheck_ast(ast);
    assert(st);
  }

TEST("validate deref") {
  const char* prog = R(int main(void) { int *x; return *x; });
  AstProgram* ast = parse_ast(lex(string_from(prog)));
  SymbolTable* st = typecheck_ast(ast);
  assert(st);

  AstDecl* main_func = first_func(ast);
  AstBlockItem* b = vec_get(main_func->fn.body, 1);
  assert(b->ty == BLOCK_STMT);

  AstStmt* ret = b->stmt;
  assert(ret->ty == STMT_RETURN);
  assert(ret->expr->ty == EXPR_UNARY);
  assert(ret->expr->c_type->ty == CTYPE_INT);
}
  printf("Ch 14: all tests pass!\n");
  return 0;
}
