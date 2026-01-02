#ifndef VCC_UNIT_TEST_HELPERS_H
#define VCC_UNIT_TEST_HELPERS_H

#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <vcc/ast.h>
#include <vcc/gen_x64.h>
#include <vcc/ir.h>
#include <vcc/lex.h>
#include <vcc/string.h>
#include <vcc/typecheck.h>

#define R(...) #__VA_ARGS__

#define TEST(name) printf("=== Test " #name " ===\n");

static AstDecl* first_func(AstProgram* ast) {
  assert(ast);
  AstDecl* first = vec_get(ast->decls, 0);
  assert(first->ty == AST_DECL_FN);
  return first;
}

static AstDecl* first_decl_from_first_fn(AstProgram* ast) {
  AstDecl* first = first_func(ast);
  AstBlockItem* b = vec_get(first->fn.body, 0);
  assert(b->ty == BLOCK_DECL);
  return b->decl;
}

#endif
