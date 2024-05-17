#ifndef VCC_AST_H
#define VCC_AST_H

#include <vcc/string.h>
#include <vcc/vec.h>

//
// AST expression definition
//
typedef enum {
  EXPR_CONST,
  EXPR_UNARY,
} AstExprType;

typedef struct AstExpr {
  AstExprType ty;
  union {
    // EXPR_CONST
    struct {
      int imm;
    } constant;

    // EXPR_UNARY
    struct {
      enum {
        UNARY_NEG,
        UNARY_COMPLEMENT,
      } op;
      struct AstExpr* expr;
    } unary;
  };
} AstExpr;

//
// AST statement definition
//
typedef enum {
  STMT_RETURN,
} AstStmtType;

typedef struct {
  AstStmtType ty;
  union {
    // STMT_RETURN
    struct {
      AstExpr* expr;
    } ret;
  };
} AstStmt;

//
// AST node definition
//
typedef enum {
  NODE_FN,
  NODE_STMT,
  NODE_EXPR,
} AstNodeType;

typedef struct AstNode {
  AstNodeType ty;
  union {
    // NODE_FN
    struct {
      String* name;

      // This should always be a NODE_STMT
      struct AstNode* body;
    } fn;

    // NODE_STMT
    AstStmt* stmt;

    // NODE_EXPR
    AstExpr* expr;
  };
} AstNode;

typedef struct {
  AstNode* main_function;
} AstProgram;

AstProgram* parse_ast(Vec* tokens);

#endif  // VCC_AST_H