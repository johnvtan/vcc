#ifndef VCC_AST_H
#define VCC_AST_H

#include <vcc/string.h>
#include <vcc/vec.h>

//
// AST expression definition
//

typedef struct AstExpr AstExpr;

typedef enum {
  EXPR_BINARY,
  EXPR_UNARY,
  EXPR_INT_CONST,
} AstExprType;

struct AstExpr {
  AstExprType ty;
  union {
    // EXPR_FACT
    int int_const;

    // FACT_UNARY
    struct {
      enum {
        UNARY_NEG,
        UNARY_COMPLEMENT,
        UNARY_NOT,
      } op;
      struct AstExpr* expr;
    } unary;

    // EXPR_BINARY
    struct {
      enum {
        BINARY_ADD,
        BINARY_SUB,
        BINARY_MUL,
        BINARY_DIV,
        BINARY_REM,
        BINARY_AND,
        BINARY_OR,
        BINARY_EQ,
        BINARY_NEQ,
        BINARY_LT,
        BINARY_LTEQ,
        BINARY_GT,
        BINARY_GTEQ,
      } op;
      struct AstExpr* lhs;
      struct AstExpr* rhs;
    } binary;
  };
};

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
