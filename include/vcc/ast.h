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
  EXPR_VAR,
} AstExprType;

struct AstExpr {
  AstExprType ty;
  union {
    // EXPR_FACT
    int int_const;

    // EXPR_UNARY
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
        BINARY_ASSIGN,
      } op;
      struct AstExpr* lhs;
      struct AstExpr* rhs;
    } binary;

    // EXPR_VAR
    String* ident;
  };
};

//
// AST statement definition
//
typedef enum {
  STMT_RETURN,
  STMT_EXPR,
  STMT_NULL,
} AstStmtType;

typedef struct {
  AstStmtType ty;
  union {
    AstExpr* expr;
  };
} AstStmt;

typedef struct {
  String* name;
  AstExpr* init;
} AstDecl;

typedef struct {
  enum {
    BLOCK_STMT,
    BLOCK_DECL,
  } ty;

  union {
    AstDecl* decl;
    AstStmt* stmt;
  };
} AstBlockItem;

//
// AST node definition
//
typedef enum {
  NODE_FN,
  NODE_STMT,
  NODE_EXPR,
  NODE_DECL,
} AstNodeType;

typedef struct AstNode {
  AstNodeType ty;
  union {
    // NODE_FN
    struct {
      String* name;
      // Vec<AstBlockItem>
      Vec* body;
    } fn;

    // NODE_STMT
    AstStmt* stmt;

    // NODE_EXPR
    AstExpr* expr;

    // NODE_DECL
    AstDecl* decl;
  };
} AstNode;

typedef struct {
  AstNode* main_function;
} AstProgram;

AstProgram* parse_ast(Vec* tokens, bool do_variable_resolution);

#endif  // VCC_AST_H
