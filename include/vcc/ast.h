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
  EXPR_TERNARY,
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
        UNARY_PREINC,
        UNARY_PREDEC,
        UNARY_POSTINC,
        UNARY_POSTDEC,
      } op;
      AstExpr* expr;
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

        // Note: all assigns should be below BINARY_ASSIGN
        // For ease of checking, assigns are defined as
        // op >= BINARY_ASSIGN.
        BINARY_ASSIGN,
        BINARY_ADD_ASSIGN,
        BINARY_SUB_ASSIGN,
        BINARY_MUL_ASSIGN,
        BINARY_DIV_ASSIGN,
        BINARY_REM_ASSIGN,
      } op;
      AstExpr* lhs;
      AstExpr* rhs;
    } binary;

    struct {
      AstExpr* cond;
      AstExpr* then;
      AstExpr* else_;
    } ternary;

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
  STMT_IF,
  STMT_NULL,
} AstStmtType;

typedef struct AstStmt AstStmt;

struct AstStmt {
  AstStmtType ty;
  union {
    AstExpr* expr;

    struct {
      AstExpr* cond;
      AstStmt* then;
      AstStmt* else_;
    } if_;
  };
};

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
