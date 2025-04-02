#ifndef VCC_AST_H
#define VCC_AST_H

#include <vcc/hashmap.h>
#include <vcc/string.h>
#include <vcc/vec.h>

typedef struct AstStmt AstStmt;
typedef struct AstExpr AstExpr;

//
// AST type definition
//

typedef enum CType {
  TYPE_INT,
} CType;

//
// AST expression definition
//

typedef enum {
  EXPR_BINARY,
  EXPR_UNARY,
  EXPR_INT_CONST,
  EXPR_VAR,
  EXPR_TERNARY,
  EXPR_FN_CALL,
} AstExprType;

struct AstExpr {
  // The AST type of the expression.
  // This determines which union variant to use.
  AstExprType ty;

  // The C type of the expression.
  CType c_type;

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

    // EXPR_FN_CALL
    struct {
      String* ident;

      // Vec<AstExpr>
      Vec* args;
    } fn_call;
  };
};

typedef struct AstFnParam {
  CType c_type;
  String* ident;
} AstFnParam;

typedef enum StorageClass {
  SC_NONE,
  SC_STATIC,
  SC_EXTERN,
} StorageClass;

typedef struct {
  enum {
    AST_DECL_VAR,
    AST_DECL_FN,
  } ty;

  StorageClass storage_class;
  union {
    struct {
      enum {
        VAR_LOCAL,
        VAR_STATIC,
      } ty;

      String* name;
      CType c_type;

      // Tentatively declared variables should be initialized to 0.
      AstExpr* init;
    } var;

    struct {
      String* name;

      // Vec<AstFnParam>
      Vec* params;

      // Vec<AstBlockItem>
      Vec* body;
    } fn;
  };
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

typedef struct {
  AstExpr* const_expr;
  bool is_default;
  String* label;
} AstCaseJump;

//
// AST statement definition
//
typedef enum {
  STMT_RETURN,
  STMT_EXPR,
  STMT_IF,
  STMT_GOTO,
  STMT_COMPOUND,
  STMT_LABELED,
  STMT_FOR,
  STMT_WHILE,
  STMT_DOWHILE,
  STMT_SWITCH,
  STMT_NULL,
} AstStmtType;

struct AstStmt {
  AstStmtType ty;
  union {
    AstExpr* expr;

    struct {
      AstExpr* cond;
      AstStmt* then;
      AstStmt* else_;
    } if_;

    // STMT_LABELED
    struct {
      String* label;
      AstStmt* stmt;
    } labeled;

    // STMT_GOTO
    String* ident;

    // STMT_COMPOUND
    // Vec<AstBlockItem>
    Vec* block;

    // STMT_FOR
    struct {
      struct {
        enum {
          FOR_INIT_NONE,
          FOR_INIT_DECL,
          FOR_INIT_EXPR,
        } ty;
        union {
          AstDecl* decl;
          AstExpr* expr;
        };
      } init;

      AstExpr* cond;
      AstExpr* post;
      AstStmt* body;

      String* continue_label;
      String* break_label;
    } for_;

    // STMT_WHILE/STMT_DOWHILE
    struct {
      AstExpr* cond;
      AstStmt* body;

      String* continue_label;
      String* break_label;
    } while_;

    struct {
      // cond must evaluate to an integer
      AstExpr* cond;

      // Case statements are only allowed in here.
      AstStmt* body;

      // Vec<AstCaseJmp>. Case statements are just labeled statements.
      Vec* case_jumps;
      String* break_label;  // no continue in switch statement.
    } switch_;
  };
};

typedef struct {
  CType c_type;
  bool global;
  struct {
    enum {
      // NOTE: this is ordered by priority. INIT_NONE is lowest priority.
      // Ensure that priority is maintatined in this definition.
      INIT_NONE = 0,
      INIT_TENTATIVE = 1,
      INIT_HAS_VALUE = 2,
    } ty;

    // INIT_HAS_VALUE
    int val;
  } init;
} StaticVariableSymbol;

typedef struct {
  enum {
    ST_STATIC_VAR,
    ST_LOCAL_VAR,
    ST_FN,
  } ty;

  // ST_FN
  struct {
    size_t num_params;
    bool defined;

    // visibility
    bool global;
  } fn;

  // ST_STATIC_VAR
  StaticVariableSymbol static_;

  // ST_LOCAL_VAR
  struct {
    CType c_type;
  } local;
} SymbolTableEntry;

typedef struct {
  // |map| is a flat map containing every symbol in the program.
  //
  // The parsing stage guarantees that every symbol in the program has a
  // unique name, which is used as the index into this map. AST nodes with
  // identifiers (like variable and function declarations) will contain the
  // unique name for those identifiers, which can be used to index into this
  // table to get more information about the type of that symbol.
  //
  // Hashmap<String, SymbolTableEntry>
  Hashmap* map;

  // List of all the symbol names in the table.
  // Vec<String>
  Vec* symbols;
} SymbolTable;

typedef struct {
  // Vec<AstDecl>
  Vec* decls;
  SymbolTable* symbol_table;
} AstProgram;

AstProgram* parse_ast(Vec* token);

#endif  // VCC_AST_H
