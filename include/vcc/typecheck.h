#ifndef VCC_TYPECHECK_H
#define VCC_TYPECHECK_H

#include <vcc/ast.h>

typedef struct {
  enum {
    // NOTE: this is ordered by priority. INIT_NONE is lowest priority.
    // Ensure that priority is maintatined in this definition.
    INIT_NONE = 0,
    INIT_TENTATIVE = 1,
    INIT_HAS_VALUE = 2,
  } ty;

  // only for INIT_HAS_VALUE
  struct {
    CType c_type;
    uint64_t storage_;
  };
} StaticInit;

typedef struct {
  CType c_type;
  bool global;
  StaticInit init;
} StaticVariableSymbol;

typedef struct {
  enum {
    ST_STATIC_VAR,
    ST_LOCAL_VAR,
    ST_FN,
  } ty;

  // TODO: have a single CType field used by everything in the symbol table.

  // ST_FN
  struct {
    bool defined;

    // visibility
    bool global;
    CType return_type;

    // Vec<AstFnParam>
    Vec* params;
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

SymbolTable* typecheck_ast(AstProgram* prog);
CType get_common_type(CType t1, CType t2);

#endif  // VCC_TYPECHECK_H
