#ifndef VCC_TYPECHECK_H
#define VCC_TYPECHECK_H

#include <vcc/ast.h>

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

SymbolTable* typecheck_ast(AstProgram* prog);

#endif  // VCC_TYPECHECK_H
