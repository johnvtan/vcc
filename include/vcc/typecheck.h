#ifndef VCC_TYPECHECK_H
#define VCC_TYPECHECK_H

#include <vcc/ast.h>

typedef struct {
  enum {
    // NOTE: this is ordered by priority. INIT_NONE is lowest priority.
    // Ensure that priority is maintained in this definition.
    INIT_NONE = 0,
    INIT_TENTATIVE = 1,
    INIT_HAS_VALUE = 2,
  } ty;

  // This might be redundant but I think it's a bit easier to reason about
  // when the c_type is attached to the initializer.
  CType* c_type;
  NumericValue numeric;
} StaticInit;

// TODO: add dump static init func here.

typedef struct {
  bool global;
  StaticInit init;
} StaticVariableSymbol;

typedef struct {
  enum {
    ST_STATIC_VAR,
    ST_LOCAL_VAR,
    ST_FN,
  } ty;

  CType* c_type;

  // ST_FN
  struct {
    bool defined;
    bool global;
  } fn;

  // ST_STATIC_VAR
  StaticVariableSymbol static_;
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
