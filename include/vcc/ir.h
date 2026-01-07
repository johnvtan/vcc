#ifndef VCC_IR_H
#define VCC_IR_H

#include <vcc/ast.h>
#include <vcc/typecheck.h>
#include <vcc/vec.h>

typedef struct {
  enum {
    IR_VAL_CONST,
    IR_VAL_VAR,
  } ty;

  // TODO: should this also contain the C type?

  union {
    CompTimeConst constant;
    String* var;
  };
} IrVal;

typedef enum {
  IR_UNKNOWN,
  IR_RET,

  IR_SIGN_EXTEND,
  IR_TRUNCATE,
  IR_ZERO_EXTEND,
  IR_DOUBLE_TO_INT,
  IR_DOUBLE_TO_UINT,
  IR_INT_TO_DOUBLE,
  IR_UINT_TO_DOUBLE,

  IR_UNARY_COMPLEMENT,
  IR_UNARY_NEG,

  IR_ADD,
  IR_SUB,
  IR_MUL,
  IR_DIV,
  IR_REM,
  IR_EQ,
  IR_NEQ,
  IR_LT,
  IR_LTEQ,
  IR_GT,
  IR_GTEQ,

  IR_COPY,
  IR_JMP,
  IR_JZ,
  IR_JNZ,
  IR_LABEL,

  IR_FN_CALL,

  // ptr stuff
  IR_GET_ADDR,
  IR_LOAD,
  IR_STORE,
} IrType;

typedef struct {
  IrType ty;

  // Used by any instructions that return a value,
  // including most unary/binary ops and IR_FN_CALL.
  IrVal* dst;
  IrVal* r1;
  IrVal* r2;

  // Used by IR_LABEL, IR_JZ, IR_JNZ, IR_FN_CALL
  String* label;

  // IR_FN_CALL: Vec<IrVal>
  Vec* args;
} IrInstruction;

typedef struct {
  String* name;

  // Vec<String>
  Vec* params;

  // Vec<IrInstruction>
  Vec* instructions;

  bool global;
} IrFunction;

typedef struct {
  String* name;
  bool global;
  StaticInit init;
} IrStaticVariable;

typedef struct {
  // Vec<IrFunction>
  Vec* functions;

  // Vec<IrStaticVariable>
  Vec* static_variables;
  SymbolTable* symbol_table;
} IrProgram;

// Helpers that are used in gen_x64.c
IrVal* constant(CompTimeConst c);
IrProgram* gen_ir(AstProgram* program, SymbolTable* symbol_table);

#endif  // VCC_IR_H
