#ifndef VCC_IR_H
#define VCC_IR_H

#include <vcc/ast.h>
#include <vcc/vec.h>

typedef struct {
  enum {
    IR_VAL_CONST,
    IR_VAL_VAR,
  } ty;

  union {
    int constant;
    String* var;
  };
} IrVal;

typedef enum {
  IR_RET,
  IR_UNARY_COMPLEMENT,
  IR_UNARY_NEG,
} IrType;

typedef struct {
  IrType ty;

  IrVal* dst;
  IrVal* r1;
  IrVal* r2;

} IrInstruction;

typedef struct {
  String* name;

  // Vec<IrInstruction>
  Vec* instructions;
} IrFunction;

typedef struct {
  IrFunction* function;
} IrProgram;

IrProgram* gen_ir(AstProgram* program);

#endif  // VCC_IR_H