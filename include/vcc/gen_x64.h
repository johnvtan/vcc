#ifndef VCC_GEN_X64_H
#define VCC_GEN_X64_H

#include <vcc/ir.h>
#include <vcc/string.h>
#include <vcc/vec.h>

typedef enum {
  X64_OP_IMM,
  X64_OP_REG,
  X64_OP_PSEUDO,
  X64_OP_STACK,
} x64_OperandType;

typedef enum {
  REG_AX,
  REG_R10,
} x64_RegType;

typedef struct {
  x64_OperandType ty;
  union {
    // X64_OP_IMM
    int imm;

    // X64_OP_REG
    x64_RegType reg;

    // X64_OP_PSEUDO
    String* pseudo;

    // X64_OP_STACK
    int stack;
  };
} x64_Operand;

typedef enum {
  X64_MOV,
  X64_RET,
  X64_NEG,
  X64_NOT,
  X64_ALLOC_STACK,
} x64_InstructionType;

typedef struct {
  x64_InstructionType ty;

  union {
    // Most instruction types
    struct {
      x64_Operand* r1;
      x64_Operand* r2;
    };

    // X64_ALLOC_STACK
    int stack;
  };
} x64_Instruction;

typedef struct {
  String* name;

  // Vec<x64_Instruction>
  Vec* instructions;
} x64_Function;

typedef struct {
  x64_Function* function;
} x64_Program;

x64_Program* generate_x86(IrProgram* ir_program);

#endif  // VCC_GEN_X64_H