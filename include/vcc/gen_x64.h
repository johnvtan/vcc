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
  X64_OP_LABEL,
} x64_OperandType;

typedef enum {
  REG_AX,
  REG_CX,
  REG_DX,
  REG_DI,
  REG_SI,
  REG_R8,
  REG_R9,
  REG_R10,
  REG_R11,
} x64_RegType;

typedef struct {
  x64_OperandType ty;
  // X64_OP_IMM
  int imm;

  // X64_OP_REG
  x64_RegType reg;

  // X64_OP_PSEUDO
  String* pseudo;

  // X64_OP_STACK
  int stack;

  // X64_OP_LABEL
  String* label;

  int size;
} x64_Operand;

typedef enum {
  X64_MOV,
  X64_RET,
  X64_NEG,
  X64_NOT,
  X64_ADD,
  X64_SUB,
  X64_MUL,
  X64_IDIV,
  X64_CDQ,  // sign extend
  X64_CMP,
  X64_JMP,
  X64_JMPCC,
  X64_SETCC,
  X64_LABEL,
  X64_ALLOC_STACK,
  X64_DEALLOC_STACK,
  X64_PUSH,
  X64_CALL,
} x64_InstructionType;

typedef enum {
  CC_E,
  CC_NE,
  CC_G,
  CC_GE,
  CC_L,
  CC_LE,
} x64_ConditionCode;

typedef struct {
  x64_InstructionType ty;

  // Most instruction types
  struct {
    // condition codes
    // Used for SETCC, ignored otherwise
    x64_ConditionCode cc;

    // For JMP and LABEL instructions, r1 contains the label
    x64_Operand* r1;
    x64_Operand* r2;
  };

  // X64_ALLOC_STACK
  int stack;

  // X64_CALL
  String* fn;
} x64_Instruction;

typedef struct {
  String* name;

  // Vec<x64_Instruction>
  Vec* instructions;
  int stack_size;
} x64_Function;

typedef struct {
  // Vec<X64_Function*>
  Vec* functions;
} x64_Program;

x64_Program* generate_x86(IrProgram* ir_program);

#endif  // VCC_GEN_X64_H
