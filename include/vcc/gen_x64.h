#ifndef VCC_GEN_X64_H
#define VCC_GEN_X64_H

#include <vcc/ast.h>
#include <vcc/string.h>
#include <vcc/vec.h>

typedef enum {
  X64_OP_IMM,
  X64_OP_REG,
} x64_OperandType;

typedef struct {
  x64_OperandType ty;
  union {
    int imm;
  };
} x64_Operand;

typedef enum {
  X64_MOV,
  X64_RET,
} x64_InstructionType;

typedef struct {
  x64_InstructionType ty;
  union {
    // ty == X64_MOV
    struct {
      x64_Operand src;
      x64_Operand dst;
    } mov;
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

x64_Program* generate_x86(AstProgram* ast_program);

#endif  // VCC_GEN_X64_H