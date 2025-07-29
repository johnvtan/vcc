#ifndef VCC_GEN_X64_H
#define VCC_GEN_X64_H

#include <vcc/ir.h>
#include <vcc/string.h>
#include <vcc/vec.h>

typedef enum {
  X64_OP_IMM,
  X64_OP_REG,
  X64_OP_STACK,
  X64_OP_LABEL,
  X64_OP_DATA,
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
  REG_SP,
} x64_RegType;

// Determines the suffix used for some instructions.
// E.g. a MOV with a QUADWORD size will be movq.
// The value for each enum variant is the suffix used for
// the instruction.
typedef enum {
  QUADWORD = 'q',
  LONGWORD = 'l',
} x64_Size;

typedef struct {
  x64_OperandType ty;
  // X64_OP_IMM
  uint64_t imm;
  bool sign;

  // X64_OP_REG
  x64_RegType reg;

  // X64_OP_STACK
  int stack;

  // X64_OP_LABEL or X64_OP_DATA
  String* ident;
} x64_Operand;

typedef enum {
  X64_MOV,
  X64_MOVSX,  // move with sign extend
  X64_RET,
  X64_NEG,
  X64_NOT,
  X64_ADD,
  X64_SUB,
  X64_MUL,
  X64_DIV,   // unsigned division
  X64_IDIV,  // signed division
  X64_CDQ,   // sign extend
  X64_CMP,
  X64_JMP,
  X64_JMPCC,
  X64_SETCC,
  X64_LABEL,
  X64_PUSH,
  X64_CALL,
} x64_InstructionType;

typedef enum {
  // Used for both signed and unsigned
  CC_E,
  CC_NE,

  // Used for signed integers.
  CC_G,
  CC_GE,
  CC_L,
  CC_LE,

  // Used for unsigned integers.
  CC_A,
  CC_AE,
  CC_B,
  CC_BE,
} x64_ConditionCode;

typedef struct {
  x64_InstructionType ty;
  x64_Size size;

  // Most instruction types
  struct {
    // condition codes
    // Used for SETCC, ignored otherwise
    x64_ConditionCode cc;

    // For JMP, LABEL, and CALL instructions, r1 contains the label
    // TODO: consider renaming this to src/dst to make it less confusing.
    x64_Operand* r1;
    x64_Operand* r2;
  };
} x64_Instruction;

typedef struct {
  String* name;

  // Vec<x64_Instruction>
  Vec* instructions;
  int stack_size;
  bool global;
} x64_Function;

typedef struct {
  String* name;
  bool global;
  StaticInit init;
  int alignment;
} x64_StaticVariable;

typedef struct {
  // Vec<X64_Function*>
  Vec* functions;

  // Vec<x64_StaticVariable>
  Vec* static_variables;
} x64_Program;

x64_Program* generate_x86(IrProgram* ir_program);

#endif  // VCC_GEN_X64_H
