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

  // Note: SSE registers should always come after general purpose registers.
  // It's easier to validate whether a register is a GP or SSE reg that way.
  REG_XMM0,
  REG_XMM1,
  REG_XMM2,
  REG_XMM3,
  REG_XMM4,
  REG_XMM5,
  REG_XMM6,
  REG_XMM7,
  REG_XMM14,
  REG_XMM15,
} x64_RegType;

typedef enum {
  X64_QUADWORD,
  X64_LONGWORD,
  X64_DOUBLE,
} x64_DataType;

typedef struct {
  x64_OperandType ty;
  // X64_OP_IMM
  uint64_t imm;
  bool is_signed;

  // X64_OP_REG
  x64_RegType reg;

  // X64_OP_STACK
  int stack;

  // X64_OP_LABEL or X64_OP_DATA
  String* ident;

  // X64_OP_DATA
  bool is_constant;
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
  X64_CVTTSD2SI,
  X64_CVTSI2SD,
  X64_DIV_DOUBLE,
  X64_SHR,  // shift right
  X64_XOR,
  X64_AND,  // bitwise and
  X64_OR,   // bitwise or
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
  x64_DataType data_type;

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

// These are constants generated internally by the compiler.
// Currently they're always doubles that are stored in the rodata section.
typedef struct {
  String* name;
  StaticInit init;
  int alignment;
} x64_StaticConst;

typedef struct {
  // Vec<X64_Function*>
  Vec* functions;

  // Vec<x64_StaticVariable>
  Vec* static_variables;

  // Vec<x64_StaticConst>
  Vec* static_constants;
} x64_Program;

x64_Program* generate_x64(IrProgram* ir_program);

#endif  // VCC_GEN_X64_H
