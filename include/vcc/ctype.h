#ifndef VCC_CTYPE_H
#define VCC_CTYPE_H

#include <stdbool.h>
#include <stdint.h>

typedef enum {
  CTYPE_NONE = 0,  // used for catching errors
  CTYPE_INT,
  CTYPE_LONG,
  CTYPE_UINT,
  CTYPE_ULONG,
  CTYPE_DOUBLE,
} CTypeKind;  // CTypeType would be unfortunate naming

typedef struct {
  CTypeKind ty;
} CType;

bool c_type_eq(CType* c1, CType* c2);
CType* basic_data_type(CTypeKind ty);

// An architecture-independent way for describing the size of a type. We don't
// specify how many bytes these are in the IR.
typedef enum {
  SIZE_INT,
  SIZE_LONG,
} TypeSize;

// Helpers for determining properties of types.
CType* get_common_type(CType* t1, CType* t2);
TypeSize get_type_size(CType* ty);
bool is_signed(CType* ty);
bool is_integer(CType* ty);
bool is_float(CType* ty);

typedef union {
  uint64_t int_;
  double double_;
} NumericValue;

// Container for a compile time constant.
typedef struct {
  CType* c_type;
  NumericValue numeric;
} CompTimeConst;

#endif  // VCC_CTYPE_H
