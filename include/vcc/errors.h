#ifndef VCC_ERRORS_H
#define VCC_ERRORS_H

#include <stdarg.h>
#include <vcc/string.h>

typedef struct {
  // The full input string
  const String* input;
  int idx;
  int line;
  int col;
} ErrorContext;

void emit_error(ErrorContext cx, const char* fmt, ...);

#endif  // VCC_ERRORS_H