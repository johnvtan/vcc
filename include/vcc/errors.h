#ifndef VCC_ERRORS_H
#define VCC_ERRORS_H

#include <stdarg.h>
#include <stdlib.h>
#include <vcc/file_pos.h>
#include <vcc/string.h>

void emit_error(const FilePos* pos, const char* fmt, ...);
void emit_error_no_pos(const char* fmt, ...);

#define panic(fmt, args...)       \
  do {                            \
    emit_error_no_pos(fmt, args); \
    exit(-1);                     \
  } while (0);

#endif  // VCC_ERRORS_H