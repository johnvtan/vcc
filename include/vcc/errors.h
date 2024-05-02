#ifndef VCC_ERRORS_H
#define VCC_ERRORS_H

#include <stdarg.h>
#include <vcc/file_pos.h>
#include <vcc/string.h>

void emit_error(const FilePos* pos, const char* fmt, ...);

#endif  // VCC_ERRORS_H