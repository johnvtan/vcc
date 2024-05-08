#include <assert.h>
#include <vcc/errors.h>
#include <vcc/string.h>

#define RED "\e[0;31m"
#define RESET_COLOR "\e[0m"

void emit_error(const FilePos* pos, const char* fmt, ...) {
  va_list args;
  va_start(args, fmt);

  String* line = file_pos_current_line(pos);
  assert(line);

  fprintf(stderr, "line %lu col %lu: " RED "error: " RESET_COLOR, pos->line,
          pos->col);
  vfprintf(stderr, fmt, args);
  fprintf(stderr, "\n%s\n", cstring(line));
  for (size_t i = 0; i < pos->col; i++) {
    fprintf(stderr, " ");
  }
  fprintf(stderr, "^\n");

  va_end(args);
}

void emit_error_no_pos(const char* fmt, ...) {
  va_list args;
  va_start(args, fmt);

  fprintf(stderr, RED "error: " RESET_COLOR);
  vfprintf(stderr, fmt, args);
  fprintf(stderr, "\n");
  va_end(args);
}