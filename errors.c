#include <assert.h>
#include <vcc/errors.h>
#include <vcc/string.h>

#define RED "\e[0;31m"
#define RESET_COLOR "\e[0m"

static String* get_error_line(ErrorContext cx) {
  assert(cx.col <= cx.idx);

  // Find next newline to get extents of the current line
  size_t n = 0;
  while (cx.idx + n < string_len(cx.input) &&
         string_get(cx.input, cx.idx + n) != '\n') {
    n++;
  }

  return string_substring(cx.input, cx.idx - cx.col, n + cx.col);
}

void emit_error(ErrorContext cx, const char* fmt, ...) {
  va_list args;
  va_start(args, fmt);

  String* line = get_error_line(cx);
  assert(line);

  fprintf(stderr, "line %u col %u: " RED "error: " RESET_COLOR, cx.line,
          cx.col);
  vfprintf(stderr, fmt, args);
  fprintf(stderr, "\n%s\n", cstring(line));
  for (int i = 0; i < cx.col; i++) {
    fprintf(stderr, " ");
  }
  fprintf(stderr, "^\n");

  va_end(args);
}