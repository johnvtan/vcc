#include <assert.h>
#include <vcc/file_pos.h>

bool file_pos_is_eof(const FilePos* pos) {
  return pos->idx >= string_len(pos->contents);
}

String* file_pos_current_line(const FilePos* pos) {
  assert(pos->col <= pos->idx);

  // Find next newline to get extents of the current line
  size_t n = 0;
  while (!file_pos_is_eof(pos) && file_pos_peek_char_at(pos, n) != '\n') {
    n++;
  }

  return string_substring(pos->contents, pos->idx - pos->col, n + pos->col);
}

char file_pos_peek_char_at(const FilePos* pos, size_t n) {
  assert(!file_pos_is_eof(pos));
  return string_get(pos->contents, pos->idx + n);
}

char file_pos_peek_char(const FilePos* pos) {
  return file_pos_peek_char_at(pos, 0);
}