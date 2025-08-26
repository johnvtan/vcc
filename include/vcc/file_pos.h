#ifndef VCC_FILE_POS_H
#define VCC_FILE_POS_H

#include <vcc/string.h>

typedef struct {
  // The name of the file.
  const String* name;

  // The contents of the file.
  const String* contents;

  // The current index/line/col number in the file.
  size_t idx;
  size_t line;
  size_t col;
} FilePos;

bool file_pos_is_eof(const FilePos* pos);
bool file_pos_is_eof_at(const FilePos* pos, size_t n);
String* file_pos_current_line(const FilePos* pos);
size_t file_pos_remaining(const FilePos* pos);

char file_pos_peek_char_at(const FilePos* pos, size_t n);
char file_pos_peek_char(const FilePos* pos);

#endif  // VCC_FLIE_POS_H
