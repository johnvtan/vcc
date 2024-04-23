#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <vcc/string.h>

static char kNc = '\0';

String* string_new(void) {
  String* s = (String*)vec_new(sizeof(char));
  string_init(s);
  return s;
}

void string_init(String* s) {
  Vec* v = (Vec*)s;
  vec_init(v, sizeof(char));

  // Internally, strings are always null terminated.
  vec_push(v, &kNc);
}

String* string_from(const char* s) {
  assert(s);
  String* ret = string_new();

  while (*s) string_append(ret, *s++);

  return ret;
}

String* string_copy(const String* s) {
  Vec* v = vec_new_cap(sizeof(char), s->len);
  v->len = s->len;
  memcpy(v->data, s->data, s->len);
  return (String*)v;
}

String* string_substring(const String* s, size_t start, size_t len) {
  assert(len);
  assert(start + len <= s->len);

  Vec* v = vec_new_cap(sizeof(char), len + 1);

  v->len = len;
  memcpy(v->data, &s->data[start], len);

  vec_push(v, &kNc);

  assert(v->len == len + 1);

  return (String*)v;
}

void string_append(String* s, char c) {
  size_t initial_len = s->len;
  Vec* v = (Vec*)s;

  assert(v->len && *(char*)vec_back(v) == kNc);

  // Remove the last null character
  v->len--;

  // Push the character
  vec_push(v, &c);

  // Then push the new null character.
  vec_push(v, &kNc);

  assert(s->len == initial_len + 1);
}

char string_get(const String* s, size_t i) {
  assert(i <= string_len(s));
  return *(char*)(vec_get((Vec*)s, i));
}

size_t string_len(const String* s) {
  // Returns length of the string without the null char.
  assert(s->len);
  return s->len - 1;
}

char* cstring(const String* s) { return s->data; }

bool string_eq(const String* s1, const String* s2) {
  assert(s1 && s2 && s1->len && s2->len);

  if (string_len(s1) != string_len(s2)) return false;

  size_t len = s1->len;
  const char* c1 = s1->data;
  const char* c2 = s2->data;

  while (len--) {
    if (*c1++ != *c2++) return false;
  }
  return true;
}

bool string_eq2(const String* s1, const char* s2) {
  assert(s1 && s2 && s1->len);

  size_t len = string_len(s1);
  const char* c1 = s1->data;

  while (len--) {
    if (*s2 == '\0') return false;
    if (*c1++ != *s2++) return false;
  }

  return *s2 == '\0';
}

size_t string_begins(const String* s1, const char* s2) {
  assert(s1 && s2 && s1->len);

  int matched = 0;
  size_t len = string_len(s1);
  const char* c1 = s1->data;

  while (len--) {
    if (*s2 == '\0') return matched;
    if (*c1++ != *s2++) return 0;
    matched++;
  }

  return *s2 == '\0' ? matched : 0;
}

#define MAX_FMT_LEN (1024U)
String* string_format(const char* fmt, ...) {
  va_list args;
  va_start(args, fmt);

  char buf[MAX_FMT_LEN];
  memset(buf, 0, MAX_FMT_LEN);
  vsnprintf(buf, MAX_FMT_LEN, fmt, args);
  va_end(args);

  return string_from(buf);
}
