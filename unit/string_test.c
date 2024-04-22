#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <vcc/string.h>

const char* cstr = "abcdef\nghijk lmno\tpqrstuvwx\ryz\r\n";

void test_append(void) {
  String* s = string_new();
  const char* c = cstr;
  while (*c) string_append(s, *c++);

  assert(string_eq2(s, cstr));
  assert(string_len(s) == strlen(cstr));
  assert(strncmp(cstring(s), cstr, string_len(s)) == 0);
}

void test_from(void) {
  String* s = string_from(cstr);
  assert(string_eq2(s, cstr));
  assert(string_len(s) == strlen(cstr));
  assert(strncmp(cstring(s), cstr, string_len(s)) == 0);
}

void test_cstring(void) {
  String* s = string_from(cstr);
  char* cstr2 = cstring(s);
  assert(strcmp(cstr, cstr2) == 0);
}

void test_get(void) {
  String* s = string_from(cstr);
  for (size_t i = 0; i < string_len(s); i++)
    assert(string_get(s, i) == cstr[i]);
}

void test_eq(void) {
  String* s1 = string_from(cstr);
  String* s2 = string_from(cstr);
  assert(string_eq(s1, s2));
  assert(string_eq(s2, s1));
  assert(string_eq2(s1, cstr));
  assert(string_eq2(s2, cstr));

  string_append(s1, 'b');
  assert(!string_eq(s1, s2));
  assert(!string_eq(s2, s1));
  assert(!string_eq2(s1, cstr));

  String* e1 = string_new();
  String* e2 = string_new();
  assert(string_eq(e1, e2));

  char* ecstr = "";
  assert(string_eq2(e1, ecstr));
  assert(!string_eq(s1, e1));
  assert(!string_eq(e1, s1));
  assert(!string_eq2(s1, ecstr));
}

void test_format(void) {
  String* s = string_format("a:%d b:%u c:%s", -1, 5, "butt");
  assert(string_eq2(s, "a:-1 b:5 c:butt"));
}

void test_view(void) {
  String* s = string_from(cstr);
  const String* view = string_view_from(s, 5, s->len - 5);

  for (size_t i = 0; i < view->len; i++) {
    assert(string_get(view, i) == string_get(s, i + 5));
  }
}

void test_begins(void) {
  String* s = string_from(cstr);
  assert(string_begins(s, "abc") == 3);
  assert(string_begins(s, "xxx") == 0);
  assert(string_begins(s, "ab") == 2);
  assert(string_begins(s, "") == 0);

  String* s2 = string_from("abcdef");
  assert(string_begins(s2, "abcdef") == 6);

  String* e = string_new();
  assert(string_begins(e, "abc") == 0);
  assert(string_begins(e, "xxx") == 0);
  assert(string_begins(e, "ab") == 0);
  assert(string_begins(e, "") == 0);
}

int main(void) {
  test_append();
  test_from();
  test_cstring();
  test_get();
  test_eq();
  test_format();
  test_begins();
  printf("string test completed\n");
  return 0;
}
