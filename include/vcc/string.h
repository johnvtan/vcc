#ifndef VCC_STRING_H
#define VCC_STRING_H

#include <stdbool.h>
#include <vcc/vec.h>

// Strings are just vectors with extra helpers
typedef Vec String;

// Allocate new string
// The string will be zero-initialized
// (e.g., they're all null chars)
String* string_new(void);

// Initialize a string
void string_init(String* s);

// Create new string from C-string
// This copies from s into the newly created
// string.
String* string_from(const char* s);

// Copies a string
String* string_copy(const String* s);

// Copies s[start:start+len] into a new string.
String* string_substring(const String* s, size_t start, size_t len);

// Append a character to s
void string_append(String* s, char c);

// Gets i-th character in s.
char string_get(const String* s, size_t i);

size_t string_len(const String* s);

// Returns a null terminated string
char* cstring(const String* s);

// Checks if two strings are equal
bool string_eq(const String* s1, const String* s2);

// Checks if string and cstring are equal
bool string_eq2(const String* s1, const char* s2);

// Checks that s1 begins with s2
// Returns the length of s2 on success, 0 otherwise.
size_t string_begins(const String* s1, const char* s2);

// Like sprintf, but returns a String.
String* string_format(const char* fmt, ...);

bool string_is_view(const String* s);

#endif
