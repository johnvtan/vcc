#ifndef VCC_LEX_H
#define VCC_LEX_H

#include <vcc/errors.h>
#include <vcc/string.h>
#include <vcc/vec.h>

typedef enum {
  // keywords
  TK_INT,
  TK_VOID,
  TK_RETURN,
  TK_OPEN_PAREN,
  TK_CLOSE_PAREN,
  TK_OPEN_BRACE,
  TK_CLOSE_BRACE,
  TK_SEMICOLON,

  TK_IDENT,
  TK_NUM_CONST,
} TokenType;

typedef struct {
  TokenType ty;
  String* content;
  ErrorContext err_cx;
} Token;

// Returns a vector of Tokens
Vec* lex(const String* input);

#endif  // VCC_LEX_H