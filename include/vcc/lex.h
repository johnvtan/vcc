#ifndef VCC_LEX_H
#define VCC_LEX_H

#include <vcc/errors.h>
#include <vcc/file_pos.h>
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
  TK_TILDE,
  TK_DASH,
  TK_DASHDASH,
  TK_PLUS,
  TK_PLUSPLUS,
  TK_STAR,
  TK_SLASH,
  TK_PERCENT,
  TK_BANG,
  TK_AMPAMP,
  TK_PIPEPIPE,
  TK_EQEQ,
  TK_EQ,
  TK_BANGEQ,
  TK_LT,
  TK_GT,
  TK_LTEQ,
  TK_GTEQ,
  TK_PLUSEQ,
  TK_DASHEQ,
  TK_STAREQ,
  TK_SLASHEQ,
  TK_PERCENTEQ,

  TK_IDENT,
  TK_NUM_CONST,
} TokenType;

typedef struct {
  TokenType ty;
  String* content;
  FilePos pos;
} Token;

// Returns a vector of Tokens
Vec* lex(const String* input);

#endif  // VCC_LEX_H
