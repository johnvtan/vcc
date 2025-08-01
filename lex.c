#include <assert.h>
#include <ctype.h>
#include <stdlib.h>  // qsort
#include <string.h>  // strlen
#include <vcc/lex.h>

//
// Keyword matching helpers
// Keywords are matched in descending order by length.
//
typedef struct {
  TokenType ty;
  char* match;
} KeywordMatch;

static KeywordMatch KEYWORD_MATCHES[] = {
    {TK_INT, "int"},
    {TK_LONG, "long"},
    {TK_UNSIGNED, "unsigned"},
    {TK_SIGNED, "signed"},
    {TK_VOID, "void"},
    {TK_RETURN, "return"},
    {TK_OPEN_PAREN, "("},
    {TK_CLOSE_PAREN, ")"},
    {TK_OPEN_BRACE, "{"},
    {TK_CLOSE_BRACE, "}"},
    {TK_SEMICOLON, ";"},
    {TK_TILDE, "~"},
    {TK_DASH, "-"},
    {TK_DASHDASH, "--"},
    {TK_PLUS, "+"},
    {TK_PLUSPLUS, "++"},
    {TK_STAR, "*"},
    {TK_SLASH, "/"},
    {TK_PERCENT, "%"},
    {TK_BANG, "!"},
    {TK_AMPAMP, "&&"},
    {TK_PIPEPIPE, "||"},
    {TK_EQEQ, "=="},
    {TK_BANGEQ, "!="},
    {TK_LT, "<"},
    {TK_GT, ">"},
    {TK_LTEQ, "<="},
    {TK_GTEQ, ">="},
    {TK_EQ, "="},
    {TK_PLUSEQ, "+="},
    {TK_DASHEQ, "-="},
    {TK_STAREQ, "*="},
    {TK_SLASHEQ, "/="},
    {TK_PERCENTEQ, "%="},
    {TK_IF, "if"},
    {TK_ELSE, "else"},
    {TK_QUESTION, "?"},
    {TK_COLON, ":"},
    {TK_GOTO, "goto"},
    {TK_DO, "do"},
    {TK_WHILE, "while"},
    {TK_FOR, "for"},
    {TK_BREAK, "break"},
    {TK_CONTINUE, "continue"},
    {TK_SWITCH, "switch"},
    {TK_CASE, "case"},
    {TK_DEFAULT, "default"},
    {TK_COMMA, ","},
    {TK_STATIC, "static"},
    {TK_EXTERN, "extern"},
};

#define NUM_KEYWORDS (sizeof(KEYWORD_MATCHES) / sizeof(KEYWORD_MATCHES[0]))

// Comparator func for qsort.
// Used to sort KEYWORD_MATCHES by descending lengths.
static int longer_keyword_match(const void* a, const void* b) {
  const KeywordMatch* lhs = a;
  const KeywordMatch* rhs = b;

  // If either have match == NULL, then that one is smaller.
  if (!lhs->match) return 1;
  if (!rhs->match) return -1;

  int lhs_len = strlen(lhs->match);
  int rhs_len = strlen(rhs->match);

  if (lhs_len > rhs_len) return -1;
  if (lhs_len < rhs_len) return 1;
  return 0;
}

static inline void sort_keywords(void) {
  qsort(KEYWORD_MATCHES, NUM_KEYWORDS, sizeof(KEYWORD_MATCHES[0]),
        longer_keyword_match);
}

static inline bool is_whitespace(char c) {
  switch (c) {
    case ' ':
    case '\t':
    case '\r':
    case '\n':
    case '\v':
    case '\f':
      return true;
    default:
      return false;
  }
}

static inline bool is_newline(char c) { return c == '\n'; }

static inline bool is_num(char c) { return c >= '0' && c <= '9'; }

static inline bool is_ident_char(char c) {
  if (c >= 'a' && c <= 'z') return true;
  if (c >= 'A' && c <= 'Z') return true;
  if (is_num(c)) return true;
  if (c == '_') return true;
  return false;
}

static size_t find_next_whitespace(const FilePos* pos) {
  size_t n = 0;
  while (!file_pos_is_eof(pos)) {
    if (is_whitespace(file_pos_peek_char_at(pos, n))) {
      break;
    }
    n++;
  }

  return n;
}

static void advance_position_by_token(FilePos* pos, const Token* t) {
  size_t tok_len = string_len(t->content);
  pos->idx += tok_len;
  pos->col += tok_len;
}

//
// Matching functions
//

// Matches the input against the longest keyword possible.
// This assumes that |KEYWORD_MATCHES| is sorted by length.
// Returns false if failed. On failure, |out_token| is unmodified.
// If successful, |out_token| contains the matched token.
static bool match_keyword(const FilePos* pos, Token* out_token) {
  const char* curr = string_at(pos->contents, pos->idx);
  for (size_t i = 0; i < NUM_KEYWORDS; i++) {
    if (!string_begins2(curr, KEYWORD_MATCHES[i].match)) {
      continue;
    }

    // HACK: I check whether the keyword could be part of a larger ident
    // by only checking if the first character of the keyword is a valid
    // ident char. I don't think any keywords mix ident chars with non
    // ident chars, but this could bite me in the future.
    if (is_ident_char(KEYWORD_MATCHES[i].match[0])) {
      // check character in curr after the keyword match to see if
      // it's actually part of a larger ident.
      size_t next_idx = strlen(KEYWORD_MATCHES[i].match);
      if (file_pos_remaining(pos) > next_idx &&
          is_ident_char(file_pos_peek_char_at(pos, next_idx))) {
        return false;
      }
    }

    out_token->ty = KEYWORD_MATCHES[i].ty;
    out_token->content = string_from(KEYWORD_MATCHES[i].match);
    out_token->pos = *pos;
    return true;
  }
  return false;
}

// Matches a token the longest substring of |is_ident_char| characters.
// Explicitly checks that the first character is NOT a number to avoid
// accidentally matching numeric constants.
static bool match_ident(const FilePos* pos, Token* out_token) {
  assert(out_token && pos);
  if (is_num(file_pos_peek_char(pos))) {
    return 0;
  }

  size_t n = 0;
  while (!file_pos_is_eof(pos) &&
         is_ident_char(file_pos_peek_char_at(pos, n))) {
    n++;
  }

  if (!n) {
    return false;
  }

  // At input[n] is the first non-ident char
  out_token->ty = TK_IDENT;
  out_token->pos = *pos;
  out_token->content = string_substring(pos->contents, pos->idx, n);
  return true;
}

static bool match_num_constant(const FilePos* pos, Token* out_token) {
  // Advance until no longer a number.
  size_t n = 0;
  while (!file_pos_is_eof(pos) && is_num(file_pos_peek_char_at(pos, n))) {
    n++;
  }

  if (!n) {
    return false;
  }

  // Determine the out token type based on the suffx.
  // An integral suffix (for now) is only one character. Eventually, we'll need
  // to handle suffixes with multiple characters, like UL.
  TokenType out_ty = TK_INT_CONST;

  String* suffix = string_new();
  char next_char;
  while ((next_char = tolower(file_pos_peek_char_at(pos, n)))) {
    if (next_char == 'l' || next_char == 'u') {
      string_append(suffix, next_char);
      n++;
      continue;
    }
    break;
  }

  if (string_len(suffix) == 0) {
    out_ty = TK_INT_CONST;
  } else if (string_eq2(suffix, "l")) {
    out_ty = TK_LONG_CONST;
  } else if (string_eq2(suffix, "u")) {
    out_ty = TK_UINT_CONST;
  } else if (string_eq2(suffix, "lu") || string_eq2(suffix, "ul")) {
    out_ty = TK_ULONG_CONST;
  } else {
    emit_error(pos, "Invalid numeric literal suffix");
    return false;
  }

  // TODO: we have to check that the number ends at a word boundary.
  // Currently we check this by looking at the next character and seeing if it's
  // part of some malformed ident, but is this the right way to check?
  if (is_ident_char(next_char)) {
    return false;
  }

  out_token->ty = out_ty;
  out_token->pos = *pos;

  // Note: content will contain the suffix if it exists.
  out_token->content = string_substring(pos->contents, pos->idx, n);
  return true;
}

Vec* lex(const String* input) {
  sort_keywords();

  FilePos pos = {.contents = input, .idx = 0, .line = 0, .col = 0};
  Vec* out = vec_new(sizeof(Token));
  bool error = false;

  while (!file_pos_is_eof(&pos)) {
    char c = file_pos_peek_char(&pos);
    if (is_newline(c)) {
      pos.line++;
      pos.col = 0;
      pos.idx++;
      continue;
    }

    if (is_whitespace(c)) {
      pos.idx++;
      pos.col++;
      continue;
    }

    Token t = {};

    if (match_keyword(&pos, &t) || match_num_constant(&pos, &t) ||
        match_ident(&pos, &t)) {
      vec_push(out, &t);
      advance_position_by_token(&pos, &t);
      continue;
    }

    // emit error -- should be unreachable
    error = true;
    emit_error(&pos, "Unrecognized token");

    // Continue lexing at start of next whitespace to emit all errors at this
    // stage at once.
    size_t n = find_next_whitespace(&pos);
    pos.idx += n;
    pos.col += n;
  }

  // for (size_t i = 0; i < out->len; i++) {
  //   Token* t = vec_get(out, i);
  //   printf("%s\n", cstring(t->content));
  // }
  return error ? NULL : out;
}
