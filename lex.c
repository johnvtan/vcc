#include <assert.h>
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
    {TK_INT, "int"},       {TK_VOID, "void"},     {TK_RETURN, "return"},
    {TK_OPEN_PAREN, "("},  {TK_CLOSE_PAREN, ")"}, {TK_OPEN_BRACE, "{"},
    {TK_CLOSE_BRACE, "}"}, {TK_SEMICOLON, ";"},
};

#define NUM_KEYWORDS (sizeof(KEYWORD_MATCHES) / sizeof(KEYWORD_MATCHES[0]))

// Comparator func for qsort.
// Used to sort KEYWORD_MATCHES by descending lengths.
static int longer_keyword_match(const void* a, const void* b) {
  const KeywordMatch* lhs = a;
  const KeywordMatch* rhs = b;

  // If either have match == NULL, then that one is smaller.
  if (!lhs->match) return -1;
  if (!rhs->match) return 1;

  int lhs_len = strlen(lhs->match);
  int rhs_len = strlen(rhs->match);

  if (lhs_len > rhs_len) return 1;
  if (lhs_len < rhs_len) return -1;
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

//
// Lexing context
// Note: this is exactly the same as ErrorContext right now, but I'll keep them
// separate in case they diverge.
//
typedef struct {
  const String* input;
  int idx;
  int line;
  int col;
} Context;

static bool has_more(const Context* cx) {
  return (size_t)cx->idx < string_len(cx->input);
}

// Peeks the input at |n| characters after the current |idx| in |cx|.
static inline char peek_char_at(const Context* cx, size_t n) {
  assert(has_more(cx));
  return string_get(cx->input, cx->idx + n);
}

static inline char peek_char(const Context* cx) { return peek_char_at(cx, 0); }

static size_t find_next_whitespace(const Context* cx) {
  size_t n = 0;
  while (has_more(cx)) {
    if (is_whitespace(peek_char_at(cx, n))) {
      break;
    }
    n++;
  }

  return n;
}

static void advance_context_by_token(Context* cx, const Token* t) {
  size_t tok_len = string_len(t->content);
  cx->idx += tok_len;
  cx->col += tok_len;
}

static ErrorContext to_err_cx(const Context* cx) {
  ErrorContext ret = {
      .input = cx->input, .idx = cx->idx, .col = cx->col, .line = cx->line};
  return ret;
}

//
// Matching functions
//

// Matches the input against the longest keyword possible.
// This assumes that |KEYWORD_MATCHES| is sorted by length.
// Returns false if failed. On failure, |out_token| is unmodified.
// If successful, |out_token| contains the matched token.
static bool match_keyword(const Context* cx, Token* out_token) {
  const char* curr = string_at(cx->input, cx->idx);
  for (size_t i = 0; i < NUM_KEYWORDS; i++) {
    if (string_begins2(curr, KEYWORD_MATCHES[i].match)) {
      out_token->ty = KEYWORD_MATCHES[i].ty;
      out_token->content = string_from(KEYWORD_MATCHES[i].match);
      out_token->err_cx = to_err_cx(cx);
      return true;
    }
  }
  return false;
}

// Matches a token the longest substring of |is_ident_char| characters.
// Explicitly checks that the first character is NOT a number to avoid
// accidentally matching numeric constants.
static bool match_ident(const Context* cx, Token* out_token) {
  assert(out_token && cx);
  if (is_num(peek_char(cx))) {
    return 0;
  }

  size_t n = 0;
  while (has_more(cx) && is_ident_char(peek_char_at(cx, n))) {
    n++;
  }

  if (!n) {
    return false;
  }

  // At input[n] is the first non-ident char
  out_token->ty = TK_IDENT;
  out_token->err_cx = to_err_cx(cx);
  out_token->content = string_substring(cx->input, cx->idx, n);
  return true;
}

static bool match_num_constant(const Context* cx, Token* out_token) {
  size_t n = 0;
  while (has_more(cx) && is_num(peek_char_at(cx, n))) {
    n++;
  }

  // TODO: we have to check that the number ends at a word boundary.
  // Currently we check this by looking at the next character and seeing if it's
  // part of some malformed ident, but is this the right way to check?
  if (!n || is_ident_char(peek_char_at(cx, n))) {
    return false;
  }

  out_token->ty = TK_NUM_CONST;
  out_token->err_cx = to_err_cx(cx);
  out_token->content = string_substring(cx->input, cx->idx, n);
  return true;
}

Vec* lex(const String* input) {
  sort_keywords();

  Context cx = {.input = input, .idx = 0, .line = 0, .col = 0};
  Vec* out = vec_new(sizeof(Token));
  bool error = false;

  while (has_more(&cx)) {
    char c = peek_char(&cx);
    if (is_newline(c)) {
      cx.line++;
      cx.col = 0;
      cx.idx++;
      continue;
    }

    if (is_whitespace(c)) {
      cx.idx++;
      cx.col++;
      continue;
    }

    Token t = {};

    if (match_keyword(&cx, &t) || match_num_constant(&cx, &t) ||
        match_ident(&cx, &t)) {
      vec_push(out, &t);
      advance_context_by_token(&cx, &t);
      continue;
    }

    // emit error -- should be unreachable
    error = true;
    emit_error(to_err_cx(&cx), "Unrecognized token");

    // Continue lexing at start of next whitespace to emit all errors at this
    // stage at once.
    size_t n = find_next_whitespace(&cx);
    cx.idx += n;
    cx.col += n;
  }

  // for (size_t i = 0; i < out->len; i++) {
  //   Token* t = vec_get(out, i);
  //   printf("%s\n", cstring(t->content));
  // }
  return error ? NULL : out;
}