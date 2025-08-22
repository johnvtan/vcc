#include <assert.h>
#include <stdio.h>
#include <vcc/lex.h>
#include <vcc/string.h>

#define R(...) #__VA_ARGS__

void lex_test(void) {
  {
    Vec* tokens = lex(string_from("double"));
    assert(tokens);
    assert(tokens->len == 1);

    Token* double_tk = vec_get(tokens, 0);
    assert(double_tk->ty != TK_IDENT);
  }

  {
    Vec* tokens = lex(string_from("3.0"));
    assert(tokens);
  }

  {
    Vec* tokens = lex(string_from("-3.0234"));
    assert(tokens);
  }
}

int main(void) {
  lex_test();
  //   const char* prog = R(int main(void) {
  //     \n double x = 3.0;
  //     \n return 0;
  //     \n
  //   });
  //
  //   String* input = string_from(prog);
  //   Vec* tokens = lex(input);
  //   assert(tokens);

  printf("Ch 13 pass\n");
  return 0;
}
