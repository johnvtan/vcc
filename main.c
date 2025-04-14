#include <assert.h>
#include <getopt.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <vcc/ast.h>
#include <vcc/emit_x64.h>
#include <vcc/gen_x64.h>
#include <vcc/ir.h>
#include <vcc/lex.h>
#include <vcc/string.h>
#include <vcc/typecheck.h>

static const struct option long_options[] = {
    {"lex", optional_argument, NULL, 'l'},
    {"parse", optional_argument, NULL, 'p'},
    {"validate", optional_argument, NULL, 'v'},
    {"tacky", optional_argument, NULL, 't'},
    {"codegen", optional_argument, NULL, 'c'},
    {0},
};

typedef struct {
  enum { LEX, PARSE, VALIDATE, TACKY, CODEGEN, EMIT } stage;
  char* input;
  char* output;
} CompilerArgs;

void usage(void) {
  printf(
      "vcc [--lex/--parse/--validate/--tacky/--codegen/...flags] <input> "
      "<output>\n");
  exit(-1);
}

CompilerArgs parse_args(int argc, char** argv) {
  // By default emit code
  CompilerArgs args = {.stage = EMIT};

  // Note: options will override each other, so the last one wins.
  char ch;
  while ((ch = getopt_long(argc, argv, "l:p:c:t:v:", long_options, NULL)) !=
         -1) {
    switch (ch) {
      case 'l':
        args.stage = LEX;
        continue;
      case 'p':
        args.stage = PARSE;
        continue;
      case 'v':
        args.stage = VALIDATE;
        continue;
      case 't':
        args.stage = TACKY;
        continue;
      case 'c':
        args.stage = CODEGEN;
        continue;
      default:
        break;
    }
  }

  // Then handle the positional filenames.
  if (argv[optind] == NULL || argv[optind + 1] == NULL) {
    usage();
  }

  args.input = argv[optind++];
  args.output = argv[optind];
  return args;
}

int main(int argc, char** argv) {
  CompilerArgs args = parse_args(argc, argv);

  FILE* input_fp = fopen(args.input, "r");
  assert(input_fp);

  String* input = string_from_file(input_fp);

  Vec* tokens = lex(input);
  if (!tokens) {
    return -1;
  }
  if (args.stage == LEX) {
    return 0;
  }

  AstProgram* prog = parse_ast(tokens);
  if (!prog) {
    return -1;
  }
  if (args.stage == PARSE) {
    return 0;
  }

  SymbolTable* symbol_table = typecheck_ast(prog);
  if (args.stage == VALIDATE) {
    return 0;
  }

  IrProgram* ir_prog = gen_ir(prog, symbol_table);
  if (!ir_prog) {
    return -1;
  }
  if (args.stage == TACKY) {
    return 0;
  }

  x64_Program* x64_prog = generate_x86(ir_prog);
  if (!x64_prog) {
    return -1;
  }

  if (args.stage == CODEGEN) {
    return 0;
  }

  return emit_x64(x64_prog, args.output);
}
