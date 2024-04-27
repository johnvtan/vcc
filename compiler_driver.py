#!/usr/bin/python3
import argparse
from subprocess import run
import tempfile

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--lex", help="Run up to lexer", action="store_true")
    parser.add_argument("--parse", help="Run up to parser", action="store_true")
    parser.add_argument("--codegen", help="Run up to codegen", action="store_true")
    parser.add_argument("input_file", help="File to compiler")

    args = parser.parse_args()
    print(args.input_file)

    basename, ext = args.input_file.split('.')
    if ext != 'c':
        print('Must be a .c file')
        exit(1)

    # create tempfile for preprocess input
    pp_file = tempfile.NamedTemporaryFile()
    run(f'gcc -E -P {args.input_file} -o {pp_file.name}', check=True, shell=True)

    asm_file = tempfile.NamedTemporaryFile()

    # TODO: there's gotta be a better way
    vcc_cli_arg = ""
    emit = False 
    if args.lex: vcc_cli_arg = "--lex"
    elif args.parse: vcc_cli_arg = "--parse"
    elif args.codegen: vcc_cli_arg = "--codegen"
    else: emit = True

    run(f'./bin/vcc {vcc_cli_arg} {pp_file.name} {asm_file.name}', check=True, shell=True)

    if emit:
        run(f'gcc {asm_file.name} -o {basename}', check=True, shell=True)