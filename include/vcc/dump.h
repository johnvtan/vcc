#ifndef VCC_DUMP_H
#define VCC_DUMP_H

#include <vcc/ast.h>
#include <vcc/gen_x64.h>
#include <vcc/ir.h>
#include <vcc/typecheck.h>

void dump_ir(IrProgram* ir);
void dump_x64(x64_Program* prog);

#endif
