CC := clang
CFLAGS := -Wall -Wextra
LD := clang
LDFLAGs :=

INCDIR := include
TESTDIR := unit
OBJDIR := obj
BINDIR := bin

COMPILER_SRCS := ast.c \
				ctype.c\
				dump.c \
			  emit_x64.c \
				errors.c \
				file_pos.c \
				gen_x64.c \
				hashmap.c \
				ir.c \
				lex.c \
				string.c \
				typecheck.c \
				vec.c

COMPILER_OBJS := $(patsubst %.c, $(OBJDIR)/%.o, $(COMPILER_SRCS))

SRCS := $(COMPILER_SRCS) main.c
OBJS := $(COMPILER_OBJS) $(OBJDIR)/main.o

TESTSRCS := $(wildcard $(TESTDIR)/*_test.c)
TESTS ?= $(patsubst $(TESTDIR)/%_test.c, %_test, $(TESTSRCS))

TESTBINS := $(patsubst %, $(BINDIR)/%, $(TESTS))

TARGET := vcc

all: $(TARGET)

$(TARGET): dirs $(BINDIR)/$(TARGET)

# run unit tests
unit: dirs $(TESTS)

debug: CFLAGS += -g -DDUMP_AST
debug: all

$(BINDIR)/$(TARGET): $(OBJS)
	$(LD) $(LDFLAGS) $(OBJS) -o $(BINDIR)/$(TARGET)

%_test: $(BINDIR)/%_test
	@echo "\n=========== Running test ==========="
	./$<
	@echo "====================================\n"

$(BINDIR)/%_test: $(TESTDIR)/%_test.c $(COMPILER_OBJS)
	$(CC) $(CFLAGS) -I $(INCDIR) -c $< -o $(OBJDIR)/$*_test.o
	$(LD) $(LDFLAGS) $(COMPILER_OBJS) $(OBJDIR)/$*_test.o -o $@

$(OBJDIR)/%.o: %.c
	$(CC) $(CFLAGS) -I$(INCDIR) -c $< -o $@

dirs:
	@mkdir -p $(OBJDIR) $(BINDIR)

clean:
	rm -rf $(OBJDIR) $(BINDIR)
	cd testing/ && git clean -fd && cd ..

format:
	clang-format --style Google -i $(SRCS) $(INCDIR)/vcc/*.h $(TESTSRCS)

# lol does this work
bear: clean
	@bear -- make

.phony: clean %_test format
