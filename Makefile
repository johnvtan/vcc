CC := clang
CFLAGS := -Wall -Wextra
LD := clang
LDFLAGs :=

INCDIR := include
TESTDIR := unit
OBJDIR := obj
BINDIR := bin

SRCS := $(wildcard *.c)
TESTSRCS := $(wildcard $(TESTDIR)/*_test.c)
TESTS ?= $(patsubst $(TESTDIR)/%_test.c, %_test, $(TESTSRCS))

OBJS := $(patsubst %.c, $(OBJDIR)/%.o, $(SRCS))

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

$(BINDIR)/%_test: $(TESTDIR)/%_test.c %.c
	$(CC) $(CFLAGS) -I $(INCDIR) $^ -o $@

$(BINDIR)/string_test: $(TESTDIR)/string_test.c string.c vec.c
	$(CC) $(CFLAGS) -I $(INCDIR) $^ -o $@

$(BINDIR)/hashmap_test: $(TESTDIR)/hashmap_test.c string.c vec.c hashmap.c
	$(CC) $(CFLAGS) -I $(INCDIR) $^ -o $@

$(OBJDIR)/%.o: %.c
	$(CC) $(CFLAGS) -I$(INCDIR) -c $< -o $@

dirs:
	@mkdir -p $(OBJDIR) $(BINDIR)

clean:
	rm -rf $(OBJDIR) $(BINDIR)

format:
	clang-format --style Google -i $(SRCS) $(INCDIR)/vcc/*.h $(TESTSRCS)

# lol does this work
bear: clean
	@bear -- make

.phony: clean %_test format
