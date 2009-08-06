CUDD=../../cudd-2.4.1
CC = gcc
FLEX = flex
BISON = bison
CFLAGS = -Wall -I$(CUDD)/include -I../include -g  -mtune=pentium4 -DHAVE_IEEE_754 -DBSD
AR = ar -rcs
OBJS = smt_lexer.yy.o smt_parser.tab.o smt_formula.o
DEPS = $(patsubst %.o,%.d,$(OBJS))
LIB = libsmtlib-parser.a
LDLIBS =

all : test

$(LIB) : $(OBJS)
	$(AR) $@ $(OBJS)

test: smt_parser_test
	./smt_parser_test < queen3-1.smt

smt_parser_test: smt_parser_test.c $(LIB)
	$(CC) -o $@ $(OBJS) smt_parser_test.c $(LIB) $(LDLIBS)

smt_lexer.yy.c: smt_lexer.lex
	$(FLEX) -t $< > $@

smt_parser.tab.c: smt_parser.y
	$(BISON) -d -o $@ $< 

%.d : %.c
	$(CC) -MM $(CFLAGS) -c -o $@ $<

%.o : %.c %.d
	$(CC) $(CFLAGS) -c -o $@ $<

-include $(DEPS)

clean :
	rm -f $(LIB) $(OBJS) $(DEPS) smt_lexer.yy.c smt_parser.tab.[ch] *~ smt_parser_test
