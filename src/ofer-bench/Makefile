CUDD=../../cudd-2.4.1
CC = gcc
FLEX = flex
BISON = bison
CFLAGS = -Wall -I$(CUDD)/include -I../include  -g  -mtune=pentium4 -malign-double -DHAVE_IEEE_754 -DBSD
AR = ar -rcs
OBJS = lexer.yy.o parser.tab.o 
DEPS = $(patsubst %.o,%.d,$(OBJS))
LIB = libtdd.a
LDFLAGS = -L$(CUDD)/cudd -L$(CUDD)/st -L$(CUDD)/util -L$(CUDD)/mtr -L$(CUDD)/epd -L$(CUDD)/dddmp \
	  -L../tdd -L../tdd-ddd -L../tdd-oct 
LDLIBS = -lcudd -ltdd-ddd -ltdd-oct -ltdd -lst -lutil -lmtr -lepd -ldddmp -lm -lfl
BINS = parser jobshop 

all : $(BINS)


parser: $(OBJS) 
	$(CC) $(LDFLAGS) -o $@ $(OBJS) $(LDLIBS)

lexer.yy.c: lexer.lex 
	$(FLEX) -t $< > $@

parser.tab.c: parser.y
	$(BISON) -d -o $@ $< 

%.d : %.c
	$(CC) -MM $(CFLAGS) -c -o $@ $<

%.o : %.c %.d
	$(CC) $(CFLAGS) -c -o $@ $<

-include $(DEPS)

clean :
	rm -f $(LIB) $(OBJS) $(DEPS) lexer.yy.c parser.tab.[ch] *~ parser jobshop
