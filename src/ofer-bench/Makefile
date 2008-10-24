CUDD=../../cudd-2.4.1
CC = gcc
FLEX = flex
BISON = bison
CFLAGS = -pg -Wall -I$(CUDD)/include -I../include  -g  -mtune=pentium4 -malign-double -DHAVE_IEEE_754 -DBSD -O2
AR = ar -rcs
OBJS = lexer.yy.o parser.tab.o qelim1.o qelim2.o
DEPS = $(patsubst %.o,%.d,$(OBJS))
LIB = libtdd.a
LDFLAGS = -L$(CUDD)/cudd -L$(CUDD)/st -L$(CUDD)/util -L$(CUDD)/mtr -L$(CUDD)/epd -L$(CUDD)/dddmp \
	  -L../tdd -L../tdd-ddd -L../tdd-oct -pg
LDLIBS = -lcudd -ltdd-ddd -ltdd-oct -ltdd -lst -lutil -lmtr -lepd -ldddmp -lm -lfl
BINS = jobshop qelim1 qelim2

all : $(BINS)


qelim2: qelim2.o parser.tab.o lexer.yy.o
	$(CC) $(LDFLAGS) -o $@  $^ $(LDLIBS)

qelim1: qelim1.o parser.tab.o lexer.yy.o
	$(CC) $(LDFLAGS) -o $@  $^ $(LDLIBS)

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
	rm -f $(LIB) $(OBJS) $(DEPS) lexer.yy.c parser.tab.[ch] *~ $(BINS)
