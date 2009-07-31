CUDD=../../cudd-2.4.1
CC = gcc
CFLAGS = -Wall -I$(CUDD)/include -g  -mtune=pentium4 -malign-double -DHAVE_IEEE_754 -DBSD -pg -O2 
AR = ar -rcs
OBJS = tdd_init.o tdd_ite.o tdd_vars.o tdd_abs.o tdd_debug.o tdd_reduce.o tdd_bdd_abs.o tdd_mv_abs.o tdd_widen.o tdd_nodeset.o
DEPS = $(patsubst %.o,%.d,$(OBJS))
LIB = libtdd.a

all : $(LIB)

$(LIB) : $(OBJS)
	$(AR) $@ $(OBJS)

%.d : %.c
	$(CC) -MM $(CFLAGS) -c -o $@ $<

%.o : %.c %.d
	$(CC) $(CFLAGS) -c -o $@ $<

-include $(DEPS)

clean :
	rm -f $(LIB) $(OBJS) $(DEPS)
