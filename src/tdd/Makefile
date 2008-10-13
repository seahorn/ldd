CUDD=../../cudd-2.4.1
CC = gcc
CFLAGS = -Wall -I$(CUDD)/include -g  -mtune=pentium4 -malign-double -DHAVE_IEEE_754 -DBSD
AR = ar -rcs
OBJS = tdd_init.o tdd_ite.o tdd_vars.o tdd_abs.o
LIB = libtdd.a

all : $(LIB)

$(LIB) : $(OBJS)
	$(AR) $@ $(OBJS)

%.d : %.c
	$(CC) -MM $(CFLAGS) -c -o $@ $<

%.o : %.c %.d
	$(CC) $(CFLAGS) -c -o $@ $<

#-include tdd-ddd.d

clean :
	rm -f $(LIB) $(OBJS) *.d
