CUDD=../../cudd-2.4.1
CC = gcc
CFLAGS = -Wall -I$(CUDD)/include

all : tdd_init.o tdd_ite.o tdd_vars.o

%.d : %.c
	$(CC) -MM $(CFLAGS) -c -o $@ $<

%.o : %.c %.d
	$(CC) $(CFLAGS) -c -o $@ $<

#-include tdd-ddd.d

clean :
	rm -f *.o *.d
