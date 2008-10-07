CC = gcc
CFLAGS = -Wall -I../../../cudd-2.4.1/include

all : tdd-ddd.o

%.d : %.c
	$(CC) -MM $(CFLAGS) -c -o $@ $<

%.o : %.c %.d
	$(CC) $(CFLAGS) -c -o $@ $<

-include tdd-ddd.d

clean :
	rm -f *.o *.d
