CC = gcc
CFLAGS = -Wall -I../../../cudd-2.4.1/cudd \
	 -I../../../cudd-2.4.1/mtr \
	 -I../../../cudd-2.4.1/epd

all : tdd-ddd.o

%.d : %.c
	$(CC) -MM $(CFLAGS) -c -o $@ $<

%.o : %.c %.d
	$(CC) $(CFLAGS) -c -o $@ $<

-include tdd-ddd.d

clean :
	rm -f *.o *.d
