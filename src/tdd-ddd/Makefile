CC = gcc
CFLAGS = -Wall -I../../cudd-2.4.1/include
AR = ar -rcs
OBJS = tdd-ddd.o
LIB = libtdd-ddd.a

all : $(LIB)

$(LIB) : $(OBJS)
	$(AR) $@ $(OBJS)

%.d : %.c
	$(CC) -MM $(CFLAGS) -c -o $@ $<

%.o : %.c %.d
	$(CC) $(CFLAGS) -c -o $@ $<

-include tdd-ddd.d

clean :
	rm -f $(LIB) $(OBJS) *.d
