CC = gcc
CFLAGS = -Wall -I../../cudd-2.4.1/include -g -mtune=pentium4 -malign-double -DHAVE_IEEE_754 -DBSD
AR = ar -rcs 
OBJS = tdd-tvpi.o
DEPS = $(patsubst %.o,%.d,$(OBJS))
LIB = libtdd-tvpi.a

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
