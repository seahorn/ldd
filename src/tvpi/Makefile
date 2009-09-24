CC = gcc
CFLAGS = -Wall -I../../cudd-2.4.1/include -I../include -O6 -g -mtune=pentium4 -DHAVE_IEEE_754 -DBSD
AR = ar -rcs 
OBJS = tvpi.o
DEPS = $(patsubst %.o,%.d,$(OBJS))
LIB = libtvpi.a

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
