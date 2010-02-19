CC = gcc
ICFLAGS = -g -Wall -O6 
XCFLAGS = -mtune=pentium4 -DHAVE_IEEE_754 -DBSD
CFLAGS = $(ICFLAGS) $(MFLAG) $(XCFLAGS) $(INCLUDE)
INCLUDE = -I$(CUDD)/include -I../include

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
