ROOT=../..

include $(ROOT)/src/Makefile.common
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
