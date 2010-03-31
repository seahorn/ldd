ROOT=../..
include $(ROOT)/src/Makefile.common

OBJS = lddInit.o lddIte.o lddVars.o tdd_debug.o  lddNodeset.o lddExport.o lddPrint.o  lddCof.o lddQelimFM.o lddQelimPAT.o lddQelim.o lddQelimInf.o lddQelimBdd.o lddAPI.o tdd_reduce.o tdd_widen.o
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
