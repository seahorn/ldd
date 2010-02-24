ROOT=../..
include $(ROOT)/src/Makefile.common

BINS = test1 test1b test2 test3 test_box_widen test_term_replace \
       cuddDvoMtrBug cuddMtrBug
OBJS = test1.o test1b.o test2.o test3.o test_box_widen.o test_term_replace.o \
       cuddDvoMtrBug.o cuddMtrBug.o
DEPS = $(patsubst %.o,%.d,$(OBJS))
TESTLIBS = $(CUDD)/cudd/libcudd.a $(CUDD)/st/libst.a \
	   $(CUDD)/util/libutil.a $(CUDD)/mtr/libmtr.a \
	   $(CUDD)/epd/libepd.a $(CUDD)/dddmp/libdddmp.a \
	   $(ROOT)/src/tdd/libtdd.a  \
	   $(ROOT)/src/tvpi/libtvpi.a

.PHONY: all
.PHONY: clean


all : $(BINS) 

$(BINS) : $(TESTLIBS)

%.d : %.c
	$(CC) -MM $(CFLAGS) -c -o $@ $<

%.o : %.c %.d
	$(CC) $(CFLAGS) -c -o $@ $<

-include $(DEPS)

clean:
	rm -f  $(OBJS) $(BINS) $(DEPS) *~

