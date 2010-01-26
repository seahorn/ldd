CC = gcc
CUDD = ../../cudd-2.4.1
CFLAGS = -Wall -I$(CUDD)/include -I../include -g  -mtune=pentium4 -DHAVE_IEEE_754 -DBSD
LDFLAGS = -L$(CUDD)/cudd -L$(CUDD)/st -L$(CUDD)/util -L$(CUDD)/mtr -L$(CUDD)/epd -L$(CUDD)/dddmp \
	  -L../tdd -L../box -L../tvpi
LDLIBS = -lcudd  -ltvpi -lbox -ltdd -lst -lutil -lmtr -lepd -ldddmp -lgmp -lm
BINS = test1 test1b test2 test3 test_box_widen test_term_replace
OBJS = test1.o test1b.o test2.o test3.o test_box_widen.o test_term_replace.o
DEPS = $(patsubst %.o,%.d,$(OBJS))
TESTLIBS = $(CUDD)/cudd/libcudd.a $(CUDD)/st/libst.a \
	   $(CUDD)/util/libutil.a $(CUDD)/mtr/libmtr.a \
	   $(CUDD)/epd/libepd.a $(CUDD)/dddmp/libdddmp.a \
	   ../tdd/libtdd.a  \
	   ../box/libbox.a ../tvpi/libtvpi.a

all : $(BINS) 

$(BINS) : $(TESTLIBS)

%.d : %.c
	$(CC) -MM $(CFLAGS) -c -o $@ $<

%.o : %.c %.d
	$(CC) $(CFLAGS) -c -o $@ $<

-include $(DEPS)

clean:
	rm -f  $(OBJS) $(DEPS) $(BINS)
