CUDD = ../../cudd-2.4.1
AR = ar -rcs
CFLAGS = -Wall -I$(CUDD)/include -I../include -g  -mtune=pentium4 -malign-double -DHAVE_IEEE_754 -DBSD
CPPFLAGS = -Wall -I$(CUDD)/include -I../include -g  -mtune=pentium4 -malign-double -DHAVE_IEEE_754 -DBSD
LDFLAGS = -L$(CUDD)/cudd -L$(CUDD)/st -L$(CUDD)/util -L$(CUDD)/mtr -L$(CUDD)/epd -L$(CUDD)/dddmp \
	  -L../tdd -L../tdd-ddd -L../tdd-oct 
LDLIBS = -lcudd -ltdd-ddd -ltdd-oct -ltdd -lst -lutil -lmtr -lepd -ldddmp -lgmp -lm
BINS = diamond
OBJS = diamond.o smt_qelim_solver.o
DEPS = $(patsubst %.o,%.d,$(OBJS))
TESTLIBS = $(CUDD)/cudd/libcudd.a $(CUDD)/st/libst.a \
	   $(CUDD)/util/libutil.a $(CUDD)/mtr/libmtr.a \
	   $(CUDD)/epd/libepd.a $(CUDD)/dddmp/libdddmp.a \
	   libsmt-qelim-solver.a \
	   ../smtlib-parser/libsmtlib-parser.a \
	   ../tdd/libtdd.a ../tdd-ddd/libtdd-ddd.a \
	   ../tdd-oct/libtdd-oct.a ../tdd-tvpi/libtdd-tvpi.a

all : $(BINS) 

$(BINS) : $(TESTLIBS)

libsmt-qelim-solver.a : smt_qelim_solver.o
	$(AR) $@ $<

%.d : %.c
	$(CC) -MM $(CFLAGS) -c -o $@ $<

%.o : %.c %.d
	$(CC) $(CFLAGS) -c -o $@ $<

-include $(DEPS)

clean :
	rm -f libsmt-qelim-solver.a $(OBJS) $(DEPS) $(BINS)
