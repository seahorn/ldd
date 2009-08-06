CUDD = ../../cudd-2.4.1
CPPFLAGS = -Wall -I$(CUDD)/include -I../include -g  -mtune=pentium4 -DHAVE_IEEE_754 -DBSD
LDFLAGS = -L$(CUDD)/cudd -L$(CUDD)/st -L$(CUDD)/util -L$(CUDD)/mtr -L$(CUDD)/epd -L$(CUDD)/dddmp \
	  -L../tdd -L../tdd-ddd -L../tdd-oct 
LDLIBS = -lcudd -ltdd-ddd -ltdd-oct -ltdd -lst -lutil -lmtr -lepd -ldddmp -lgmp -lm
BINS = diamond smt_qelim_solver
OBJS = 
DEPS = $(patsubst %.o,%.d,$(OBJS))
TESTLIBS = $(CUDD)/cudd/libcudd.a $(CUDD)/st/libst.a \
	   $(CUDD)/util/libutil.a $(CUDD)/mtr/libmtr.a \
	   $(CUDD)/epd/libepd.a $(CUDD)/dddmp/libdddmp.a \
	   ../smtlib-parser/libsmtlib-parser.a \
	   ../tdd/libtdd.a ../tdd-ddd/libtdd-ddd.a \
	   ../tdd-oct/libtdd-oct.a ../tdd-tvpi/libtdd-tvpi.a

all : $(BINS) 

$(BINS) : $(TESTLIBS)

#%.d : %.c
#	$(CC) -MM $(CFLAGS) -c -o $@ $<

#%.o : %.c %.d
#	$(CC) $(CFLAGS) -c -o $@ $<

#-include $(DEPS)

clean :
	rm -f $(OBJS) $(DEPS) $(BINS)
