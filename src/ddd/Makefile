#
#    Cudd - DDD package
#---------------------------
.SUFFIXES: .o .c .u

CC	= gcc
RANLIB	= ranlib
PURE	=
# Define EXE as .exe for MS-DOS and derivatives.
EXE	=
#EXE	= .exe

ICFLAGS	= -g -O6
#XCFLAGS	= -DDD_STATS
CFLAGS	= $(ICFLAGS) $(XCFLAGS)
#DDDEBUG = -DDD_DEBUG -DDD_VERBOSE -DDD_STATS -DDD_CACHE_PROFILE -DDD_UNIQUE_PROFILE -DDD_COUNT


# Include directories
CUDDDIR = ../../cudd-2.4.1
DDDDIR	= ..
CUDDIDIR = $(CUDDDIR)/include
MVDDIDIR = $(DDDDIR)/include
INCLUDEDIRS =   $(addprefix -I,$(CUDDIDIR)) \
		$(addprefix -I,$(DDDDIDIR))

LIBS	= \
	$(CUDDDIR)/dddmp/libdddmp.a \
	$(CUDDDIR)/cudd/libcudd.a \
	$(CUDDDIR)/mtr/libmtr.a \
	$(CUDDDIR)/st/libst.a \
	$(CUDDDIR)/util/libutil.a \
	$(CUDDDIR)/epd/libepd.a \
	./libdddcudd.a 


BLIBS	= -kL. -klmvlcudd -kL$(CUDDDIR)/mtr -klmtr \
	-kL$(CUDDDIR)/st -klst -kL$(CUDDDIR)/util -klutil

LDFLAGS	=

# files for the package
P	= dddcudd
PSRC	= matrix.c dddAbs.c dddIte.c dddOps.c dddInit.c

PHDR    = dddCudd.h dddCuddInt.h
POBJ	= $(PSRC:.c=.o)
PUBJ	= $(PSRC:.c=.u)

#------------------------------------------------------


lib$(P).a: $(POBJ)
	ar rv $@ $?
	$(RANLIB) $@

.c.o: $(PSRC) $(PHDR)
	$(CC) -c  $< $(INCLUDEDIRS) $(CFLAGS) $(DDDEBUG) 

lib$(P).b: $(PUBJ)
	ar rv $@ $?
	$(RANLIB) $@

.c.u: $(PSRC) $(PHDR)
	cc -j $< $(INCLUDEDIRS) $(XCFLAGS)

# if the header files change, recompile
$(POBJ): $(PHDR)
$(PUBJ): $(PHDR)
$(OBJ): $(PHDR)
$(UBJ): $(PHDR)


testDDD: $(SRC) $(OBJ) $(HDR) $(LIBS) $(MNEMLIB) testDDD.o
	$(PURE) $(CC) $(CFLAGS) $(LDFLAGS) -o $@ testDDD.o $(OBJ) $(LIBS) $(MNEMLIB) -lm

tags: $(PSRC) $(PHDR)
	ctags $(PSRC) $(PHDR)

all: lib$(P).a lib$(P).b tags

clean:
	rm -f *.o *.u mon.out gmon.out *.pixie *.Addrs *.Counts mnem.* \
	.pure core *.warnings

distclean: clean
	rm -f $(TARGET) $(TARGETu) lib*.a lib$(P).b \
	*.bak *~ tags .gdb_history *.qv *.qx
