CC = gcc
CUDD = ../../cudd-2.4.1
CFLAGS = -Wall -I$(CUDD)/include -I../include -g  -mtune=pentium4 -malign-double -DHAVE_IEEE_754 -DBSD
LDFLAGS = -L$(CUDD)/cudd  -L../tdd -L../tdd-ddd -L$(CUDD)/st -L$(CUDD)/util -L$(CUDD)/mtr -L$(CUDD)/epd -L$(CUDD)/dddmp
LDLIBS = -lcudd -ltdd-ddd -ltdd -lst -lutil -lmtr -lepd -ldddmp -lm
AR = ar -rcs
BINS = test1
OBJS = test1.o
DEPS = $(patsubst %.o,%.d,$(OBJS))

all : $(BINS) 


%.d : %.c
	$(CC) -MM $(CFLAGS) -c -o $@ $<

%.o : %.c %.d
	$(CC) $(CFLAGS) -c -o $@ $<

-include $(DEPS)

clean :
	rm -f  $(OBJS) $(DEPS) $(BINS)
