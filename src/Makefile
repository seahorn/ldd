# all compile options are in Makefile.common
DIRS	= tvpi tdd test bench-runner

#------------------------------------------------------------------------

.PHONY : build
.PHONY : all
.PHONY : clean
.PHONY : distclean


build:
	sh ./setup.sh
	@for dir in $(DIRS); do \
		(cd $$dir; \
		echo Making $$dir ...; \
		make )\
	done
all:
	sh ./setup.sh
	@for dir in $(DIRS); do \
		(cd $$dir; \
		echo Making all in $$dir ...; \
		make all )\
	done

clean:
	@for dir in $(DIRS); do	\
	    (cd $$dir; 	\
	     echo Cleaning $$dir ...; \
	     make clean ) \
	done

distclean:
	@for dir in $(DIRS) ; do	\
	    (cd $$dir; 	\
	     echo Cleaning $$dir ...; \
	     make distclean	) \
	done
	sh ./shutdown.sh
