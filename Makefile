DOXYGEN=doxygen

DIRS = cudd-2.4.2 src

.PHONY: all
.PHONY: clean
.PHONY: doc


all:
	@for dir in $(DIRS); do \
		(cd $$dir; \
		echo Making all in $$dir ...; \
		make )\
	done

clean:
	@for dir in $(DIRS); do	\
	    (cd $$dir; 	\
	     echo Cleaning $$dir ...; \
	     make clean ) \
	done

doc: 
	$(DOXYGEN) doc/Doxyfile
