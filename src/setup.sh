#!/bin/sh
[ -d include ] || mkdir include
cd include
ln -sf ../ldd/ldd.h .
ln -sf ../ldd/lddInt.h .
ln -sf ../tvpi/tvpi.h .
cd -
