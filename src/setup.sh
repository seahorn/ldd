#!/bin/sh
[ -d include ] || mkdir include
cd include
ln -sf ../tdd/ldd.h .
ln -sf ../tdd/lddInt.h .
ln -sf ../tvpi/tvpi.h .
cd -
