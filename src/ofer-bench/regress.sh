#!/bin/sh

# limit to 512MB memory
ulimit -v 512000

# 4s
time ./jobsolve -e 1 -m 20 -r 0 tests/ta01.txt

time ./jobsolve -e 1 -m 20 -r 0 tests/ta81.txt

time ./jobsolve -e 1 -m 20 -r 0 tests/ta93.txt


time ./jobsolve -e 1 -m 10 -r 0 tests/ofer2.txt
time ./jobsolve -e 2 -m 10 -r 0 tests/ofer2.txt
time ./jobsolve -e 3 -m 10 -r 0 tests/ofer2.txt
time ./jobsolve -e 4 -m 10 -r 0 tests/ofer2.txt
time ./jobsolve -e 5 -m 10 -r 0 tests/ofer2.txt



time ./jobsolve -e 1 -m 11 -r 1 tests/ofer2.txt
time ./jobsolve -e 2 -m 11 -r 1 tests/ofer2.txt
time ./jobsolve -e 3 -m 11 -r 1 tests/ofer2.txt
time ./jobsolve -e 4 -m 11 -r 1 tests/ofer2.txt
time ./jobsolve -e 5 -m 11 -r 1 tests/ofer2.txt


time ./jobsolve -e 1 -m 116  -r 0 tests/ofer3.txt
time ./jobsolve -e 2 -m 116  -r 0 tests/ofer3.txt
time ./jobsolve -e 3 -m 116  -r 0 tests/ofer3.txt
time ./jobsolve -e 4 -m 116  -r 0 tests/ofer3.txt
time ./jobsolve -e 5 -m 116  -r 0 tests/ofer3.txt


time ./jobsolve -e 1 -m 117  -r 1 tests/ofer3.txt
time ./jobsolve -e 2 -m 117  -r 1 tests/ofer3.txt
time ./jobsolve -e 3 -m 117  -r 1 tests/ofer3.txt
time ./jobsolve -e 4 -m 117  -r 1 tests/ofer3.txt
time ./jobsolve -e 5 -m 117  -r 1 tests/ofer3.txt


time ./jobsolve -e 2 -m 443 -r 0 tests/ofer1.txt
time ./jobsolve -e 2 -m 444 -r 1 tests/ofer1.txt
time ./jobsolve -e 4 -m 443 -r 0 tests/ofer1.txt
time ./jobsolve -e 4 -m 444 -r 1 tests/ofer1.txt
time ./jobsolve -e 5 -m 443 -r 0 tests/ofer1.txt
time ./jobsolve -e 5 -m 444 -r 1 tests/ofer1.txt


# 10s 
time ./jobsolve -e 1 -m 443 -r2 -l3 tests/ofer1.txt
# -e3 fails completelly

# 10s
time ./jobsolve -e 1 -m 444 -r2 -l3  tests/ofer1.txt

time ./jobsolve -e 1 -m 250  -r0  tests/ofer1.txt

time ./jobsolve -e 1 -m 282  -r0  tests/ofer1.txt

time ./jobsolve -e 1 -m 283  -r0  tests/ofer1.txt


time ./jobsolve -e 2 -m 433 -r0   tests/ta81.txt 
time ./jobsolve -e 2 -m 434 -r1   tests/ta81.txt 
time ./jobsolve -e 4 -m 433 -r0   tests/ta81.txt 
time ./jobsolve -e 4 -m 434 -r1   tests/ta81.txt 
time ./jobsolve -e 5 -m 433 -r0   tests/ta81.txt 
time ./jobsolve -e 5 -m 434 -r1   tests/ta81.txt 


time ./jobsolve -e2 -m 458 -r0  tests/ta82.txt  
time ./jobsolve -e2 -m 459 -r1  tests/ta82.txt  
time ./jobsolve -e4 -m 458 -r0  tests/ta82.txt  
time ./jobsolve -e4 -m 459 -r1  tests/ta82.txt  
time ./jobsolve -e5 -m 458 -r0  tests/ta82.txt  
time ./jobsolve -e5 -m 459 -r1  tests/ta82.txt  


# 2m
#time ./jobsolve -e 1 -m 20 -r 0 tests/ta50.txt

# 1m
#time ./jobsolve -e 1 -m 290  -r0  tests/ofer1.txt
# 2m
#time ./jobsolve -e 1 -m 305  -r0 tests/ofer1.txt