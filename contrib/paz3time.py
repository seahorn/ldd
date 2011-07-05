#!/usr/bin/python

import sys
import re

def processFile (f):
    time = ""
    timeRe = re.compile (r"^time:[^0-9]*([0-9]+\.[0-9]+) secs")
    
    for line in open (f + ".stdout", "r"):
        m = timeRe.match (line)
        if m:
            time = m.group (1)
    if len(time) == 0: 
        time = "65"

    print f + "," + time

def main ():
    print "Name,ZSolve"
    for f in sys.argv[1:]:
        processFile (f)
        

if __name__ == "__main__":
    main ()
