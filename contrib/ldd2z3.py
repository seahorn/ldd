#!/usr/bin/python

###
### Converts SMT benchmarks for LDDSolver into benchmarks for Z3
###

import re
import sys
import os


def main ():
  predRe = re.compile (r"^:extrapreds \(\((P[0-9]+)\)\)")
  #varRe = re.compile (r"^[ ]+\((v[0-9])+ FOO\)")
  varRe = re.compile (r"^  \((v[0-9][^ ]*) FOO")
  boolVarRe = re.compile (r"^  \((B[^ ][^ ]*) FOO")

  print '(set-option set-param ELIM_QUANTIFIERS true)'
  sys.stdout.flush ()

  # skip first 5 lines
  sys.stdin.readline ()
  sys.stdin.readline ()
  sys.stdin.readline ()
  sys.stdin.readline ()
  sys.stdin.readline ()

  preds = []
  for line in iter (sys.stdin.readline, ""):
    m = predRe.match (line)
    if m:
      preds.append (m.group (1))
      continue

    if line.startswith (":formula"):
      print '(declare-preds ('
      for p in preds:
        print '(', p, ')'
      print '))'
      print '(simplify'
      continue
    
    m = varRe.match (line)
    if m:
      print '  (', m.group(1), 'Int)'
      continue
    
    m = boolVarRe.match (line)
    if m:
      print '  (', m.group(1), 'Bool)'
      continue


    sys.stdout.write (line)

  sys.stdout.flush ()

main ()
