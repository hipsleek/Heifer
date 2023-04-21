#!/usr/bin/env python

import sys
first = True
a = ''
for l in sys.stdin:
  if first:
    a = l.rstrip()
  else:
    if 'true' in a and 'true' not in l:
      print(a)
      print(l)
    elif 'true' in a and 'true' not in l:
      print(a)
      print(l)
  first = not first
  
