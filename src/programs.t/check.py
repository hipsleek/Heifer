#!/usr/bin/env python

import sys
first = True
a = ''
failed = False
for l in sys.stdin:
  if first:
    a = l.rstrip()
  else:
    if ('true' in a and 'true' not in l) or ('false' in a and 'false' not in l):
      if not failed:
        print('TESTS FAILED')
        failed = True
      print(a)
  first = not first

if not failed:
  print('ALL OK!')