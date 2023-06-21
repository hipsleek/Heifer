#!/usr/bin/env python

import sys

first = True
fn = ''
yet_failed = False
for l in sys.stdin:
  l = l.rstrip()

  if 'error' in l:
    yet_failed = True
    print(l)
    break

  if first:
    fn = l
  else:
    if "===" in l:
      # the previous test passed
      # print(fn, 'trivial')
      fn = l.rstrip()
      continue

    # fail if we:
    # assert false and get true,
    # assert true and get false
    # do not assert and get false
    should_fail = ('false' in fn and 'true' in l) or ('false' not in fn and 'true' not in l)

    if should_fail:
      if not yet_failed:
        print('TESTS FAILED')
        yet_failed = True
      print(fn)
    # else:
    #   print(fn, 'passed')
  first = not first

if not yet_failed:
  print('ALL OK!')