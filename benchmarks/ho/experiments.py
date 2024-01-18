#!/usr/bin/env python


import subprocess
import re

def run_one(file):
  # print(file)
  output = subprocess.run(['dune', 'exec', 'parsing/hip.exe', f'src/examples/{file}.ml'],
    capture_output=True, text=True).stdout

  loc = int(re.search(r'\[\s*LoC\s*\]\s*([0-9.]+)', output).group(1))
  los_ratio = re.search(r'\[\s*LoS\s*\]\s*([0-9.]+) \(([0-9.]+)\)', output)
  los = int(los_ratio.group(1))
  ratio = float(los_ratio.group(2))

  z3 = float(re.search(r'\[\s*Z3\s*\]\s*([0-9.]+) s', output).group(1))
  why3 = float(re.search(r'\[\s*Why3\s*\]\s*([0-9.]+) s', output).group(1))
  total = float(re.search(r'\[\s*Total\s*\]\s*([0-9.]+) s', output).group(1))

  return (loc, los, ratio, total, z3, why3)


if __name__ == "__main__":
  benchmarks = ['map', 'list', 'fold', 'length_pure', 'iter', 'compose', 'length', 'closure', 'nth', 'exception', 'applyN']
  # benchmarks = ['map', 'fold']
  bench = [(b,run_one(b)) for b in benchmarks]

  for (n, (loc, los, r, t, z, w)) in bench:
    print(f'{n} & {loc} & {los} & {r} & {t} & {z} & {w} & & & & \\\\')

