#!/usr/bin/env python

# Usage: benchmarks/ho/experiments.py | pbcopy

import subprocess
import re
from dataclasses import dataclass
import os

import sys


def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)


@dataclass
class Test:
    file: str
    src: str = None

    # updated after test
    loc: int = None
    los: int = None
    ratio: float = None
    z3_time: float = None
    why3_time: float = None
    total_time: float = None

    def add(self, other):
        self.loc += other.loc
        self.los += other.los
        self.ratio = float(self.los) / float(self.loc)
        self.z3_time += other.z3_time
        self.why3_time += other.why3_time
        self.total_time += other.total_time


def count_loc(s):
    return len([l for l in s.split("\n") if l.strip()])


def count_lines_cameleer(fname):
    with open(fname, "r") as f:
        txt = f.read()

    # strip comments
    txt = re.sub(r"\(\*\s(?:.|\n)*?\*\)", "", txt)

    # eprint('WITHOUT COMMENTS', txt)

    # find spec comments, then strip them too
    spec_comment_regex = (
        r"\(\*@[^@]+\*\)"  # very slightly different from heifer, without ending @
    )
    spec_comments = re.findall(spec_comment_regex, txt)
    los = sum(count_loc(c) for c in spec_comments)
    txt = re.sub(spec_comment_regex, "", txt)

    loc = count_loc(txt)

    # eprint('SPEC COMMENTS')
    # for c in spec_comments:
    #   eprint(c)

    # eprint('WIHTOUT SPEC COMMENTS', txt)

    # import pdb; pdb.set_trace()

    return loc, los


def count_lines_heifer(fname):
    with open(fname, "r") as f:
        txt = f.read()

    # strip comments
    txt = re.sub(r"\(\*\s(?:.|\n)*?\*\)", "", txt)

    # eprint('WITHOUT COMMENTS', txt)

    # find spec comments, then strip them too
    spec_comment_regex = r"\(\*@[^@]+@\*\)"
    spec_comments = re.findall(spec_comment_regex, txt)
    los = sum(count_loc(c) for c in spec_comments)
    txt = re.sub(spec_comment_regex, "", txt)

    loc = count_loc(txt)

    # eprint('SPEC COMMENTS')
    # for c in spec_comments:
    #   eprint(c)

    # eprint('WIHTOUT SPEC COMMENTS', txt)

    # import pdb; pdb.set_trace()

    return loc, los


def run_heifer(test):
    # eprint(filename)
    output = subprocess.run(
        ["dune", "exec", "parsing/hip.exe", test.file], capture_output=True, text=True
    ).stdout
    # eprint(output)

    # these are wrong
    # test.loc = int(re.search(r'\[\s*LoC\s*\]\s*([0-9.]+)', output).group(1))
    # los_ratio = re.search(r'\[\s*LoS\s*\]\s*([0-9.]+) \(([0-9.]+)\)', output)
    # test.los = int(los_ratio.group(1))
    # test.ratio = float(los_ratio.group(2))

    loc, los = count_lines_heifer(test.file)
    test.loc = loc
    test.los = los
    test.ratio = float(los) / float(loc)

    test.z3_time = float(re.search(r"\[\s*Z3\s*\]\s*([0-9.]+) s", output).group(1))
    test.why3_time = float(re.search(r"\[\s*Why3\s*\]\s*([0-9.]+) s", output).group(1))
    test.total_time = float(
        re.search(r"\[\s*Total\s*\]\s*([0-9.]+) s", output).group(1)
    )


def run_cameleer(test):
    # file = f"{path}/{bench}/why3session.xml"
    file, _ = os.path.splitext(test.file)
    file += "/why3session.xml"

    with open(file, "r") as f:
        txt = f.read()

    m = re.findall(r"time=\"([0-9.]+)\"", txt)

    test.total_time = sum([float(t) for t in m])

    loc, los = count_lines_cameleer(test.file)
    # eprint(test.file)
    test.loc = loc
    test.los = los
    test.ratio = float(los) / float(loc)


if __name__ == "__main__":
    cameleer_path = os.path.expanduser("~/ocaml/cameleer")
    cameleer_benchmarks = {
        "map": Test(file=f"{cameleer_path}/map.ml"),
        "fold": Test(file=f"{cameleer_path}/examples/ocaml_fold.ml"),
        "applyN": Test(file=f"{cameleer_path}/applyN.ml"),
        "compose": Test(file=f"{cameleer_path}/compose.ml"),
        "length": Test(file=f"{cameleer_path}/length.ml"),
        # leaving these out
        # "exception": Test(file=f"{cameleer_path}/exception.ml"),
        # "map_list": Test(file=f"{cameleer_path}/map_list.ml"),
    }

    for k, v in cameleer_benchmarks.items():
        run_cameleer(v)

    heifer_benchmarks = {
        "map": Test(file="src/examples/map.ml", src="DBLP:journals/pacmpl/WolffBMMS21"),
        "fold": Test(
            file="src/examples/fold.ml", src="DBLP:journals/pacmpl/WolffBMMS21"
        ),
        "iter": Test(file="src/examples/iter.ml", src="DBLP:conf/tacas/DenisJ23"),
        "compose": Test(file="src/examples/compose.ml"),
        "length": Test(file="src/examples/length.ml"),
        "length_pure": Test(file="src/examples/length_pure.ml"),
        "closure": Test(file="src/examples/closure.ml", src="svendsen2013modular"),
        "applyN": Test(file="src/examples/applyN.ml"),
        "blameassgn": Test(
            file="src/prusti/blameassgn.ml", src="Findler2002ContractsFH"
        ),
        "counter": Test(file="src/prusti/counter.ml", src="Kassios2010SpecificationAV"),
        "lambda": Test(file="src/programs.t/test_lambda.ml"),
        # 'exception': Test(file='src/examples/exception.ml'),
    }

    for n, t in heifer_benchmarks.items():
        eprint(f"{n}")
        run_heifer(t)
    eprint()

    for n, t in heifer_benchmarks.items():
        eprint(
            f"""Benchmark: {n}
LoC: {t.loc}
LoS: {t.los}
Ratio: {t.ratio}
Total: {t.total_time}
Z3: {t.z3_time}
Why3: {t.why3_time}
"""
        )

    # merge some before generating table
    if "length" in heifer_benchmarks and "length_pure" in heifer_benchmarks:
        heifer_benchmarks["length"].add(heifer_benchmarks["length_pure"])
        del heifer_benchmarks["length_pure"]

    # compute some stats
    heifer_avg = float(sum([b.ratio for _, b in heifer_benchmarks.items()])) / float(
        len(heifer_benchmarks)
    )
    cameleer_avg = float(
        sum([b.ratio for _, b in cameleer_benchmarks.items()])
    ) / float(len(cameleer_benchmarks))
    heifer_total_loc = sum([b.loc for _, b in heifer_benchmarks.items()])
    heifer_total_los = sum([b.los for _, b in heifer_benchmarks.items()])
    cameleer_total_loc = sum([b.loc for _, b in cameleer_benchmarks.items()])
    cameleer_total_los = sum([b.los for _, b in cameleer_benchmarks.items()])

    eprint("heifer")
    eprint(f"average ratio: {heifer_avg:.2f}")
    eprint(f"total loc: {heifer_total_loc:.2f}")
    eprint(f"total los: {heifer_total_los:.2f}")
    eprint()

    eprint("cameleer")
    eprint(f"average ratio: {cameleer_avg:.2f}")
    eprint(f"total loc: {cameleer_total_loc:.2f}")
    eprint(f"total los: {cameleer_total_los:.2f}")
    eprint()

    print("% generated")
    for n, t in heifer_benchmarks.items():
        src = ""
        if t.src:
            src = rf"~\cite{{{t.src}}}"

        cameleer_cols = "- & - & - & -"
        if n in cameleer_benchmarks:
            b = cameleer_benchmarks[n]
            cameleer_cols = f"{b.loc} & {b.los} & {b.ratio:.2f} & {b.total_time:.2f}"

        print(
            f"{n}{src} & {t.loc} & {t.los} & {t.ratio:.2f} & {t.total_time:.2f} & {t.z3_time:.2f} & {t.why3_time:.2f} & {cameleer_cols} \\\\"
        )
    print("% end generated")
