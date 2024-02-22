#!/usr/bin/env python

# Usage: benchmarks/ho/experiments.py | pbcopy

ML_COMMENTS = r"\(\*\s(?:.|\n)*?\*\)"
RUST_COMMENTS = r"//[^\n]+"
RUST_COMMENTS = r"//[^\n]+"
CAMELEER_SPEC = r"\(\*@[^@]+\*\)"
HEIFER_SPEC = r"\(\*@[^@]+\*\)"

# we can't matched balanced parens without recursion.
# example: #[requires([
#            ...
#          ])]
#          ^
# the extra .* at the end consumes everything after the first ],
# so all that should be on the same line.
PRUSTI_SPEC = r"#\[(?:.|\n)*?\].*"

import subprocess
import re
from dataclasses import dataclass, field
import os

import sys


def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)


@dataclass
class Test:
    file: str = None
    src: str = None

    # manually-given list of properties to prove, should be comparable across verifiers
    properties: list[str] = field(default_factory=list)
    inexpressible: bool = False
    loc_but_actually_los: int = 0

    # updated after test
    lemmas: int = None  # total number of lemmas proved, may include aux. not comparable
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
        self.lemmas += other.lemmas
        self.properties = list(set(self.properties + other.properties))


def count_loc(s):
    return len([l for l in s.split("\n") if l.strip()])


def process_src_file(fname, comment_regex, spec_comment_regex):
    with open(fname, "r") as f:
        txt = f.read()

    # strip comments
    txt = re.sub(comment_regex, "", txt)

    # eprint('WITHOUT COMMENTS', txt)

    # find spec comments, then strip them too
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
    """
    Actualy run Heifer and collect stats
    """
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

    loc, los = process_src_file(
        fname=test.file,
        comment_regex=ML_COMMENTS,
        spec_comment_regex=r"\(\*@[^@]+@\*\)",
    )
    test.loc = loc - test.loc_but_actually_los
    test.los = los + test.loc_but_actually_los
    test.ratio = float(test.los) / float(test.loc)

    test.z3_time = float(re.search(r"\[\s*Z3\s*\]\s*([0-9.]+) s", output).group(1))
    test.why3_time = float(re.search(r"\[\s*Why3\s*\]\s*([0-9.]+) s", output).group(1))
    test.total_time = float(
        re.search(r"\[\s*Total\s*\]\s*([0-9.]+) s", output).group(1)
    )
    test.lemmas = len(re.findall(r"Entail Check", output))


def run_prusti(test):
    """
    Does not run the files, only counts lines.
    Files can be absent for inexpressible=True.
    """
    # output = subprocess.run(
    #     ["docker", "run", "-it", "oopsla215", "time", "./run-test.sh", test.file],
    #     capture_output=True,
    #     text=True,
    # ).stdout
    # test.total_time = float(
    #     re.search(r"\[\s*Total\s*\]\s*([0-9.]+) s", output).group(1)
    # )
    if test.file:
        loc, los = process_src_file(
            fname=test.file,
            comment_regex=RUST_COMMENTS,
            spec_comment_regex=PRUSTI_SPEC,
        )
        test.loc = loc
        test.los = los
        test.ratio = float(los) / float(loc)
    else:
        test.loc = 0
        test.los = 0
        test.ratio = 0


def run_cameleer(test):
    """
    Read Why3 session file, which contains a record of how the proof was done
    """
    # file = f"{path}/{bench}/why3session.xml"
    file, _ = os.path.splitext(test.file)
    file += "/why3session.xml"

    with open(file, "r") as f:
        txt = f.read()

    m = re.findall(r"time=\"([0-9.]+)\"", txt)

    test.total_time = sum([float(t) for t in m])

    loc, los = process_src_file(
        fname=test.file,
        comment_regex=ML_COMMENTS,
        spec_comment_regex=CAMELEER_SPEC,
    )
    # eprint(test.file)
    test.loc = loc
    test.los = los
    test.ratio = float(los) / float(loc)
    test.lemmas = len(re.findall(r"^ <goal", txt, re.MULTILINE))


def compute_stats(name, benchmarks):
    total_loc = sum([b.loc for _, b in benchmarks.items()])
    total_los = sum([b.los for _, b in benchmarks.items()])
    avg = total_los / total_loc

    eprint(name)
    eprint(f"average ratio: {avg:.2f}")
    eprint(f"total loc: {total_loc:.2f}")
    eprint(f"total los: {total_los:.2f}")
    eprint()
    return avg, total_loc, total_los


if __name__ == "__main__":
    # CONFIGURE SOME STUFF

    cameleer_path = os.path.expanduser("~/ocaml/cameleer")

    cameleer_benchmarks = {
        "map": Test(
            file=f"{cameleer_path}/map.ml",
            properties=[
                "map_id",
                "map_succ",
                "map_thrice",
            ],
        ),
        "fold": Test(
            file=f"{cameleer_path}/examples/ocaml_fold.ml",
            properties=[
                "foldl_sum",
                "foldl_length",
                "foldr_sum",
                "foldr_length",
            ],
        ),
        "applyN": Test(file=f"{cameleer_path}/applyN.ml", properties=["summary"]),
        "compose": Test(
            file=f"{cameleer_path}/compose.ml", properties=["compose_pure"]
        ),
        # leaving these out
        # "exception": Test(file=f"{cameleer_path}/exception.ml"),
        # "map_list": Test(file=f"{cameleer_path}/map_list.ml"),
    }

    heifer_benchmarks = {
        "map": Test(
            file="benchmarks/ho/heifer/map.ml",
            properties=[
                "map_id",
                "map_succ",
                "map_thrice",
            ],
            # succ_list, thrice_list
            loc_but_actually_los=4 + 4,
        ),
        "map_closure": Test(
            file="benchmarks/ho/heifer/map_closure.ml",
            properties=[
                "cl_map",
                "cl_map_incr_l",
                "cl_map_incr_l",
            ],
            # length
            loc_but_actually_los=4,
        ),
        "fold": Test(
            file="benchmarks/ho/heifer/fold.ml",
            properties=[
                "foldl_sum",
                "foldl_length",
                "foldr_sum",
                "foldr_length",
            ],
            # length, sum
            loc_but_actually_los=4 + 4,
        ),
        "fold_closure": Test(
            file="benchmarks/ho/heifer/fold_closure.ml",
            properties=[
                "foldl_sum_state",
                "foldl_length_state",
                "foldr_sum_state",
                "foldr_length_state",
            ],
            # length, sum
            loc_but_actually_los=4 + 4,
        ),
        "iter": Test(
            file="benchmarks/ho/heifer/iter.ml",
            properties=["build_fill"],
            # integers
            loc_but_actually_los=3,
        ),
        "compose": Test(
            file="benchmarks/ho/heifer/compose.ml",
            properties=["compose_pure"],
        ),
        "compose_closure": Test(
            file="benchmarks/ho/heifer/compose_closure.ml",
            properties=["compose_state_1", "compose_state_2"],
        ),
        "closure": Test(
            file="benchmarks/ho/heifer/closure.ml",
            src="svendsen2013modular",
            properties=[
                "closures_with_local_state",
                "closure_with_effects",
                "private_aliased",
            ],
        ),
        "closure_list": Test(
            file="benchmarks/ho/heifer/closure_list.ml",
            properties=[
                "closure_list",
            ],
        ),
        "applyN": Test(
            file="benchmarks/ho/heifer/applyN.ml",
            properties=["summary"],
        ),
        "blameassgn": Test(
            file="benchmarks/ho/heifer/blameassgn.ml",
            src="Findler2002ContractsFH",
            properties=["g_f_false"],
        ),
        "counter": Test(
            file="benchmarks/ho/heifer/counter.ml",
            src="Kassios2010SpecificationAV",
            properties=["counter"],
        ),
        "lambda": Test(file="benchmarks/ho/heifer/lambda.ml", properties=["main", "g"]),
    }

    prusti_path = os.path.expanduser(
        "~/ocaml/AlgebraicEffect/stuff/prusti-artifact-programs/pass"
    )

    prusti_benchmarks = {
        "closure": Test(
            file=f"{prusti_path}/../../../benchmarks/ho/prusti/closure.rs",  # written by us
            properties=[
                "main",
            ],
            total_time=6.753,
        ),
        "blameassgn": Test(
            file=f"{prusti_path}/blameassgn.rs",
            properties=[
                "main",
            ],
            total_time=6.235,
        ),
        "counter": Test(
            file=f"{prusti_path}/counter.rs",
            properties=[
                "main",
            ],
            total_time=6.374,
        ),
        # "map": Test(
        #     file=f"{prusti_path}/map_vec.rs",
        #     properties=[
        #         "main",
        #     ],
        #     total_time=10.349,  # with test2 removed
        # ),
        # "map_closure": Test(
        #     inexpressible=True,
        # ),
        "compose_closure": Test(
            inexpressible=True,
        ),
    }

    # END CONFIGURATION

    for k, v in cameleer_benchmarks.items():
        run_cameleer(v)

    for k, v in prusti_benchmarks.items():
        run_prusti(v)

    for n, t in heifer_benchmarks.items():
        eprint(f"{n}")
        run_heifer(t)

    eprint()

    # print state before transforming anything
    for n, t in heifer_benchmarks.items():
        eprint(
            f"""Benchmark: {n}
LoC: {t.loc}
LoS: {t.los}
Ratio: {t.ratio}
Total: {t.total_time}
Z3: {t.z3_time}
Why3: {t.why3_time}
Lemmas: {t.lemmas}
"""
        )

    # compute some stats
    heifer_avg, heifer_total_loc, heifer_total_los = compute_stats(
        "heifer", heifer_benchmarks
    )
    cameleer_avg, cameleer_total_loc, cameleer_total_los = compute_stats(
        "cameleer", cameleer_benchmarks
    )
    prusti_avg, prusti_total_loc, prusti_total_los = compute_stats(
        "prusti", prusti_benchmarks
    )

    print("% generated")
    for n, t in heifer_benchmarks.items():
        src = ""
        if t.src:
            src = rf"~\cite{{{t.src}}}"

        # cameleer's default is inexpressible
        # cameleer_cols = r"\inexpressible & \inexpressible & \inexpressible"
        cameleer_cols = r"& \inexpressible &"
        if n in cameleer_benchmarks:
            b = cameleer_benchmarks[n]
            cameleer_cols = f"{b.loc} & {b.los} & {b.total_time:.2f}"

        # prusti's default is untried
        # prusti_cols = r"\untried & \untried & \untried"
        prusti_cols = r"& \untried &"
        if n in prusti_benchmarks:
            b = prusti_benchmarks[n]
            if b.inexpressible:
                prusti_cols = r"& \inexpressible &"
            else:
                prusti_cols = f"{b.loc} & {b.los} & {b.total_time:.2f}"

        # escape name of benchmark
        n1 = re.sub("_", r"\_", n)

        print(
            f"{n1}{src} & {t.loc} & {t.los} & {t.total_time:.2f} & {t.z3_time + t.why3_time:.2f} & {cameleer_cols} & {prusti_cols} \\\\"
        )
    print("\\hline")
    print(
        f"& {heifer_total_loc} & {heifer_total_los} & & & {cameleer_total_loc} & {cameleer_total_los} & & {prusti_total_loc} & {prusti_total_los} & \\\\"
    )
    print("% end generated")

    eprint(rf"\newcommand*{{\heiferratio}}{{{heifer_avg:.2f}}}")
    eprint(rf"\newcommand*{{\cameleerratio}}{{{cameleer_avg:.2f}}}")
    eprint(rf"\newcommand*{{\prustiratio}}{{{prusti_avg:.2f}}}")
