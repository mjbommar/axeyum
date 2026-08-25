"""Micro-benchmarks for the `axeyum._native` binding surface.

Plain `time.perf_counter`, no third-party dependency: the dev group installs
`pytest` and `ruff` only, and a benchmark that needs a plugin nobody has is a
benchmark nobody runs. Every case reports the MINIMUM of its repeats, not the
mean -- the minimum is the one statistic a noisy shared box cannot inflate, and
these lanes share a host.

Usage::

    uv run python python/benchmarks/bench_binding.py
    uv run python python/benchmarks/bench_binding.py --json out.json
    uv run python python/benchmarks/bench_binding.py --only smt.solve

The `--json` form emits a record per case (`name`, `unit`, `best`, `repeats`,
`n`) so a later commit can pin these numbers without reformatting anything.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import statistics
import subprocess
import sys
import time
from collections.abc import Callable, Iterator
from dataclasses import asdict, dataclass

REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]
CORPUS = REPO_ROOT / "corpus" / "regression"

# Twenty committed `sat` benchmarks, named rather than globbed so the number is
# comparable across runs and across machines. Chosen by `:status sat` in sorted
# path order, spanning QF_ABV / QF_BV / QF_FP / QF_LIA / QF_LRA / QF_S so the
# double-solve cost is not measured on one theory's route alone.
SAT_FILES = [
    "cvc5/qf_abv/cvc5__cli__regress0__arrays__bug3020.smt2",
    "cvc5/qf_abv/cvc5__cli__regress0__arrays__issue4780-3.smt2",
    "cvc5/qf_abv/cvc5__cli__regress0__arrays__issue9043_1.smt2",
    "cvc5/qf_abv/cvc5__cli__regress0__arrays__issue9043_2.smt2",
    "cvc5/qf_abv/cvc5__cli__regress0__bv__issue8106_2.smt2",
    "cvc5/qf_abv/cvc5__cli__regress0__bv__issue8106.smt2",
    "cvc5/qf_abv/cvc5__cli__regress0__bv__issue8809.smt2",
    "cvc5/qf_abv/cvc5__cli__regress0__bv__proj-issue320.smt2",
    "cvc5/qf_bv/cvc5__cli__regress0__bug578.smt2",
    "cvc5/qf_bv/cvc5__cli__regress0__bv__bool-model.smt2",
    "cvc5/qf_bv/cvc5__cli__regress0__bv__bvmul-pow2-only.smt2",
    "cvc5/qf_fp/cvc5__cli__regress0__fp__abs-unsound.smt2",
    "cvc5/qf_fp/cvc5__cli__regress0__fp__bvcomp-rewrite.smt2",
    "cvc5/qf_fp/cvc5__cli__regress0__fp__issue3536.smt2",
    "cvc5/qf_fp/cvc5__cli__regress0__fp__issue7858-1.smt2",
    "cvc5/qf_lia/cvc5__cli__regress0__bug383.smt2",
    "cvc5/qf_lia/cvc5__cli__regress1__arith__issue789.smt2",
    "cvc5/qf_lia/cvc5__cli__regress1__sym__sym4.smt2",
    "cvc5/qf_lra/cvc5__cli__regress0__bug187.smt2",
    "cvc5/qf_s/cvc5__cli__regress0__strings__issue3440.smt2",
]

# Ten committed `unsat` benchmarks, same construction.
UNSAT_FILES = [
    "uflia_induction/guarded_parity_range.smt2",
    "uflia_induction/guarded_linear_nonneg.smt2",
    "uflia_induction/guarded_linear_closed_form.smt2",
    "cvc5/qf_abv/cvc5__cli__regress0__bv__issue8274.smt2",
    "cvc5/qf_abv/cvc5__cli__regress0__arrays__bug637.delta.smt2",
    "cvc5/qf_fp/cvc5__cli__regress0__fp__rti_3_5_bug.smt2",
    "cvc5/qf_abv/cvc5__cli__regress0__arrays__issue5925.smt2",
]


@dataclass
class Case:
    """One measured benchmark case."""

    name: str
    unit: str
    best: float
    median: float
    repeats: int
    n: int


def _measure(name: str, unit: str, n: int, repeats: int, body: Callable[[], object]) -> Case:
    """Runs `body` `repeats` times and reports the best and median wall time."""
    samples = []
    for _ in range(repeats):
        start = time.perf_counter()
        body()
        samples.append(time.perf_counter() - start)
    return Case(
        name=name,
        unit=unit,
        best=min(samples),
        median=statistics.median(samples),
        repeats=repeats,
        n=n,
    )


def _existing(names: list[str]) -> list[pathlib.Path]:
    """The named corpus files that are present, so a trimmed corpus degrades."""
    return [path for name in names if (path := CORPUS / name).is_file()]


def bench_smt_solve() -> Iterator[Case]:
    """`smt.solve` over committed `sat` and `unsat` scripts."""
    from axeyum import smt

    sat = [path.read_text() for path in _existing(SAT_FILES)]
    unsat = [path.read_text() for path in _existing(UNSAT_FILES)]

    def run(scripts: list[str]) -> None:
        for text in scripts:
            smt.solve(text, timeout_ms=10_000)

    if sat:
        yield _measure("smt.solve/sat", "s per sweep", len(sat), 3, lambda: run(sat))
    if unsat:
        yield _measure("smt.solve/unsat", "s per sweep", len(unsat), 3, lambda: run(unsat))


def bench_arena() -> Iterator[Case]:
    """Term construction: 10k hash-consed nodes through the `Arena` surface."""
    from axeyum import ir

    def build() -> None:
        arena = ir.Arena()
        x = arena.bv_var("x", 32)
        y = arena.bv_var("y", 32)
        acc = x
        for i in range(10_000):
            acc = arena.bvadd(acc, arena.bvmul(y, arena.bv_const(32, i % 97 + 1)))

    yield _measure("ir.Arena/build", "s per 10k terms", 10_000, 5, build)


def bench_eval() -> Iterator[Case]:
    """`ir.eval` of one ground term, 10k times -- the per-call crossing cost."""
    from axeyum import ir

    arena = ir.Arena()
    sx = arena.declare("x", ir.Sort.bv(32))
    sy = arena.declare("y", ir.Sort.bv(32))
    x = arena.bv_var("x", 32)
    y = arena.bv_var("y", 32)
    term = arena.bvadd(arena.bvmul(x, y), arena.bv_const(32, 7))
    assignment = arena.assignment()
    assignment.set(arena, sx, 12345)
    assignment.set(arena, sy, 6789)

    def run() -> None:
        for _ in range(10_000):
            ir.eval(arena, term, assignment)

    yield _measure("ir.eval", "s per 10k calls", 10_000, 5, run)


def bench_cas() -> Iterator[Case]:
    """`cas.simplify` over a mid-sized rational expression, 200 times."""
    from axeyum import cas

    # `Expr` has no parser by design, so the fixture is built structurally:
    # (x^2 - 1)/(x - 1) + sin(x)^2 + cos(x)^2 - x, which simplification collapses.
    x = cas.Expr.var("x")
    one = cas.Expr.one()
    expr = (x.pow(2) - one) / (x - one) + cas.Expr.sin(x).pow(2) + cas.Expr.cos(x).pow(2) - x

    def run() -> None:
        for _ in range(200):
            cas.simplify(expr)

    yield _measure("cas.simplify", "s per 200 calls", 200, 5, run)


def bench_prelude() -> Iterator[Case]:
    """`Kernel.build_nat_prelude`, cold process versus warm in-process cache."""
    from axeyum import kernel

    # Cold means a FRESH INTERPRETER: the prelude template cache is process-wide,
    # so a "cold" measurement taken after any other case in this process would be
    # measuring the cache. A subprocess is the only honest cold number.
    cold_src = (
        "import time;from axeyum import kernel;"
        "t=time.perf_counter();kernel.Kernel().build_nat_prelude();"
        "print(time.perf_counter()-t)"
    )
    samples = []
    for _ in range(3):
        out = subprocess.run(
            [sys.executable, "-c", cold_src], capture_output=True, text=True, check=True
        )
        samples.append(float(out.stdout.strip()))
    yield Case(
        name="Kernel.build_nat_prelude/cold",
        unit="s per build (fresh interpreter)",
        best=min(samples),
        median=statistics.median(samples),
        repeats=len(samples),
        n=1,
    )

    kernel.Kernel().build_nat_prelude()  # prime

    def warm() -> None:
        kernel.Kernel().build_nat_prelude()

    yield _measure("Kernel.build_nat_prelude/cached", "s per build", 1, 20, warm)


def bench_proof_text() -> Iterator[Case]:
    """Proof text handoff: `str` accessors versus the `bytes` accessors."""
    from axeyum import ir, solver

    # A 24-bit multiplier contradiction: big enough that the DIMACS text is
    # hundreds of kilobytes, which is the regime where handing it across as a
    # `str` copy is worth measuring at all.
    arena = ir.Arena()
    a = arena.bv_var("a", 24)
    b = arena.bv_var("b", 24)
    product = arena.bvmul(a, b)
    assertions = [
        arena.bvult(product, arena.bv_const(24, 4)),
        arena.bvugt(product, arena.bv_const(24, 4)),
    ]
    outcome = solver.proofs.export_qf_bv_unsat_proof(arena, assertions, timeout_ms=60_000)
    proof = getattr(outcome, "proof", None)
    if proof is None:
        return
    print(f"  (proof fixture: dimacs={len(proof.dimacs)}B drat={len(proof.drat)}B)")

    def read_str() -> None:
        for _ in range(200):
            _ = proof.dimacs

    yield _measure("UnsatProof.dimacs (str)", "s per 200 reads", 200, 5, read_str)

    if hasattr(proof, "dimacs_bytes"):

        def read_bytes() -> None:
            for _ in range(200):
                _ = proof.dimacs_bytes()

        yield _measure("UnsatProof.dimacs_bytes", "s per 200 reads", 200, 5, read_bytes)


def bench_declarations() -> Iterator[Case]:
    """`Kernel.declarations()` versus the name-only / single-name accessors."""
    from axeyum import kernel

    k = kernel.Kernel()
    k.build_nat_prelude()

    def full() -> None:
        for _ in range(20):
            k.declarations()

    yield _measure("Kernel.declarations", "s per 20 calls", 20, 5, full)

    if hasattr(k, "declaration_names"):

        def names() -> None:
            for _ in range(20):
                k.declaration_names()

        yield _measure("Kernel.declaration_names", "s per 20 calls", 20, 5, names)

        # The single-name accessor is the long-standing `get_declaration`; the
        # name-only listing is what was missing beside it.
        sample = k.declaration_names()[0]

        def one() -> None:
            for _ in range(20):
                k.get_declaration(sample)

        yield _measure("Kernel.get_declaration", "s per 20 calls", 20, 5, one)


BENCHES: dict[str, Callable[[], Iterator[Case]]] = {
    "smt.solve": bench_smt_solve,
    "ir.Arena": bench_arena,
    "ir.eval": bench_eval,
    "cas.simplify": bench_cas,
    "kernel.prelude": bench_prelude,
    "solver.proof": bench_proof_text,
    "kernel.declarations": bench_declarations,
}


def main() -> int:
    """Runs the selected benchmarks and prints a table (or JSON)."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", metavar="PATH", help="write the records to PATH as JSON")
    parser.add_argument(
        "--only",
        action="append",
        choices=sorted(BENCHES),
        help="run only this group (repeatable)",
    )
    parser.add_argument("--label", default="", help="a label stored in the JSON record")
    args = parser.parse_args()

    groups = args.only or sorted(BENCHES)
    cases: list[Case] = []
    for group in groups:
        for case in BENCHES[group]():
            cases.append(case)
            print(f"{case.name:34s} {case.best * 1000:12.3f} ms  ({case.unit})")

    if args.json:
        payload = {"label": args.label, "cases": [asdict(case) for case in cases]}
        pathlib.Path(args.json).write_text(json.dumps(payload, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
