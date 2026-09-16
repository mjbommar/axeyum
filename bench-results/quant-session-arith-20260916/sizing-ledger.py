#!/usr/bin/env python3
"""Exit-1 sizing for ADR-2130: of the rows ADR-2124 attributed to the interleaved
ground check, how many carry an ARITHMETIC-bearing ground set?

ADR-2124's lever made `OnlineQuantifierClauseSession` exist on those sets by
ABSTRACTING every Boolean-position term the `EUF` encoder has no arm for.  An
abstracted atom is a free propositional variable: the session can decline to
re-solve, but it cannot REFUTE through it.  So the population ADR-2130 (hosting
the arithmetic theory) can move is the subset whose refusing atoms are
ARITHMETIC -- a datatype tester or a `distinct` is refused for a different
theory and is sized separately here rather than folded in.

Two things this script does deliberately.

1.  **It re-derives ADR-2124's qGROUND population rather than quoting it.**  The
    script that produced `SIZING-ledger.txt` was NOT committed (the README lists
    only its output), so the 108/101 was unfalsifiable in-tree.  The predicate
    below reproduces that table EXACTLY on all seven divisions -- see
    `--self-check`, which fails if it ever stops doing so.  The reading that
    works is narrow and was not the first one tried: the LAST `q:`-prefixed
    decline **that carries a nonempty detail**.  Taking the last `q:` decline
    regardless of whether its detail is empty gives 27/20, not 108/101.

2.  **It reports a STATIC classification and says so.**  The ground set handed
    to the interleaved check is dynamic -- it grows with every admitted
    instance.  What is scanned here is the benchmark's own text: the atoms that
    appear in ground (unquantified) assertion positions, and separately the ones
    that appear only under a quantifier and therefore reach the ground set only
    through an instance.  Both are reported.  Neither is the ground set; the
    dynamic measurement is the `[qtrace] ground-session` counter and lives in
    `sizing-session.py`.

Usage:
    python3 sizing-ledger.py --self-check
    python3 sizing-ledger.py > SIZING-ledger.txt
"""

from __future__ import annotations

import argparse
import csv
import os
import sys
from pathlib import Path

csv.field_size_limit(10**9)

REPO = Path(__file__).resolve().parents[2]
LEDGER = REPO / "bench-results" / "ledger"
CORES53 = (
    REPO
    / "bench-results"
    / "quant-ground-incremental-20260916"
    / "cores53.paths"
)
CORPUS = Path("/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental")

DIVS = ["AUFDTLIRA", "AUFLIRA", "QF_NIA", "UF", "UFDTLIRA", "UFLIA", "UFNIA"]
LEDGER_BINARY = "db31113fa"

# ADR-2124 SIZING-ledger.txt, the table this script must keep reproducing.
ADR2124_TABLE = {
    "AUFDTLIRA": (18, 18),
    "AUFLIRA": (6, 6),
    "QF_NIA": (0, 0),
    "UF": (4, 4),
    "UFDTLIRA": (1, 1),
    "UFLIA": (34, 28),
    "UFNIA": (45, 44),
}

GROUND_CHECK_DETAIL = "interleaved ground check"

# The Boolean-position shapes `EufEncoder::encode` has no arm for, by theory.
# These are the terms ADR-2124 level 1 abstracts to a free propositional
# variable -- the ones this lane proposes to HOST instead.
ARITH_PREDS = {"<", "<=", ">", ">=", "divisible", "is_int"}
# A `distinct` over any sort: EUF-shaped, but still no encoder arm.
DISTINCT_PREDS = {"distinct"}
# Arithmetic FUNCTION symbols.  Their presence means the ground set has integer
# or real TERMS even where the comparison itself is hidden behind a macro.
ARITH_FUNS = {"+", "-", "*", "/", "div", "mod", "abs", "to_int", "to_real"}


# ---------------------------------------------------------------- s-expressions


def tokenize(text: str):
    """SMT-LIB tokens.  Handles `;` comments, `|quoted|` symbols and strings."""
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch in " \t\r\n":
            i += 1
        elif ch == ";":
            j = text.find("\n", i)
            i = n if j < 0 else j + 1
        elif ch in "()":
            yield ch
            i += 1
        elif ch == "|":
            j = text.find("|", i + 1)
            j = n if j < 0 else j + 1
            yield text[i:j]
            i = j
        elif ch == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        j += 2
                        continue
                    j += 1
                    break
                j += 1
            yield text[i:j]
            i = j
        else:
            j = i
            while j < n and text[j] not in " \t\r\n()|;\"":
                j += 1
            yield text[i:j]
            i = j


def parse(text: str):
    """Top-level s-expressions, as nested lists of str."""
    stack: list[list] = [[]]
    for tok in tokenize(text):
        if tok == "(":
            stack.append([])
        elif tok == ")":
            if len(stack) == 1:
                continue  # unbalanced input: keep what parsed
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(tok)
    return stack[0]


def is_dt_tester(head) -> bool:
    """`(_ is C)` -- the indexed form.  `is-C` sugar is not SMT-LIB 2.6."""
    return isinstance(head, list) and len(head) == 3 and head[0] == "_" and head[1] == "is"


def scan(node, under_q: bool, acc: dict) -> None:
    """Record which refusing shapes occur, split by quantifier depth."""
    if not isinstance(node, list) or not node:
        return
    head = node[0]
    binder = isinstance(head, str) and head in ("forall", "exists")
    if isinstance(head, str):
        key = "q" if under_q else "g"
        if head in ARITH_PREDS:
            acc[f"arith_{key}"] += 1
        elif head in DISTINCT_PREDS:
            acc[f"distinct_{key}"] += 1
        elif head in ARITH_FUNS:
            acc[f"arithfun_{key}"] += 1
    elif is_dt_tester(head):
        acc["dttest_q" if under_q else "dttest_g"] += 1
    for child in node[1:] if binder else node:
        scan(child, under_q or binder, acc)


def classify(path: Path) -> dict | None:
    try:
        text = path.read_text(errors="replace")
    except OSError:
        return None
    acc = {
        f"{k}_{s}": 0
        for k in ("arith", "distinct", "dttest", "arithfun")
        for s in ("g", "q")
    }
    for form in parse(text):
        if isinstance(form, list) and form and form[0] == "assert":
            for child in form[1:]:
                scan(child, False, acc)
    return acc


# ------------------------------------------------------------------- the ledger


def qground_rows(div: str):
    """ADR-2124's qGROUND population, re-derived.

    The predicate: among a row's decline pairs, take the LAST one whose route
    is `q:`-prefixed AND whose detail is nonempty; the row is in the population
    when that detail names the interleaved ground check.
    """
    path = LEDGER / f"t1-{div}-{LEDGER_BINARY}.tsv"
    out = []
    with path.open() as handle:
        for row in csv.DictReader(handle, delimiter="\t"):
            reasons = [p for p in row["decline_reasons"].split("\\p") if p]
            details = row["decline_details"].split("\\p")
            last = None
            for i, reason in enumerate(reasons):
                if reason.startswith("q:") and i < len(details) and details[i]:
                    last = details[i]
            if last and GROUND_CHECK_DETAIL in last:
                out.append((row["corpus_path"], row["verdict"]))
    return out


def self_check() -> int:
    bad = 0
    for div in DIVS:
        rows = qground_rows(div)
        got = (len(rows), sum(1 for _, v in rows if v == "unknown"))
        want = ADR2124_TABLE[div]
        mark = "ok " if got == want else "BAD"
        if got != want:
            bad += 1
        print(f"{mark} {div:12s} got={got[0]:3d}/{got[1]:3d}  ADR-2124={want[0]:3d}/{want[1]:3d}")
    print()
    if bad:
        print(f"SELF-CHECK FAILED on {bad} of {len(DIVS)} divisions")
    else:
        print("SELF-CHECK PASS: the qGROUND predicate reproduces ADR-2124 on all 7 divisions")
    return 1 if bad else 0


# ------------------------------------------------------------------------ report


def bucket(acc: dict) -> str:
    """One label per file, in the order a refusal would be hit."""
    if acc["arith_g"] or acc["distinct_g"] or acc["dttest_g"]:
        pass
    arith = acc["arith_g"] + acc["arith_q"]
    dt = acc["dttest_g"] + acc["dttest_q"]
    dist = acc["distinct_g"] + acc["distinct_q"]
    fun = acc["arithfun_g"] + acc["arithfun_q"]
    if arith:
        return "arith"
    if dt:
        return "dt-only"
    if fun:
        return "arithfun-only"
    if dist:
        return "distinct-only"
    return "euf-only"


def report_population(title: str, files: list[tuple[str, str, Path]]) -> None:
    print(f"== {title} ==")
    print(
        f"{'division':12s} {'n':>4s} {'arith':>6s} {'arithG':>7s} {'arithQonly':>11s} "
        f"{'dt-only':>8s} {'fun-only':>9s} {'dist-only':>10s} {'euf-only':>9s} {'missing':>8s}"
    )
    print("-" * 92)
    per: dict[str, dict[str, int]] = {}
    for div, _verdict, path in files:
        slot = per.setdefault(
            div,
            {
                "n": 0,
                "arith": 0,
                "arithG": 0,
                "arithQonly": 0,
                "dt": 0,
                "fun": 0,
                "dist": 0,
                "euf": 0,
                "missing": 0,
            },
        )
        slot["n"] += 1
        acc = classify(path)
        if acc is None:
            slot["missing"] += 1
            continue
        label = bucket(acc)
        if label == "arith":
            slot["arith"] += 1
            if acc["arith_g"]:
                slot["arithG"] += 1
            else:
                slot["arithQonly"] += 1
        elif label == "dt-only":
            slot["dt"] += 1
        elif label == "arithfun-only":
            slot["fun"] += 1
        elif label == "distinct-only":
            slot["dist"] += 1
        else:
            slot["euf"] += 1
    total = {
        k: 0
        for k in ("n", "arith", "arithG", "arithQonly", "dt", "fun", "dist", "euf", "missing")
    }
    for div in sorted(per):
        s = per[div]
        for k in total:
            total[k] += s[k]
        print(
            f"{div:12s} {s['n']:4d} {s['arith']:6d} {s['arithG']:7d} {s['arithQonly']:11d} "
            f"{s['dt']:8d} {s['fun']:9d} {s['dist']:10d} {s['euf']:9d} {s['missing']:8d}"
        )
    print("-" * 92)
    print(
        f"{'TOTAL':12s} {total['n']:4d} {total['arith']:6d} {total['arithG']:7d} "
        f"{total['arithQonly']:11d} {total['dt']:8d} {total['fun']:9d} {total['dist']:10d} "
        f"{total['euf']:9d} {total['missing']:8d}"
    )
    print()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--self-check", action="store_true")
    args = ap.parse_args()
    if args.self_check:
        return self_check()

    print("== ADR-2130 exit-1 sizing: the ARITHMETIC-bearing share of the ground-check population ==")
    print()
    print("population : ADR-2124's qGROUND rows, RE-DERIVED here (its own script was not committed).")
    print("predicate  : the LAST `q:`-prefixed decline WITH A NONEMPTY DETAIL names")
    print(f"             {GROUND_CHECK_DETAIL!r}.  Reproduces ADR-2124's table on 7 of 7 divisions;")
    print("             `--self-check` fails if it ever stops doing so.")
    print("source     : bench-results/ledger/t1-<DIV>-%s.tsv, 200 benchmarks per division." % LEDGER_BINARY)
    print()
    print("classification is STATIC over the benchmark TEXT, not over the dynamic ground set:")
    print("  arith      = a Boolean-position arithmetic comparison (<, <=, >, >=, divisible, is_int)")
    print("               occurs anywhere in an assertion.  THE CEILING FOR THIS LANE.")
    print("  arithG     = ...and at least one of them is in a GROUND (unquantified) position, so the")
    print("               session is refused on round 0 rather than only after an instance lands.")
    print("  arithQonly = the comparisons are all under a quantifier: the ground set acquires one")
    print("               only through an admitted instance, which is exactly the atom this lane's")
    print("               `add_atom_at_root` hook has to accept AFTER construction.")
    print("  dt-only    = no arithmetic comparison, but a datatype tester `(_ is C)`.  NOT this lane.")
    print("  fun-only   = no comparison at all, but arithmetic FUNCTION symbols (+ - * div mod ...).")
    print("               The EUF encoder accepts these -- an `=` over them has an arm -- so the session")
    print("               is not refused, but it treats `+` as UNINTERPRETED and can call `sat` where")
    print("               LIA refutes.  A SECOND population hosting arithmetic reaches, reported apart")
    print("               from the ceiling because the ground check is not what refuses them.")
    print("  distinct-only / euf-only = refused for neither reason; hosting LIA changes nothing.")
    print()
    self_check()
    print()

    ledger_files = []
    for div in DIVS:
        for corpus_path, verdict in qground_rows(div):
            ledger_files.append((div, verdict, CORPUS / corpus_path))
    report_population("1a: ALL qGROUND rows (108)", ledger_files)
    report_population(
        "1b: qGROUND rows that ended `unknown` (101) -- the population this lane can move",
        [t for t in ledger_files if t[1] == "unknown"],
    )

    core_files = []
    if CORES53.exists():
        for line in CORES53.read_text().split("\n"):
            line = line.strip()
            if line:
                core_files.append(("UFLIA-core", "core", Path(line)))
        report_population("1c: ADR-2113's 53 reference-minimal UFLIA cores", core_files)
    else:
        print(f"== 1c == NOT MEASURED: {CORES53} is absent (a stated absence, not a zero)")
    return 0


if __name__ == "__main__":
    sys.setrecursionlimit(100000)
    if os.environ.get("AXEYUM_SIZING_NO_LIMIT") != "1":
        pass
    raise SystemExit(main())
