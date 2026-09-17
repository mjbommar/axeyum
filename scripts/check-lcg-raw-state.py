#!/usr/bin/env python3
"""No test generator hands out a raw LCG state -- and the backlog can only shrink.

Why this exists (2026-09-16, lane ax-proptest, bench-results/proptest-box-
audit-20260916): the repository's hand-rolled fuzz generators are all the same
MMIX linear-congruential generator, `state = state * a + c mod 2^64` with `a`
and `c` odd, and most of them returned the STATE ITSELF from `next_u64`. Bit
`k` of such a generator has period `2^(k+1)`: bit 0 alternates on every draw,
bits 0-1 cycle with period 4, bits 0-2 with period 8. So `flip()`, `& 1`,
`below(2)`, `below(4)` and `below(8)` at a fixed draw offset from the seed are
CONSTANTS -- a fixed function of the seed's parity -- and two consecutive
`below(2)` draws are anti-correlated with certainty.

Measured consequences, each a class the fuzz was believed to cover:
  * `qf_lia_differential_fuzz`: the `DivByConstZero` corner asserted the
    negated atom for all 80 of its seeds, so the SATISFIABLE `(div p 0) = c`
    shape -- the a946f925 wrong-unsat's own shape -- was never in the random
    population;
  * `quantified_bv_differential_fuzz`: 0 of 600 quantified bodies mentioned a
    bound variable (every sentence was `forall x y. <ground>`);
  * `nia_differential_fuzz`: `mod` was never emitted and no divisor was ever
    negative; `qf_uf_differential_fuzz`: the term language collapsed to four
    atom shapes; the vivify fuzzes: every clause was single-polarity;
  * `check_qf_bv_faithfulness` (PRODUCTION, its seed is part of the
    certificate): bit 0 of every symbol was 0 on every sample at every seed.

The fix is one line per generator -- pass the output through a finalizer such
as SplitMix64's -- but the idiom was copied into 81 files, and prose does not
stop the 82nd. This gate does: every raw-state return site must be listed in
`scripts/lcg-raw-state-baseline.txt` with its count, a NEW site fails, a GROWN
count fails, and a baseline entry the tree no longer needs also fails (so the
number ratchets down honestly rather than rotting). `--print` lists the
backlog. Exit status depends on the finding.

What counts as a raw-state return: inside a function whose body updates the
state with one of the known LCG multipliers, the function's tail expression is
a bare state name (`self.0`, `state`, `self.state`, `s`, ...) rather than a
mixed value. A tail that shifts (`state >> 33`), xors, or multiplies the state
before returning is not flagged -- it may still be weak, but it is not the
period-2 trap this gate is about.
"""

from __future__ import annotations

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CRATES = os.path.join(ROOT, "crates")
BASELINE = os.path.join(ROOT, "scripts", "lcg-raw-state-baseline.txt")

# The LCG multipliers seen in this repository (MMIX / Knuth, and the
# `2862933555777941757` variant used in axeyum-cas). Underscores are stripped
# before matching so both spellings count.
MULTIPLIERS = ("6364136223846793005", "2862933555777941757")

# A tail expression that IS the state: a bare path with no operator.
RAW_TAIL = re.compile(
    r"^\s*(self\.(?:[0-9]+|[A-Za-z_][A-Za-z0-9_]*)|\*?state|\*?s|\*?st|\*?x|\*?seed|\*?rng)\s*$"
)


def raw_state_sites(text: str) -> list[int]:
    """1-based line numbers of raw-state tail returns in `text`.

    A site is: a line carrying an LCG multiplier, followed within the next
    six lines (the `.wrapping_add(...)` continuation and the return) by a
    tail line that is a bare state name and then a closing brace.
    """
    lines = text.splitlines()
    plain = [ln.replace("_", "") for ln in lines]
    sites = []
    for i, ln in enumerate(plain):
        if not any(m in ln for m in MULTIPLIERS):
            continue
        for j in range(i + 1, min(i + 7, len(lines))):
            if RAW_TAIL.match(lines[j]):
                # The tail must be the function's last expression: the next
                # non-blank line closes a block.
                k = j + 1
                while k < len(lines) and not lines[k].strip():
                    k += 1
                if k < len(lines) and lines[k].strip().startswith("}"):
                    sites.append(j + 1)
                break
    return sites


def scan(crates_dir: str) -> dict[str, list[int]]:
    found: dict[str, list[int]] = {}
    for dirpath, _dirnames, filenames in os.walk(crates_dir):
        if os.sep + "target" + os.sep in dirpath + os.sep:
            continue
        for name in filenames:
            if not name.endswith(".rs"):
                continue
            path = os.path.join(dirpath, name)
            try:
                with open(path, encoding="utf-8") as fh:
                    text = fh.read()
            except (OSError, UnicodeDecodeError):
                continue
            sites = raw_state_sites(text)
            if sites:
                found[os.path.relpath(path, os.path.dirname(crates_dir))] = sites
    return found


def read_baseline(path: str) -> dict[str, int]:
    out: dict[str, int] = {}
    if not os.path.exists(path):
        return out
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            rel, _, count = line.rpartition(":")
            out[rel.strip()] = int(count)
    return out


def evaluate(found: dict[str, list[int]], baseline: dict[str, int]) -> tuple[bool, list[str]]:
    """(ok, messages). Every message is a finding; none is decoration."""
    messages = []
    ok = True
    for rel in sorted(found):
        n = len(found[rel])
        if rel not in baseline:
            ok = False
            messages.append(f"NEW raw-state return in {rel} at line(s) {found[rel]} -- mix the output")
        elif n > baseline[rel]:
            ok = False
            messages.append(f"GREW {rel}: {baseline[rel]} -> {n} raw-state return(s) at {found[rel]}")
    for rel in sorted(baseline):
        n = len(found.get(rel, []))
        if n < baseline[rel]:
            ok = False
            messages.append(
                f"STALE baseline {rel}: pinned {baseline[rel]}, tree has {n} -- ratchet the baseline down"
            )
    return ok, messages


def main(argv: list[str]) -> int:
    crates_dir = CRATES
    baseline_path = BASELINE
    args = list(argv[1:])
    if "--crates" in args:
        crates_dir = args[args.index("--crates") + 1]
    if "--baseline" in args:
        baseline_path = args[args.index("--baseline") + 1]
    found = scan(crates_dir)
    scanned = sum(1 for _d, _s, files in os.walk(crates_dir) for f in files if f.endswith(".rs"))
    if scanned == 0:
        print("LCG_RAW_STATE|FAIL|scanned zero Rust files -- wrong path?")
        return 1
    if "--print" in args:
        for rel in sorted(found):
            print(f"{rel}:{len(found[rel])}")
        return 0
    baseline = read_baseline(baseline_path)
    ok, messages = evaluate(found, baseline)
    for m in messages:
        print(f"LCG_RAW_STATE|FAIL|{m}")
    total = sum(len(v) for v in found.values())
    print(
        f"LCG_RAW_STATE|files_scanned={scanned}|raw_state_files={len(found)}"
        f"|raw_state_sites={total}|baseline_files={len(baseline)}|{'PASS' if ok else 'FAIL'}"
    )
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
