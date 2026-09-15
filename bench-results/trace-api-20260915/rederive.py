#!/usr/bin/env python3
"""ADR-2101 exit criterion B: re-derive three ADRs' CORRECTED figures.

The failure mode this guards against is stated in the plan: **a reader that
reproduces the OLD wrong numbers is the failure mode**.  So each section below
prints the old number and the corrected number side by side and asserts the
corrected one.  Exit status is the finding.

What each section can and cannot do, stated up front because two of the three
are honest limits rather than results:

  ADR-2075  RE-DERIVED THROUGH THE READER.  The artifact is `--trace` stdout,
            which is exactly what the reader owns.  The old consumer
            (`grep -m1 '^; route '`, `bench-results/skeleton-reach-20260914/
            fd-census.sh:41`) is re-run here beside it on the same bytes.

  ADR-2020  NOT re-derivable through the reader, and the reason is checked
            rather than asserted: the census it corrected
            (`bench-results/round-head-20260914/census/FAMILY.shard0*.tsv`)
            has 26 columns and NOT ONE of them is a route trail -- verified
            below by counting `route-trail` occurrences in it.  The corrected
            figures are re-derived with the committed
            `census-binding-cause.py`; the reader's contribution is a
            STRUCTURAL claim, that the `;`-in-a-field defect is unreachable
            through it, driven by `scripts/tests/test-route-trace-reader.py::
            test_a_detail_containing_the_old_separators_survives_whole`.

  ADR-2060  Likewise not a trail read: its 28 is a count of PROGRAM POINTS in
            `lra.rs` on the PRE-FIX tree.  Re-running the committed
            `enumerate-producers.py` on today's tree is therefore expected to
            report 0 name-scan sites -- the fix removed them -- and that zero
            is itself the check.  The current typed vocabulary is counted from
            the five enums directly.

Run: python3 bench-results/trace-api-20260915/rederive.py
"""

from __future__ import annotations

import csv
import glob
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "scripts"))

import route_trace_reader as rtr  # noqa: E402

FINDINGS: list[tuple[str, bool, str]] = []


def check(label: str, got, want, note: str = "") -> None:
    ok = got == want
    FINDINGS.append((label, ok, f"got {got!r}, want {want!r}. {note}".strip()))
    mark = "MATCH " if ok else "DIFFER"
    print(f"  [{mark}] {label}: got {got!r}, want {want!r}")
    if note:
        print(f"           {note}")


def rel(*parts: str) -> str:
    return os.path.join(ROOT, *parts)


# ===========================================================================
# ADR-2075 -- through the reader, on the committed receipts
# ===========================================================================
def adr_2075() -> None:
    print("=" * 76)
    print("ADR-2075  the silent hang: there was never an absence")
    print("=" * 76)
    print()
    print("The defect, verbatim from the consumer that had it")
    print("  bench-results/skeleton-reach-20260914/fd-census.sh:41")
    print("    rl=$(printf '%s\\n' \"$raw\" | grep -m1 '^; route ' || true)")
    print("  The watchdog path prints `; partial route `, so that grep found")
    print("  nothing and the row was censused `bound_by=NONE`.")
    print()

    receipts = sorted(glob.glob(rel("bench-results/silent-hang-20260915/prof/*/stdout.txt")))
    assert receipts, "no committed receipts found -- the scan never reached its subject"

    old_found = 0
    new_found = 0
    partial_rows = 0
    rows = []
    for path in receipts:
        text = open(path, encoding="utf-8", errors="replace").read()
        # The OLD consumer, re-run verbatim on the same bytes.
        old_hit = any(line.startswith("; route ") for line in text.splitlines())
        old_found += 1 if old_hit else 0
        try:
            trail = rtr.read_file(path)
        except rtr.RouteTraceError:
            trail = None
        if trail is not None:
            new_found += 1
            partial_rows += 1 if trail.partial else 0
        partial_lines = sum(
            1 for line in text.splitlines() if line.startswith("; partial ")
        )
        rows.append(
            (
                os.path.basename(os.path.dirname(path)),
                "yes" if old_hit else "NO",
                "none" if trail is None else (trail.bound_by or "none"),
                "-" if trail is None else ("yes" if trail.partial else "no"),
                partial_lines,
            )
        )

    print(f"  {'receipt':16s} {'old grep':9s} {'reader bound_by':20s} {'partial':8s} {'; partial lines':>15s}")
    for name, old_hit, bound, partial, nlines in rows:
        print(f"  {name:16s} {old_hit:9s} {bound:20s} {partial:8s} {nlines:>15d}")
    print()

    check(
        "2075 receipts the OLD `^; route ` grep can attribute",
        old_found,
        2,
        "the four watchdog-killed receipts are invisible to it",
    )
    check(
        "2075 receipts the READER can attribute",
        new_found,
        len(receipts),
        "every one, and each names a real bound_by",
    )
    check("2075 of those, PARTIAL readings", partial_rows, 4)

    # The ADR's "Fourteen lines." claim, on the one committed receipt that
    # carries it.  The ADR names z3.850818 for this; the committed receipt for
    # that file took a DIFFERENT give-up path (`ResourceLimit`, not
    # `Watchdog`), so the 14-line receipt on disk is fp-mqueue's.  That is a
    # correction to the ADR's cross-reference, not to its number.
    mqueue = rel("bench-results/silent-hang-20260915/prof/fp-mqueue/stdout.txt")
    n14 = sum(
        1
        for line in open(mqueue, encoding="utf-8", errors="replace")
        if line.startswith("; partial ")
    )
    check(
        "2075 `Fourteen lines.` (ADR line 51) on the committed receipt",
        n14,
        14,
        "receipt is prof/fp-mqueue, not prof/fp-hoare -- see the note in the code",
    )

    # The population, by the ADR's own awk over the inherited census.
    census = rel("bench-results/skeleton-reach-20260914/ref/fd-census-208.tsv")
    # HEADERLESS, so positional -- the same columns the ADR's own awk used
    # ($2 verdict, $3 bound_by, $7 give-up kind).
    with open(census, encoding="utf-8") as handle:
        body = [r for r in csv.reader(handle, delimiter="\t") if len(r) >= 7]
    inherited = [
        r for r in body if r[1] == "unknown" and r[2] == "NONE" and r[6] == "Watchdog"
    ]
    complement = [r for r in body if r[1] == "unknown" and r[2] != "NONE"]
    check("2075 inherited population (ADR line 36)", len(inherited), 13)
    check(
        "2075 the awk's own positive control (ADR line 36: 'prints 142')",
        len(complement),
        142,
        "a non-empty complement, so the 13 is a filter result and not an empty scan",
    )

    phase = rel("bench-results/silent-hang-20260915/ref/phase-24s.tsv")
    with open(phase, encoding="utf-8") as handle:
        prows = list(csv.DictReader(handle, delimiter="\t"))
    rederived_out = [r for r in prows if r["phase_line"] == "NO-PHASE-LINE"]
    still = [r for r in prows if r["phase_line"] != "NO-PHASE-LINE"]
    check("2075 OLD bucket size, inherited from ADR-2040 sec.8", 12, 12, "the number the ADR corrected")
    check("2075 re-derived OUT (P5 predicted at most 2)", len(rederived_out), 4)
    check("2075 CORRECTED bucket size (ADR line 4: 'the population is 9')", len(still), 9)

    split: dict[str, int] = {}
    for row in still:
        split[row["phase_in"]] = split.get(row["phase_in"], 0) + 1
    check(
        "2075 the nine by INNERMOST running phase (ADR lines 105-109)",
        sorted(split.items()),
        sorted({"none": 3, "euf:fc-pair-scan": 2, "euf:offline": 2, "euf:round-incremental-arith": 2}.items()),
    )
    print()


# ===========================================================================
# ADR-2020 -- the truncated bucket
# ===========================================================================
def adr_2020() -> None:
    print("=" * 76)
    print("ADR-2020  the census split on `;` inside a field and truncated itself")
    print("=" * 76)
    print()

    shards = sorted(glob.glob(rel("bench-results/round-head-20260914/census/FAMILY.shard0*.tsv")))
    assert shards, "the ADR-2020 census is missing -- the scan never reached its subject"
    trail_hits = sum(
        open(s, encoding="utf-8", errors="replace").read().count("route-trail")
        for s in shards
    )
    check(
        "2020 route-trail columns in the corrected census",
        trail_hits,
        0,
        "so this artifact is NOT the reader's to own; see the module docstring",
    )

    proc = subprocess.run(
        [sys.executable, rel("bench-results/ground-decide-20260914/census-binding-cause.py"), ROOT],
        capture_output=True,
        text=True,
    )
    out = proc.stdout
    assert "LEVEL 0" in out, f"the committed census did not run:\n{proc.stderr[:800]}"

    def buckets(section: str) -> list[tuple[int, str]]:
        block = out.split(section, 1)[1].split("===", 1)[0]
        found = []
        for line in block.splitlines():
            m = re.match(r"^\s+(\d+)\s+(\S.*)$", line)
            if m and m.group(2).strip() != "TOTAL":
                found.append((int(m.group(1)), m.group(2).strip()))
        return found

    outer = buckets("=== LEVEL 0: the outer string (what a naive census sees) ===")
    inner = buckets("=== LEVEL N: the BINDING cause (wrappers peeled) ===")

    print("  OLD (outer string, what the naive census saw):")
    for n, name in outer:
        print(f"    {n:4d}  {name[:64]}")
    print("  CORRECTED (binding cause, wrappers peeled):")
    for n, name in inner:
        print(f"    {n:4d}  {name[:64]}")
    print()

    check("2020 OLD distinct buckets (ADR line 76)", len(outer), 5)
    check("2020 OLD largest bucket (ADR line 77)", outer[0][0], 25)
    check("2020 CORRECTED distinct buckets (ADR line 76)", len(inner), 10)
    check("2020 CORRECTED largest bucket (ADR line 77)", inner[0][0], 22)
    check(
        "2020 CORRECTED leader (ADR line 4/99)",
        inner[0][1].startswith("lazy linear arithmetic pre-SAT skeleton"),
        True,
        "not the eager Ackermann bound (17) the earlier prose led with -- that is second",
    )
    print()


# ===========================================================================
# ADR-2060 -- one string for 28 program points
# ===========================================================================
def adr_2060() -> None:
    print("=" * 76)
    print("ADR-2060  one give-up string for 28 program points and 15 causes")
    print("=" * 76)
    print()

    proc = subprocess.run(
        [
            sys.executable,
            rel("bench-results/timeout-diagnosis-20260914/scripts/enumerate-producers.py"),
            rel("crates/axeyum-solver/src/lra.rs"),
        ],
        capture_output=True,
        text=True,
    )
    out = proc.stdout
    print("  the committed enumerator, re-run on TODAY's tree:")
    for line in out.splitlines():
        print(f"    {line}")
    print()
    assert "NOT FOUND" not in out, (
        "the enumerator never reached its subject -- an empty result from a "
        "tool that was never pointed at your subject is not a negative"
    )

    m = re.search(r"\(whole file, any form\)\s+(\d+)", out)
    assert m, "the enumerator's output shape changed"
    check(
        "2060 `Decision::TimedOut` constructions on today's tree",
        int(m.group(1)),
        0,
        "the ADR's 28 counted the PRE-FIX tree; the fix removed every one",
    )

    source = open(rel("crates/axeyum-solver/src/lra.rs"), encoding="utf-8").read()
    sizes: dict[str, int] = {}
    for name in ("GaveUp", "FmDecline", "SimplexDecline", "ElimBail", "CollectDecline"):
        block = re.search(rf"^enum {name} \{{(.*?)^\}}", source, re.M | re.S)
        assert block, f"{name}: NOT FOUND -- the scan never reached its subject"
        sizes[name] = len(re.findall(r"^    ([A-Z][A-Za-z0-9]*)\s*[,{(]", block.group(1), re.M))
    print("  the typed vocabulary that replaced the one string:")
    for name, count in sizes.items():
        print(f"    {name:18s} {count} variants")
    print()
    check("2060 OLD: distinct reasons a consumer could tell apart", 1, 1, "one sentence")
    check("2060 OLD: program points behind it (ADR lines 55-57)", 28, 28, "27 distinct, 15 causes")
    check(
        "2060 CORRECTED: typed variants across the five enums, on today's tree",
        sum(sizes.values()),
        23,
        "ADR-2060 landed 22; `SimplexDecline` has since grown to 7",
    )

    # The reader's own contribution: the distinction must survive to a consumer.
    suite = rel("scripts/tests/test-route-trace-reader.py")
    run = subprocess.run([sys.executable, suite], capture_output=True, text=True)
    driven = "ok   test_two_declines_sharing_a_reason_token_stay_distinguishable" in run.stdout
    check(
        "2060 the reader keeps two declines with one reason token apart",
        (run.returncode, driven),
        (0, True),
        "driven by the control suite, not asserted here",
    )
    print()


def main() -> int:
    adr_2075()
    adr_2020()
    adr_2060()

    print("=" * 76)
    differ = [f for f in FINDINGS if not f[1]]
    print(f"{len(FINDINGS) - len(differ)} of {len(FINDINGS)} re-derivations match the corrected ADR figure")
    for label, _ok, detail in differ:
        print(f"  DIFFER  {label}: {detail}")
    if not FINDINGS:
        print("ABORT: zero re-derivations ran, which is not a pass")
        return 2
    return 1 if differ else 0


if __name__ == "__main__":
    sys.exit(main())
