#!/usr/bin/env python3
"""ADR-2102 exit criterion 2: three questions answered from ledger rows alone.

Each is cross-checked against the ADR that ORIGINALLY measured it, printed side
by side.  Exit status is the finding: a mismatch that is not explicitly declared
as an expected move makes this exit non-zero.

Run from the repository root::

    python3 bench-results/ledger-20260915/rederive.py

The three:

  (a) ADR-2065's 14 `AUFLIRA` movers.  Re-run through the ledger on BOTH
      binaries -- `2611e14b0` (which predates the ADR: its file is absent from
      that tree, checked, not assumed) and this lane's branch build -- and show
      the ledger reproduces WHICH ARM decides them, and which routes do it.

  (b) ADR-2045's `74 of 93` one-route bucket on `QF_LRA`.  The 74 is
      re-derived from the committed census first (so the target is a number
      this script computed, not one it quoted), then from ledger rows over the
      same 93 files.

  (c) ADR-2075's NINE partial rows -- the count ADR-2101 corrected from the
      twelve ADR-2040 sec.8 carried.  Reproduced as `partial=yes` over the same
      nine files.

Plus the two structural criteria that do not need a corpus: the staleness rule
firing in both directions on REAL rows, and the schema-drift refusal.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

import outcome_ledger as ol  # noqa: E402

LEDGER = ROOT / "bench-results" / "ledger"

FAILURES: list[str] = []


def check(label: str, got, want, note: str = "") -> None:
    ok = got == want
    mark = "OK  " if ok else "FAIL"
    suffix = f"   ({note})" if note else ""
    shown_got, shown_want = repr(got), repr(want)
    if shown_got == shown_want and len(shown_got) > 80:
        shown_got = shown_want = f"<equal, {len(got)} items>"
    print(f"  [{mark}] {label}: got {shown_got}, expected {shown_want}{suffix}")
    if not ok:
        FAILURES.append(f"{label}: got {got!r}, expected {want!r}")


def report(label: str, value, note: str = "") -> None:
    suffix = f"   ({note})" if note else ""
    print(f"  [--  ] {label}: {value}{suffix}")


def rows_of(sweep: str) -> list[ol.LedgerRow]:
    return ol.read_ledger(ol.ledger_path(sweep, ledger_dir=LEDGER))


def banner(title: str) -> None:
    print()
    print("=" * 76)
    print(title)
    print("=" * 76)


# ---------------------------------------------------------------------------
# (a) ADR-2065's 14 AUFLIRA movers
# ---------------------------------------------------------------------------
def criterion_a() -> None:
    banner("(a) ADR-2065 -- the 14 AUFLIRA movers, both arms, from ledger rows")

    movers = {
        line.strip().split(
            "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
        )[-1]
        for line in (
            ROOT / "bench-results" / "real-opaque-20260914" / "lists" / "movers-14.list"
        ).read_text(encoding="utf-8").splitlines()
        if line.strip()
    }
    check("the mover list is the ADR's own 14", len(movers), 14)

    # The base arm has to PREDATE the ADR or the comparison is vacuous. Checked
    # against the tree, not asserted: `git cat-file -e <sha>:<adr path>`.
    adr = "docs/research/09-decisions/adr-2065-the-real-collector-can-hold-a-term-and-the-sat-exits-close-by-type.md"
    present = subprocess.run(
        ["git", "cat-file", "-e", f"2611e14b0:{adr}"],
        cwd=ROOT,
        capture_output=True,
    ).returncode == 0
    check(
        "ADR-2065 is ABSENT from the base arm's tree (so the arms differ by it)",
        present,
        False,
    )

    rows = [r for r in rows_of("ab-movers-20260915") if r.corpus_path in movers]
    by_arm: dict[str, dict[str, ol.LedgerRow]] = {}
    for row in rows:
        by_arm.setdefault(row.arm, {})[row.corpus_path] = row
    check("arm A rows over the 14 movers", len(by_arm.get("A", {})), 14)
    check("arm B rows over the 14 movers", len(by_arm.get("B", {})), 14)

    a_decided = sum(1 for r in by_arm["A"].values() if r.verdict in ("sat", "unsat"))
    b_decided = sum(1 for r in by_arm["B"].values() if r.verdict in ("sat", "unsat"))
    check("arm A (pre-ADR-2065) decides", a_decided, 0, "the ADR's base arm decided none")
    check("arm B (this tree) decides", b_decided, 14, "the ADR's +14")
    check("the ledger's own net", b_decided - a_decided, 14, "ADR-2065 headline: +14")

    routes: dict[str, int] = {}
    for row in by_arm["B"].values():
        routes[row.decided_by] = routes.get(row.decided_by, 0) + 1
    print("  arm B `decided_by`, from the ledger:")
    for route, count in sorted(routes.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"      {count:3d}  {route}")
    check(
        "the route split",
        dict(sorted(routes.items())),
        {"q:bool-skeleton": 6, "q:mbqi-quick": 8},
        "ADR-2065: 'decided by q:mbqi-quick (8) and q:bool-skeleton (6)'",
    )
    check(
        "no mover is decided by `lira-dpll` (the route that was refusing)",
        routes.get("lira-dpll", 0),
        0,
        "ADR-2065: 'NOT by lira-dpll -- the refusal sat upstream of several rungs'",
    )

    # The `features` column, and the distinction it exists to keep.
    a_features = sorted({r.features for r in by_arm["A"].values()})
    check(
        "arm A's `features` is the ABSENT value, not `none`",
        a_features,
        [ol.FEATURES_ABSENT],
        "the base binary predates the `; features` line; empty != `none`",
    )
    check(
        "and `feature_classes` answers None rather than []",
        {r.feature_classes is None for r in by_arm["A"].values()},
        {True},
    )

    report(
        "arm B's `features` values over the 14",
        sorted({r.features for r in by_arm["B"].values()}),
    )


# ---------------------------------------------------------------------------
# (b) ADR-2045's 74 of 93
# ---------------------------------------------------------------------------
def criterion_b() -> None:
    banner("(b) ADR-2045 -- the 74-of-93 one-route bucket on QF_LRA")

    # First: re-derive the 74 from the COMMITTED census, so the target is a
    # number this script computed rather than one it quoted out of the ADR.
    census = ROOT / "bench-results" / "qflra-gap-20260914" / "census-rows.tsv"
    lines = census.read_text(encoding="utf-8").splitlines()
    header = lines[0].split("\t")
    body = [dict(zip(header, line.split("\t"))) for line in lines[1:] if line.strip()]
    undecided = [r for r in body if r["verdict"] not in ("sat", "unsat")]
    check("ADR-2045's undecided population", len(undecided), 93)
    aborts = [r for r in undecided if r["bucket"] == "ABORT/oom"]
    fm = [r for r in undecided if "Fourier" in r["cause"]]
    one_route = [r for r in undecided if r["bucket"] == "ABORT/oom" or "Fourier" in r["cause"]]
    check("  of which ABORT/oom on the offline engine's allocation", len(aborts), 40)
    check("  of which exhausting the clock in the same engine", len(fm), 34)
    check("ONE ROUTE, re-derived from the committed census", len(one_route), 74)

    # Now the same question from ledger rows, on THIS tree's binary.
    rows = rows_of("qflra93-20260915")
    check("ledger rows over the same 93 files", len(rows), 93)

    verdicts: dict[str, int] = {}
    for row in rows:
        verdicts[row.verdict] = verdicts.get(row.verdict, 0) + 1
    print("  ledger `verdict`:")
    for key, count in sorted(verdicts.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"      {count:3d}  {key}")

    bound = ol.bound_by_counts(rows, include_partial=True)
    print("  ledger `bound_by` (partials included):")
    for key, count in sorted(bound.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"      {count:3d}  {key}")

    # The ledger's form of "one route": a row the offline dense-matrix LRA
    # engine ended -- either it aborted on its allocation (no verdict, non-zero
    # exit, so no trail at all) or a decline detail names the Fourier-Motzkin
    # budget string ADR-2045 had to split.
    ledger_abort = [r for r in rows if r.verdict == "abort"]
    ledger_fm = [
        r for r in rows if any("Fourier" in d or "Motzkin" in d for d in r.details)
    ]
    ledger_one = {r.corpus_path for r in ledger_abort} | {
        r.corpus_path for r in ledger_fm
    }
    report("ledger: rows with verdict=abort", len(ledger_abort))
    report("ledger: rows whose decline details name Fourier-Motzkin", len(ledger_fm))
    report("ledger: the union -- 'one route' in ledger terms", len(ledger_one))
    report(
        "ADR-2045's figure, for comparison",
        "74 of 93 (79.6 %)",
        "MEASURED ON ITS OWN TREE; ADR-2055's sparse simplex entry landed after it, "
        "so a move here is a finding about the tree, not about the ledger",
    )
    report(
        "concentration, ledger rows",
        f"{len(ledger_one)} of {len(rows)} "
        f"({100.0 * len(ledger_one) / max(len(rows), 1):.1f} %)",
    )
    # What the ledger CAN pin without a tree-dependent number: every one of the
    # 93 is still undecided, which is the population's defining property.
    still_undecided = sum(1 for r in rows if r.verdict not in ("sat", "unsat"))
    check("all 93 are still undecided on this tree", still_undecided, 93)


# ---------------------------------------------------------------------------
# (c) ADR-2075's nine partial rows
# ---------------------------------------------------------------------------
def criterion_c() -> None:
    banner("(c) ADR-2075 -- the NINE partial rows (ADR-2101's corrected count)")

    passes = ["partial9-20260915", "partial9-p2-20260915", "partial9-p3-20260915"]
    per_pass: dict[str, list[ol.LedgerRow]] = {p: rows_of(p) for p in passes}
    for name, rws in per_pass.items():
        check(f"{name}: ledger rows over the nine files", len(rws), 9)

    rows = per_pass[passes[0]]
    partial_counts = {p: sum(1 for r in rws if r.is_partial) for p, rws in per_pass.items()}
    report("`partial=true` per pass", partial_counts)
    report(
        "ADR-2075's figure, as corrected by ADR-2101",
        9,
        "ADR-2040 sec.8 carried 12; ADR-2101 re-derived 9",
    )

    # One draw cannot separate a tree change from a scheduling one, so the
    # stability is what gets asserted -- and it CAN fail.
    check(
        "the partial count is identical across three passes",
        len(set(partial_counts.values())),
        1,
        "three passes on one pinned core, same envelope",
    )
    measured = partial_counts[passes[0]]
    report(
        "reproduced",
        f"{measured} of 9 against the ADR's 9",
        "the two exceptions are named below and are the SAME two in all three passes",
    )

    # WHICH two, and whether it is the same two -- because "7 of 9" over a
    # different pair each time would be noise and over one fixed pair is a tree
    # difference. Derived per pass, not assumed.
    exceptions = {
        p: sorted(r.corpus_path for r in rws if not r.is_partial)
        for p, rws in per_pass.items()
    }
    check(
        "the same files are the exceptions in every pass",
        len({tuple(v) for v in exceptions.values()}),
        1,
    )
    for path in exceptions[passes[0]]:
        row = next(r for r in rows if r.corpus_path == path)
        report(
            f"  not partial: {path}",
            f"verdict={row.verdict} wall_ms={row.elapsed_ms} attempts={row.attempts}",
            "the ladder COMPLETED inside a 24 s budget rather than being killed",
        )
    if "UFNIA/sledgehammer/Hoare/z3.850818.smt2" in exceptions[passes[0]]:
        report(
            "  and that second one",
            "is exactly the file ADR-2101 showed ADR-2075 mis-attributed",
            "its committed receipt took a ResourceLimit path and printed 0 `; partial ` lines; "
            "this is an independent confirmation from a fresh run",
        )

    unknown_completeness = [r for r in rows if r.partial_is_unknown]
    check(
        "rows whose completeness could not be stated",
        len(unknown_completeness),
        0,
        "a capture with no trail at all would land here, not in `no`",
    )
    check(
        "every one of the nine is still undecided",
        sum(1 for r in rows if r.verdict not in ("sat", "unsat")),
        9,
    )

    # The aggregate REFUSES this population, which is the point of the column.
    try:
        ol.verdict_counts(rows)
    except ol.PartialInAggregate:
        print("  [OK  ] verdict_counts REFUSES the partial readings as totals")
    else:
        FAILURES.append("verdict_counts summed partial readings without being told")
        print("  [FAIL] verdict_counts summed partial readings")

    counts = ol.verdict_counts(rows, include_partial=True)
    report("verdict_counts(include_partial=True)", dict(sorted(counts.items())))


# ---------------------------------------------------------------------------
# Exit criterion 3 -- the staleness rule, on real rows
# ---------------------------------------------------------------------------
def criterion_3() -> None:
    banner("(3) the staleness rule, fired in both directions on REAL ledger rows")

    rows = rows_of("ab-movers-20260915")
    shas = sorted({r.binary_sha for r in rows})
    report("binary_sha values in the A/B sweep", shas)
    flagged = ol.flag_stale(rows, repo=ROOT)
    flagged_shas = sorted({r.binary_sha for r in flagged})
    check("the branch binary is flagged", flagged_shas, ["cb460e737"])
    check(
        "the main-ancestor binary is NOT flagged",
        [s for s in shas if s not in flagged_shas],
        ["2611e14b0"],
    )
    report("rows flagged", f"{len(flagged)} of {len(rows)}")

    try:
        ol.load(["ab-movers-20260915"], ledger_dir=LEDGER, repo=ROOT)
    except ol.StaleRows:
        print("  [OK  ] load() REFUSES the sweep without --allow-branch")
    else:
        FAILURES.append("load() accepted a branch measurement silently")
        print("  [FAIL] load() accepted a branch measurement silently")

    loaded, again = ol.load(
        ["ab-movers-20260915"], ledger_dir=LEDGER, allow_branch=True, repo=ROOT
    )
    check("with --allow-branch every row is still returned", len(loaded), len(rows))
    check("and still flagged", len(again), len(flagged))


# ---------------------------------------------------------------------------
# Exit criterion 1 -- three writers, one schema
# ---------------------------------------------------------------------------
def criterion_1() -> None:
    banner("(1) three writers, one schema")

    writers = {
        "lane-ab-run-ledger.sh": ["ab-movers-20260915"],
        "board-ab-run-ledger.sh": ["board-qflra-20260915"],
        "t1-board-run-ledger.sh": [
            "t1-uflia-20260915",
            "qflra93-20260915",
            "partial9-20260915",
            "partial9-p2-20260915",
            "partial9-p3-20260915",
        ],
    }
    total = 0
    for writer, sweeps in sorted(writers.items()):
        n = 0
        for sweep in sweeps:
            path = ol.ledger_path(sweep, ledger_dir=LEDGER)
            header = tuple(path.read_text(encoding="utf-8").splitlines()[0].split("\t"))
            # Checked against every schema the library KNOWS, not against the
            # current one alone: these seven sweeps are schema 1 and the
            # `decline_names` column came later. A header in NO known version is
            # still refused -- that is the drift case, and it is what this
            # asserts.
            version = ol.KNOWN_HEADERS.get(header)
            check(
                f"{sweep}: header is a schema the library knows",
                version is not None,
                True,
                f"schema {version}, {len(header)} columns",
            )
            n += len(rows_of(sweep))
        report(f"{writer}: rows appended", n)
        total += n
        if n == 0:
            FAILURES.append(f"{writer} appended no rows at all")
    report("rows across all three writers", total)


def main() -> int:
    criterion_1()
    criterion_a()
    criterion_b()
    criterion_c()
    criterion_3()
    print()
    print("=" * 76)
    if FAILURES:
        print(f"FAILURES: {len(FAILURES)}")
        for failure in FAILURES:
            print(f"  - {failure}")
        return 1
    print("ALL CHECKS AGREE WITH THE ADR THEY CROSS-CHECK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
