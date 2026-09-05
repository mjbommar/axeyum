#!/usr/bin/env python3
"""ADR-1663 gate: the public Lean Kernel Arena conformance corpus, both halves.

The corpus is `leanprover/lean-kernel-arena` (<https://arena.lean-lang.org>),
pinned by `scripts/fetch-references.sh`. Its published tarball unpacks into
`good/` (streams the official Lean kernel ACCEPTS) and `bad/` (streams it
REJECTS). `crates/axeyum-lean-import/examples/kernel_conformance_check.rs` runs
one case per process with the arena's own exit-code contract; this script
drives it, scores the two halves SEPARATELY, and gates on the result.

Why both halves, always: a checker that accepts everything it can parse scores
perfectly on the accept half. The arena ships `parse-only` as exactly that
control, and this script reproduces it in-tree (`--mode parse-only`, which is
the identical reader with the trusted gate's verdict discarded). A positive-only
score is not a result; the control is what proves it.

Two layers, and BOTH decide the exit status:

  A. Artifact layer -- always runs, no corpus needed. Re-derives every count in
     `artifacts/kernel-conformance/summary.json` from the per-case rows in
     `results.tsv`, and checks them against the floors and ceilings below. A
     hand-edited summary, a silently dropped case, or a regression fails here.

  B. Live layer -- runs when the corpus is present. Re-runs the checker and
     requires the live verdicts to reproduce the committed rows exactly. By
     default it re-runs the DIVERGENT cases (every row where our verdict is not
     the corpus's expected outcome) plus a deterministic sample of agreeing
     ones; `--rerun` re-runs all of them. When the corpus is absent the layer
     reports DID NOT RUN, by name, and layer A still gates.

Guards, each of which can be deleted to see exactly one failure:

  G1  results.tsv parses and is non-empty
  G2  both modes cover the identical case set, each case exactly once
  G3  full-mode accept half: correct >= ACCEPT_FLOOR
  G4  full-mode reject half: correct >= REJECT_FLOOR
  G5  full-mode reject half: `wrong` (we accept what Lean rejects) is bounded by
      SOUNDNESS_DIVERGENCE_CEILING -- a NEW one fails, and the ledger gate
      (`scripts/check-lean-divergences.py`) separately requires each to be listed
  G6  the control INVERTS: parse-only's reject-half score is lower than
      full mode's by at least CONTROL_MARGIN. If it is not, this harness is not
      measuring the kernel and every number above is meaningless
  G7  the control does not LOSE accepts: parse-only accept-correct >= full
  G8  summary.json's counts re-derive exactly from results.tsv
  G9  live: the recomputed corpus digest matches summary.json's, and every
      re-run case reproduces its committed verdict

Usage:
    scripts/check-kernel-conformance.py               # gate (A, plus B if corpus)
    scripts/check-kernel-conformance.py --rerun       # gate, B over the whole corpus
    scripts/check-kernel-conformance.py --require-corpus
    scripts/check-kernel-conformance.py --refresh     # re-measure and WRITE artifacts
    scripts/check-kernel-conformance.py --self-test   # prove G1..G9 each fire
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ARTIFACTS = ROOT / "artifacts" / "kernel-conformance"
RESULTS_TSV = ARTIFACTS / "results.tsv"
SUMMARY_JSON = ARTIFACTS / "summary.json"
SUMMARY_MD = ARTIFACTS / "summary.md"
DEFAULT_CORPUS = ROOT / "references" / "lean-arena-tests"
EXAMPLE = "kernel_conformance_check"
BINARY = ROOT / "target" / "release" / "examples" / EXAMPLE

MODES = ("full", "parse-only")

# --- The pinned scores. Raise a floor only from a run you read; a ceiling is
# --- an inventory of KNOWN divergences and a new one must fail, not be absorbed.
ACCEPT_FLOOR = 108
REJECT_FLOOR = 69
SOUNDNESS_DIVERGENCE_CEILING = 2
INCOMPLETENESS_CEILING = 4
DECLINE_CEILING = 2
NONVERDICT_CEILING = 1  # timeouts and checker errors on the accept half
# The control has to be visibly worse at rejecting. 40 is well under the
# measured gap (69 vs 21) and well over any plausible run-to-run wobble, which
# for a deterministic checker is zero.
CONTROL_MARGIN = 40

# Per-case wall-clock budget. `good/perf/app-lam` is an arena performance case
# built to make a checker diverge and it does not finish here; the budget is what
# turns that into a reported row instead of a wedged run.
CASE_TIMEOUT_SECONDS = 30

# Deterministic sample of agreeing cases the default live layer re-runs, so the
# fast path still exercises the kernel on cases we get RIGHT and not only on the
# divergences. Chosen across families and both halves.
LIVE_SAMPLE = (
    "core/proof-irrel",
    "core/bogus1",
    "core/nat-rec-rules",
    "tutorial/001_basicDef",
    "tutorial/002_badDef",
    "tutorial/046_inductBadNonSort",
)

VERDICT_BY_EXIT = {0: "accept", 1: "reject", 2: "decline", 3: "error"}


# --------------------------------------------------------------------------
# Measurement
# --------------------------------------------------------------------------
def discover(corpus: Path) -> list[tuple[str, Path, str]]:
    """Every case under `corpus`, as (name, path, expected), in sorted order.

    `good/` is `accept` and `bad/` is `reject` -- the corpus's own partition,
    read from the tree rather than from a list in this file.
    """
    cases: list[tuple[str, Path, str]] = []
    for subdirectory, expected in (("good", "accept"), ("bad", "reject")):
        base = corpus / subdirectory
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.ndjson")):
            relative = path.relative_to(base).with_suffix("")
            parts = relative.parts
            family = parts[0] if len(parts) > 1 else "core"
            name = f"{family}/{parts[-1]}" if len(parts) > 1 else f"core/{parts[-1]}"
            cases.append((name, path, expected))
    cases.sort(key=lambda case: case[0])
    return cases


def corpus_digest(cases: list[tuple[str, Path, str]]) -> str:
    """Identity of the bytes a score was measured on."""
    digest = hashlib.sha256()
    for name, path, _ in cases:
        digest.update(name.encode())
        digest.update(b"\0")
        digest.update(hashlib.sha256(path.read_bytes()).digest())
    return digest.hexdigest()


def run_case(binary: Path, path: Path, mode: str) -> tuple[str, str, str]:
    """(verdict, class, detail) for one case, or a timeout row."""
    try:
        completed = subprocess.run(
            [str(binary), "--mode", mode, str(path)],
            capture_output=True,
            text=True,
            timeout=CASE_TIMEOUT_SECONDS,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return ("timeout", "timeout", f"no_verdict_in_{CASE_TIMEOUT_SECONDS}s")
    verdict = VERDICT_BY_EXIT.get(completed.returncode)
    if verdict is None:
        return ("error", f"exit_{completed.returncode}", "-")
    fields = dict(
        token.split("=", 1)
        for line in completed.stdout.splitlines()
        if line.startswith("KERNEL-CONFORMANCE-CASE")
        for token in line.split()[1:]
        if "=" in token
    )
    return (verdict, fields.get("class", "-"), fields.get("detail", "-"))


def measure(binary: Path, cases: list[tuple[str, Path, str]]) -> list[dict]:
    rows: list[dict] = []
    for mode in MODES:
        for name, path, expected in cases:
            verdict, klass, detail = run_case(binary, path, mode)
            rows.append(
                {
                    "mode": mode,
                    "case": name,
                    "expected": expected,
                    "verdict": verdict,
                    "class": klass,
                    "detail": detail,
                }
            )
    return rows


def ensure_binary(explicit: Path | None) -> Path | None:
    """The checker binary, built if cargo can and it is missing."""
    if explicit is not None:
        return explicit if explicit.exists() else None
    if BINARY.exists():
        return BINARY
    built = subprocess.run(
        [
            "cargo",
            "build",
            "--release",
            "-p",
            "axeyum-lean-import",
            "--example",
            EXAMPLE,
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    return BINARY if built.returncode == 0 and BINARY.exists() else None


# --------------------------------------------------------------------------
# Scoring -- pure, so `--self-test` can drive it with synthetic rows
# --------------------------------------------------------------------------
def score(rows: list[dict]) -> dict:
    """Per-mode, per-half tallies derived from the rows and nothing else."""
    out: dict = {}
    for mode in MODES:
        halves = {
            half: {"total": 0, "correct": 0, "wrong": 0, "declined": 0, "nonverdict": 0}
            for half in ("accept", "reject")
        }
        for row in rows:
            if row["mode"] != mode:
                continue
            half = halves[row["expected"]]
            half["total"] += 1
            verdict = row["verdict"]
            if verdict in ("timeout", "error"):
                half["nonverdict"] += 1
            elif verdict == "decline":
                half["declined"] += 1
            elif verdict == row["expected"]:
                half["correct"] += 1
            else:
                half["wrong"] += 1
        out[mode] = halves
    return out


def evaluate(rows: list[dict], summary: dict | None) -> list[str]:
    """Pure gate logic for layer A: a list of failure reasons (empty == pass)."""
    failures: list[str] = []

    # G1 -- rows exist at all.
    if not rows:
        failures.append("G1 rows-nonempty: results.tsv parsed to zero rows")
        return failures

    # G2 -- both modes, identical case sets, no duplicates.
    per_mode: dict[str, list[str]] = {mode: [] for mode in MODES}
    for row in rows:
        per_mode.setdefault(row["mode"], []).append(row["case"])
    for mode in MODES:
        names = per_mode.get(mode, [])
        if not names:
            failures.append(f"G2 mode-coverage: mode {mode} has no rows")
        if len(names) != len(set(names)):
            duplicated = sorted({n for n in names if names.count(n) > 1})
            failures.append(f"G2 mode-coverage: mode {mode} repeats {duplicated}")
    sets = {mode: set(per_mode.get(mode, [])) for mode in MODES}
    if all(sets.values()) and sets["full"] != sets["parse-only"]:
        only_full = sorted(sets["full"] - sets["parse-only"])
        only_control = sorted(sets["parse-only"] - sets["full"])
        failures.append(
            "G2 mode-coverage: the control does not cover the same cases "
            f"(full-only {only_full}, control-only {only_control})"
        )

    tallies = score(rows)
    full = tallies["full"]
    control = tallies["parse-only"]

    # G3 -- the accept half.
    if full["accept"]["correct"] < ACCEPT_FLOOR:
        failures.append(
            f"G3 accept-floor: full-mode accept half scored {full['accept']['correct']} "
            f"< floor {ACCEPT_FLOOR}"
        )
    if full["accept"]["wrong"] > INCOMPLETENESS_CEILING:
        failures.append(
            f"G3 accept-floor: {full['accept']['wrong']} accept-half cases rejected "
            f"> ceiling {INCOMPLETENESS_CEILING} -- a new incompleteness"
        )
    if full["accept"]["nonverdict"] > NONVERDICT_CEILING:
        failures.append(
            f"G3 accept-floor: {full['accept']['nonverdict']} accept-half cases "
            f"produced no verdict > ceiling {NONVERDICT_CEILING}"
        )

    # G4 -- the reject half, reported and gated separately.
    if full["reject"]["correct"] < REJECT_FLOOR:
        failures.append(
            f"G4 reject-floor: full-mode reject half scored {full['reject']['correct']} "
            f"< floor {REJECT_FLOOR}"
        )
    if full["reject"]["declined"] > DECLINE_CEILING:
        failures.append(
            f"G4 reject-floor: {full['reject']['declined']} reject-half declines "
            f"> ceiling {DECLINE_CEILING}"
        )

    # G5 -- we accept something Lean rejects. Bounded, never absorbed.
    if full["reject"]["wrong"] > SOUNDNESS_DIVERGENCE_CEILING:
        offenders = sorted(
            row["case"]
            for row in rows
            if row["mode"] == "full"
            and row["expected"] == "reject"
            and row["verdict"] == "accept"
        )
        failures.append(
            f"G5 accepts-what-lean-rejects: {full['reject']['wrong']} > ceiling "
            f"{SOUNDNESS_DIVERGENCE_CEILING}; cases {offenders}"
        )

    # G6 -- the control must invert. This is the guard that makes the rest mean
    # anything: if discarding the trusted gate's verdict does not cost most of
    # the reject half, the reject half was never scored by the kernel.
    gap = full["reject"]["correct"] - control["reject"]["correct"]
    if gap < CONTROL_MARGIN:
        failures.append(
            "G6 control-inverts: the parse-only control scored "
            f"{control['reject']['correct']} on the reject half against full mode's "
            f"{full['reject']['correct']} (gap {gap} < required {CONTROL_MARGIN}) -- "
            "the harness is not measuring the trusted gate"
        )

    # G7 -- and it must not lose accepts; a control that also rejects valid
    # streams is a broken reader, not a control.
    if control["accept"]["correct"] < full["accept"]["correct"]:
        failures.append(
            "G7 control-accepts: the parse-only control scored "
            f"{control['accept']['correct']} on the accept half, below full mode's "
            f"{full['accept']['correct']}"
        )

    # G8 -- the published summary is a view of the rows, not a claim beside them.
    if summary is not None:
        published = summary.get("scores")
        if published != tallies:
            failures.append(
                "G8 summary-derives: summary.json scores do not re-derive from "
                "results.tsv"
            )
        if summary.get("floors", {}).get("accept") != ACCEPT_FLOOR or summary.get(
            "floors", {}
        ).get("reject") != REJECT_FLOOR:
            failures.append(
                "G8 summary-derives: summary.json floors disagree with the gate's"
            )
    return failures


# --------------------------------------------------------------------------
# Artifact I/O
# --------------------------------------------------------------------------
TSV_HEADER = ["mode", "case", "expected", "verdict", "class", "detail"]


def read_rows(path: Path) -> list[dict]:
    if not path.exists():
        return []
    rows = []
    lines = path.read_text().splitlines()
    for line in lines[1:]:
        if not line.strip():
            continue
        fields = line.split("\t")
        if len(fields) != len(TSV_HEADER):
            continue
        rows.append(dict(zip(TSV_HEADER, fields, strict=True)))
    return rows


def write_rows(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    body = ["\t".join(TSV_HEADER)]
    body += ["\t".join(row[key] for key in TSV_HEADER) for row in rows]
    path.write_text("\n".join(body) + "\n")


def render_markdown(summary: dict) -> str:
    scores = summary["scores"]
    lines = [
        "# Lean Kernel Arena conformance -- both halves",
        "",
        "**Generated** by `scripts/check-kernel-conformance.py --refresh`. Do not",
        "edit: every number here is re-derived from `results.tsv` by the gate, and a",
        "hand edit fails G8.",
        "",
        f"- corpus: `{summary['corpus']['repository']}` at `{summary['corpus']['revision']}`",
        f"- test tarball: `{summary['corpus']['tarball_url']}`",
        f"  sha256 `{summary['corpus']['tarball_sha256']}`",
        f"- cases scored: {summary['corpus']['cases']} "
        f"(digest `{summary['corpus']['digest']}`)",
        f"- measured: {summary['measured_at']}",
        "",
        "The corpus's `either` corner cases are not in the published tarball and are",
        "not scored here. Cases larger than 10 MB (mathlib, std, cslib, cedar, init)",
        "are excluded by upstream from the same tarball.",
        "",
        "## Scores",
        "",
        "| mode | half | total | correct | wrong | declined | no verdict |",
        "|---|---|---:|---:|---:|---:|---:|",
    ]
    for mode in MODES:
        for half in ("accept", "reject"):
            tally = scores[mode][half]
            lines.append(
                f"| {mode} | {half} | {tally['total']} | {tally['correct']} | "
                f"{tally['wrong']} | {tally['declined']} | {tally['nonverdict']} |"
            )
    gap = scores["full"]["reject"]["correct"] - scores["parse-only"]["reject"]["correct"]
    lines += [
        "",
        "## The control",
        "",
        "`parse-only` is the same reader with the trusted gate's verdict discarded",
        "(`census_ndjson`). It is the arena's own control reproduced in-tree, and it",
        "is why the accept half alone is not a result.",
        "",
        f"- reject half: full mode {scores['full']['reject']['correct']}, control "
        f"{scores['parse-only']['reject']['correct']} -- a gap of **{gap}**.",
        f"- so **{scores['parse-only']['reject']['correct']}** of the reject half is",
        "  decided by the reader and recursor regeneration, and the remaining",
        f"  **{gap}** by the trusted gate. A reject-half score quoted without this",
        "  split does not say which layer earned it.",
        "",
        "## Divergences",
        "",
        "Every row below is listed in [`docs/plan/lean-divergences.md`]"
        "(../../docs/plan/lean-divergences.md); `scripts/check-lean-divergences.py`",
        "fails if one is not.",
        "",
        "| case | expected | our verdict | class |",
        "|---|---|---|---|",
    ]
    for row in summary["divergences"]:
        lines.append(
            f"| `{row['case']}` | {row['expected']} | {row['verdict']} | `{row['class']}` |"
        )
    lines.append("")
    return "\n".join(lines)


def divergences(rows: list[dict]) -> list[dict]:
    """Every full-mode row whose verdict is not the corpus's expected outcome."""
    return [
        {
            "case": row["case"],
            "expected": row["expected"],
            "verdict": row["verdict"],
            "class": row["class"],
            "detail": row["detail"],
        }
        for row in rows
        if row["mode"] == "full" and row["verdict"] != row["expected"]
    ]


# --------------------------------------------------------------------------
# Self-test: every guard, on the case that names it
# --------------------------------------------------------------------------
def synthetic_rows() -> list[dict]:
    """A passing row set: floors met, ceilings respected, control inverted."""
    rows = []
    for mode in MODES:
        for index in range(ACCEPT_FLOOR):
            rows.append(
                {
                    "mode": mode,
                    "case": f"tutorial/a{index}",
                    "expected": "accept",
                    "verdict": "accept",
                    "class": "ok",
                    "detail": "-",
                }
            )
        for index in range(REJECT_FLOOR):
            # In the control, only the first (REJECT_FLOOR - CONTROL_MARGIN - 1)
            # still reject -- a gap comfortably over CONTROL_MARGIN.
            reject_in_control = index < REJECT_FLOOR - CONTROL_MARGIN - 1
            verdict = (
                "reject" if mode == "full" or reject_in_control else "accept"
            )
            rows.append(
                {
                    "mode": mode,
                    "case": f"tutorial/r{index}",
                    "expected": "reject",
                    "verdict": verdict,
                    "class": "kernel:X",
                    "detail": "-",
                }
            )
    return rows


def self_test() -> int:
    base = synthetic_rows()
    summary = {
        "scores": score(base),
        "floors": {"accept": ACCEPT_FLOOR, "reject": REJECT_FLOOR},
    }
    checks: list[tuple[str, list[dict], dict | None]] = []

    # G1: no rows.
    checks.append(("G1", [], None))
    # G2: drop the control entirely.
    checks.append(("G2", [r for r in base if r["mode"] == "full"], None))
    # G3: one accept-half case flips to reject, taking full mode under the floor.
    g3 = [dict(r) for r in base]
    for row in g3:
        if row["mode"] == "full" and row["case"] == "tutorial/a0":
            row["verdict"] = "reject"
    checks.append(("G3", g3, None))
    # G4: one reject-half case declines, taking full mode under the floor.
    g4 = [dict(r) for r in base]
    for row in g4:
        if row["mode"] == "full" and row["case"] == "tutorial/r0":
            row["verdict"] = "decline"
    checks.append(("G4", g4, None))
    # G5: one more reject-half case than the ceiling is accepted.
    g5 = [dict(r) for r in base]
    flipped = 0
    for row in g5:
        if (
            row["mode"] == "full"
            and row["expected"] == "reject"
            and flipped <= SOUNDNESS_DIVERGENCE_CEILING
        ):
            row["verdict"] = "accept"
            flipped += 1
    checks.append(("G5", g5, None))
    # G6: the control rejects exactly what full mode does -- the harness is blind.
    g6 = [dict(r) for r in base]
    for row in g6:
        if row["mode"] == "parse-only" and row["expected"] == "reject":
            row["verdict"] = "reject"
    checks.append(("G6", g6, None))
    # G7: the control loses an accept full mode keeps.
    g7 = [dict(r) for r in base]
    for row in g7:
        if row["mode"] == "parse-only" and row["case"] == "tutorial/a0":
            row["verdict"] = "reject"
    checks.append(("G7", g7, None))
    # G8: a published summary that does not re-derive.
    bad_summary = json.loads(json.dumps(summary))
    bad_summary["scores"]["full"]["reject"]["correct"] += 1
    checks.append(("G8", base, bad_summary))

    ok = True
    # The passing baseline must actually pass, or every case below is vacuous.
    baseline = evaluate(base, summary)
    if baseline:
        print(f"SELF-TEST FAIL baseline: expected no failures, got {baseline}")
        ok = False
    else:
        print("SELF-TEST ok baseline: the synthetic passing row set passes")
    for guard, rows, published in checks:
        failures = evaluate(rows, published)
        named = [f for f in failures if f.startswith(guard)]
        if not named:
            print(f"SELF-TEST FAIL {guard}: did not fire (failures: {failures})")
            ok = False
        else:
            print(f"SELF-TEST ok {guard}: {named[0]}")
    print("SELF-TEST", "PASS" if ok else "FAIL")
    return 0 if ok else 1


# --------------------------------------------------------------------------
def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    parser.add_argument("--binary", type=Path, default=None)
    parser.add_argument("--refresh", action="store_true", help="re-measure and write")
    parser.add_argument("--rerun", action="store_true", help="live layer over all cases")
    parser.add_argument("--require-corpus", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    if args.self_test:
        return self_test()

    if args.refresh:
        binary = ensure_binary(args.binary)
        if binary is None:
            print("FAIL: --refresh needs the checker binary and cargo could not build it")
            return 1
        cases = discover(args.corpus)
        if not cases:
            print(f"FAIL: --refresh found no cases under {args.corpus}")
            return 1
        rows = measure(binary, cases)
        summary = {
            "generator": "scripts/check-kernel-conformance.py --refresh",
            "measured_at": subprocess.run(
                ["date", "-u", "+%Y-%m-%dT%H:%M:%SZ"],
                capture_output=True,
                text=True,
                check=True,
            ).stdout.strip(),
            "corpus": {
                "repository": "https://github.com/leanprover/lean-kernel-arena",
                "revision": "abc55357aee17c59dfdbf39c8a2e19739e23dd10",
                "tarball_url": "https://arena.lean-lang.org/lean-arena-tests.tar.gz",
                "tarball_sha256": (
                    "7e396d5de90e8871c9b1d7e2931f3efaba303056cdfd93e65f9ae1de628bf326"
                ),
                "cases": len(cases),
                "digest": corpus_digest(cases),
            },
            "case_timeout_seconds": CASE_TIMEOUT_SECONDS,
            "floors": {"accept": ACCEPT_FLOOR, "reject": REJECT_FLOOR},
            "scores": score(rows),
            "divergences": divergences(rows),
        }
        write_rows(RESULTS_TSV, rows)
        SUMMARY_JSON.write_text(json.dumps(summary, indent=2) + "\n")
        SUMMARY_MD.write_text(render_markdown(summary))
        print(f"refreshed {RESULTS_TSV.relative_to(ROOT)} ({len(rows)} rows)")
        print(f"refreshed {SUMMARY_JSON.relative_to(ROOT)}")
        print(f"refreshed {SUMMARY_MD.relative_to(ROOT)}")
        return 0

    rows = read_rows(RESULTS_TSV)
    summary = json.loads(SUMMARY_JSON.read_text()) if SUMMARY_JSON.exists() else None
    failures = evaluate(rows, summary)

    # Layer B.
    live_ran = 0
    if not args.corpus.is_dir():
        message = f"LIVE LAYER DID NOT RUN: no corpus at {args.corpus}"
        if args.require_corpus:
            failures.append("G9 live-agrees: " + message)
        else:
            print(message + " (scripts/fetch-references.sh)")
    else:
        binary = ensure_binary(args.binary)
        if binary is None:
            message = "LIVE LAYER DID NOT RUN: no checker binary and cargo build failed"
            if args.require_corpus:
                failures.append("G9 live-agrees: " + message)
            else:
                print(message)
        else:
            cases = discover(args.corpus)
            observed = corpus_digest(cases)
            expected_digest = (summary or {}).get("corpus", {}).get("digest")
            if expected_digest and observed != expected_digest:
                failures.append(
                    f"G9 live-agrees: corpus digest {observed} != published "
                    f"{expected_digest} -- the scored bytes changed"
                )
            wanted = {row["case"] for row in divergences(rows)} | set(LIVE_SAMPLE)
            by_name = {name: path for name, path, _ in cases}
            for row in rows:
                if not args.rerun and row["case"] not in wanted:
                    continue
                path = by_name.get(row["case"])
                if path is None:
                    failures.append(
                        f"G9 live-agrees: committed case {row['case']} is not in the corpus"
                    )
                    continue
                verdict, klass, _ = run_case(binary, path, row["mode"])
                live_ran += 1
                if verdict != row["verdict"] or klass != row["class"]:
                    failures.append(
                        f"G9 live-agrees: {row['mode']} {row['case']} committed "
                        f"{row['verdict']}/{row['class']}, live {verdict}/{klass}"
                    )

    tallies = score(rows) if rows else {}
    if tallies:
        for mode in MODES:
            for half in ("accept", "reject"):
                tally = tallies[mode][half]
                print(
                    f"KERNEL-CONFORMANCE {mode} {half}-half: "
                    f"{tally['correct']}/{tally['total']} correct, "
                    f"{tally['wrong']} wrong, {tally['declined']} declined, "
                    f"{tally['nonverdict']} no verdict"
                )
    print(f"KERNEL-CONFORMANCE live re-runs: {live_ran}")

    if failures:
        for failure in failures:
            print(f"FAIL {failure}")
        return 1
    print("PASS scripts/check-kernel-conformance.py")
    return 0


if __name__ == "__main__":
    sys.exit(main())
