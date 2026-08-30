#!/usr/bin/env python3
"""Execute the D3 counterexample-first falsification pack and gate on it
(roadmap phase D3,
`docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md`, ADR-0890).

D3's exit, verbatim: *the retained false-statement corpus is found before
producer dispatch; definition mutations alter at least one reference
observation; unexecutable definitions carry an explicit review obligation.*

This script is that sentence, executable, in three parts:

1. Every retained FALSE statement (`falsification_screen_fixtures.
   FALSE_STATEMENTS`) must be refuted -- the control must find at least one
   counterexample, or it is measuring nothing.
2. Every retained DEFINITION (`...DEFINITIONS`) must have its "correct"
   candidate match an INDEPENDENT reference over its whole bounded domain,
   and every attached mutation must MOVE at least one observation relative to
   that reference. A mutation that changes nothing is reported by name, not
   silently accepted -- that is the exact vacuity this pack exists to catch.
3. Every UNEXECUTABLE definition (`...REVIEW_OBLIGATIONS`) must carry a
   non-empty reason and a valid status; nothing may be silently exempt from
   both execution and obligation.

Ordering ("found before producer dispatch") is enforced against
`artifacts/falsification/receipts/*.json` (written by
`scripts/gen-falsification-screen.py`, one per screened target, BEFORE that
target may be dispatched) and `artifacts/falsification/dispatch-log.jsonl`
(one line per producer dispatch, real or demonstration). A dispatch entry is
rejected unless: a receipt exists for its target; that receipt's verdict is
`clear-for-dispatch` (never `reject-before-dispatch` or `review-required`);
and -- when both commits resolve in this repository's git history -- the
receipt's commit is an ancestor of, or equal to, the dispatch commit. That
last check is what makes "before dispatch" a property of `git log`, not of
prose: `git merge-base --is-ancestor <receipt-commit> <dispatch-commit>`.

Pinned outputs (`artifacts/falsification/false-statement-corpus.json`,
`.../definitions-registry.json`) are compared, not recomputed, when this
script is not given `--write`, so a silent drift in a model is caught rather
than reported as a fresh baseline -- the same discipline ADR-0752 applies to
S3's fixture pack.

Usage:

    python3 scripts/check-falsification-screen.py            # gate
    python3 scripts/check-falsification-screen.py --write     # re-pin + summary
    python3 scripts/check-falsification-screen.py --json      # for agents
"""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys
import time
from datetime import datetime, timezone

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

from falsification_screen_fixtures import (  # noqa: E402
    DEFINITIONS,
    FALSE_STATEMENTS,
    REVIEW_OBLIGATIONS,
    DefinitionReview,
    FalseStatement,
    ReviewObligation,
)

__all__ = ["DefinitionReview", "FalseStatement", "ReviewObligation"]

ROOT = pathlib.Path(__file__).resolve().parent.parent
FALS_DIR = ROOT / "artifacts" / "falsification"
CORPUS_PIN = FALS_DIR / "false-statement-corpus.json"
DEFS_PIN = FALS_DIR / "definitions-registry.json"
RECEIPTS_DIR = FALS_DIR / "receipts"
DISPATCH_LOG = FALS_DIR / "dispatch-log.jsonl"
SUMMARY = FALS_DIR / "screen-summary.md"

PACK_VERSION = 1

VALID_DEFINITION_VERDICTS = {"clear-for-dispatch", "reject-before-dispatch"}
VALID_REVIEW_STATUSES = {"open", "reviewed"}


# ---------------------------------------------------------------------------
# execution: turn the library's dataclasses into plain result dicts (pure
# data -- this is what guards operate on, and what the mutation-kill tests
# feed synthetically)
# ---------------------------------------------------------------------------


def run_false_statement(fx: FalseStatement) -> dict:
    t0 = time.time()
    out = fx.run()
    return {
        "id": fx.id,
        "kind": "false_statement",
        "family": fx.family,
        "statement": fx.statement,
        "provenance": fx.provenance,
        "executed": out.executed,
        "counterexamples": len(out.counterexamples),
        "first_counterexample": out.counterexamples[0] if out.counterexamples else "",
        "seconds": round(time.time() - t0, 3),
    }


def run_definition(d: DefinitionReview) -> dict:
    t0 = time.time()
    ref = d.run_reference_check()
    mutations = []
    for mut in d.mutations:
        mo = mut.run()
        mutations.append(
            {
                "id": mut.id,
                "description": mut.description,
                "executed": mo.executed,
                "moved": mo.moved,
                "first_divergence": mo.first_divergence,
            }
        )
    return {
        "id": d.id,
        "kind": "definition",
        "domain_note": d.domain_note,
        "provenance": d.provenance,
        "reference_note": d.reference_note,
        "witnesses": [{"args": list(w.args), "reason": w.reason} for w in d.witnesses],
        "executed": ref.executed,
        "mismatches": len(ref.counterexamples),
        "first_mismatch": ref.counterexamples[0] if ref.counterexamples else "",
        "mutations": mutations,
        "mutations_moved": sum(1 for m in mutations if m["moved"]),
        "mutations_vacuous": sum(1 for m in mutations if not m["moved"]),
        "seconds": round(time.time() - t0, 3),
    }


def run_review_obligation(r: ReviewObligation) -> dict:
    return {"id": r.id, "kind": "review_obligation", "reason": r.reason, "status": r.status}


# ---------------------------------------------------------------------------
# guards -- each independently deletable; scripts/tests/test_falsification_
# screen.py kills each with exactly one synthetic case.
# ---------------------------------------------------------------------------


def guard_corpus_nonempty(false_results: list[dict]) -> list[str]:
    """An empty false-statement corpus finds nothing before dispatch."""
    if not false_results:
        return ["the false-statement corpus is empty: 0 statements registered"]
    return []


def guard_zero_executed_false(false_results: list[dict]) -> list[str]:
    """ZERO EXECUTED CASES IS ALWAYS FAILURE, per statement and for the corpus."""
    bad = [f"{r['id']}: executed 0 cases" for r in false_results if r["executed"] == 0]
    if false_results and sum(r["executed"] for r in false_results) == 0:
        bad.append("the whole false-statement corpus executed 0 cases")
    return bad


def guard_false_statement_refuted(false_results: list[dict]) -> list[str]:
    """A retained false statement must be refuted -- a control finding no
    counterexample is measuring nothing, and is worse than no control at all,
    because it would clear a false proposal for producer dispatch."""
    return [
        f"{r['id']}: retained as FALSE but the control found no counterexample"
        for r in false_results
        if r["counterexamples"] == 0
    ]


def guard_definitions_nonempty(def_results: list[dict]) -> list[str]:
    if not def_results:
        return ["the definitions registry is empty: 0 definitions registered"]
    return []


def guard_zero_executed_definitions(def_results: list[dict]) -> list[str]:
    """ZERO EXECUTED CASES IS ALWAYS FAILURE for a definition's reference
    check too -- an unexecuted definition has no observation at all."""
    bad = [f"{r['id']}: reference check executed 0 cases" for r in def_results if r["executed"] == 0]
    if def_results and sum(r["executed"] for r in def_results) == 0:
        bad.append("the whole definitions registry executed 0 cases")
    return bad


def guard_correct_matches_reference(def_results: list[dict]) -> list[str]:
    """The CORRECT candidate must match the independent reference everywhere
    in its bounded domain. A mismatch here means the candidate this pack
    calls 'correct' is itself wrong, which would poison every mutation
    comparison built against it."""
    return [
        f"{r['id']}: the correct candidate disagrees with the reference at "
        f"{r['mismatches']} point(s): {r['first_mismatch']}"
        for r in def_results
        if r["mismatches"] > 0
    ]


def guard_definition_has_mutation(def_results: list[dict]) -> list[str]:
    """A definition with zero attached mutations has never been checked for
    sensitivity to a wrong implementation -- it is a definition nobody has
    tried to break."""
    return [f"{r['id']}: has 0 mutations -- never checked for a wrong implementation" for r in def_results if not r["mutations"]]


def guard_mutation_moves_observation(def_results: list[dict]) -> list[str]:
    """Every mutation must move at least one observation relative to the
    reference. A mutation that changes nothing on the whole bounded domain is
    the exact vacuity this pack exists to catch: it looks like a control and
    checks nothing."""
    bad = []
    for r in def_results:
        for m in r["mutations"]:
            if not m["moved"]:
                bad.append(
                    f"{r['id']}/{m['id']}: mutation moved NO observation on the bounded "
                    "domain -- vacuous mutation"
                )
    return bad


def guard_review_obligations_present(review_results: list[dict]) -> list[str]:
    """Every review obligation needs a real reason and a valid status."""
    bad = []
    for r in review_results:
        if not r["reason"].strip():
            bad.append(f"{r['id']}: review obligation has an empty reason")
        if r["status"] not in VALID_REVIEW_STATUSES:
            bad.append(f"{r['id']}: review obligation status {r['status']!r} is not one of {sorted(VALID_REVIEW_STATUSES)}")
    return bad


def guard_review_obligations_nonempty(review_results: list[dict]) -> list[str]:
    """At least one unexecutable definition must be tracked with an explicit
    obligation -- if this pack ever claims zero, that is a claim every
    definition is executable, which needs to be true, not merely unchecked."""
    if not review_results:
        return ["0 review obligations recorded: either every definition is executable (say so explicitly) or this list has silently gone stale"]
    return []


def guard_no_id_in_both_registries(def_results: list[dict], review_results: list[dict]) -> list[str]:
    """A definition may not be BOTH executed and exempted -- that would let a
    definition dodge the harder of the two checks by picking whichever one it
    happens to pass."""
    def_ids = {r["id"] for r in def_results}
    review_ids = {r["id"] for r in review_results}
    both = sorted(def_ids & review_ids)
    return [f"{i}: registered as BOTH an executable definition and a review obligation" for i in both]


# --- ordering: found before producer dispatch -------------------------------


def load_receipts() -> dict[str, dict]:
    out = {}
    if not RECEIPTS_DIR.exists():
        return out
    for p in sorted(RECEIPTS_DIR.glob("*.json")):
        try:
            data = json.loads(p.read_text())
        except json.JSONDecodeError:
            continue
        out[data.get("target_id", p.stem)] = data
    return out


def load_dispatch_log() -> list[dict]:
    if not DISPATCH_LOG.exists():
        return []
    out = []
    for line in DISPATCH_LOG.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        out.append(json.loads(line))
    return out


def is_ancestor_or_equal(older: str, newer: str, cwd: pathlib.Path = ROOT) -> bool | None:
    """True/False when both commits resolve in this repository's history,
    None when either does not resolve (e.g. a synthetic test SHA) -- callers
    must treat None as "not verifiable here", never as pass."""
    if older == newer:
        try:
            subprocess.run(
                ["git", "cat-file", "-e", older], cwd=cwd, capture_output=True, check=True
            )
            return True
        except subprocess.CalledProcessError:
            return None
    proc = subprocess.run(
        ["git", "merge-base", "--is-ancestor", older, newer],
        cwd=cwd,
        capture_output=True,
    )
    if proc.returncode in (0, 1):
        # 0 = is an ancestor, 1 = is not -- both mean git resolved both SHAs
        return proc.returncode == 0
    return None  # 128 etc: one of the SHAs does not exist here


def guard_dispatch_has_receipt(dispatch_entries: list[dict], receipts: dict[str, dict]) -> list[str]:
    """No dispatch may exist for a target with no receipt at all -- this is
    the structural half of "found before dispatch", independent of git."""
    bad = []
    for e in dispatch_entries:
        if e["target_id"] not in receipts:
            bad.append(f"dispatch of {e['target_id']!r} has NO screen receipt at all")
    return bad


def guard_dispatch_receipt_is_clear(dispatch_entries: list[dict], receipts: dict[str, dict]) -> list[str]:
    """A dispatch may only proceed against a receipt verdict of
    clear-for-dispatch -- never reject-before-dispatch or review-required."""
    bad = []
    for e in dispatch_entries:
        r = receipts.get(e["target_id"])
        if r is None:
            continue  # guard_dispatch_has_receipt already reports this
        if r.get("verdict") != "clear-for-dispatch":
            bad.append(
                f"dispatch of {e['target_id']!r} references a receipt with verdict "
                f"{r.get('verdict')!r}, not clear-for-dispatch"
            )
    return bad


def guard_dispatch_ordering(
    dispatch_entries: list[dict],
    receipts: dict[str, dict],
    ancestor_check=is_ancestor_or_equal,
) -> list[str]:
    """When both commits resolve in git history, the receipt's commit must be
    an ancestor of (or equal to) the dispatch commit -- "found before
    dispatch" verified as a property of git log, not of prose."""
    bad = []
    for e in dispatch_entries:
        r = receipts.get(e["target_id"])
        if r is None:
            continue
        receipt_commit = r.get("git_commit")
        dispatch_commit = e.get("commit")
        if not receipt_commit or not dispatch_commit:
            bad.append(f"dispatch of {e['target_id']!r} or its receipt is missing a git_commit")
            continue
        verdict = ancestor_check(receipt_commit, dispatch_commit)
        if verdict is False:
            bad.append(
                f"dispatch of {e['target_id']!r}: receipt commit {receipt_commit[:12]} is "
                f"NOT an ancestor of dispatch commit {dispatch_commit[:12]} -- screened AFTER dispatch"
            )
    return bad


def guard_receipt_ids_are_registered(receipts: dict[str, dict]) -> list[str]:
    """A receipt must name a target that actually exists in this pack --
    otherwise the census of "screened before dispatch" includes targets that
    were never really screened by anything current."""
    known = {fx.id for fx in FALSE_STATEMENTS} | {d.id for d in DEFINITIONS} | {r.id for r in REVIEW_OBLIGATIONS}
    return [f"receipt {tid!r} does not name a currently-registered target" for tid in receipts if tid not in known]


# ---------------------------------------------------------------------------
# pin drift
# ---------------------------------------------------------------------------


def guard_pin_drift(results: list[dict], pin: dict | None, key: str) -> list[str]:
    if pin is None:
        return [f"no pinned {key}: run with --write"]
    pinned = {p["id"]: p for p in pin.get("items", [])}
    bad = []
    fields = {
        "false_statement": ("executed", "counterexamples"),
        "definition": ("executed", "mismatches", "mutations_moved", "mutations_vacuous"),
    }
    for r in results:
        p = pinned.get(r["id"])
        if p is None:
            continue
        for field in fields.get(r["kind"], ()):
            if p.get(field) != r.get(field):
                bad.append(f"{r['id']}: pinned {field}={p.get(field)} but observed {r.get(field)}")
    return bad


def guard_pin_coverage(results: list[dict], pin: dict | None) -> list[str]:
    if pin is None:
        return []
    pinned = {p["id"] for p in pin.get("items", [])}
    seen = {r["id"] for r in results}
    bad = []
    for missing in sorted(pinned - seen):
        bad.append(f"pinned entry {missing} did not run -- deleted or renamed")
    for extra in sorted(seen - pinned):
        bad.append(f"entry {extra} ran but is not pinned -- run with --write")
    return bad


# ---------------------------------------------------------------------------
# reporting
# ---------------------------------------------------------------------------


def build_pin(items: list[dict], key: str) -> dict:
    return {
        "pack_version": PACK_VERSION,
        "generator": "scripts/check-falsification-screen.py",
        "note": "Generated. Do not hand-edit; run with --write.",
        "items": items,
    }


def write_summary(false_results, def_results, review_results, dispatch_entries, receipts, failures) -> None:
    w = []
    a = w.append
    a("# D3 counterexample-first falsification screen")
    a("")
    a("Generated by `scripts/check-falsification-screen.py`. Do not hand-edit.")
    a("")
    a(f"{len(false_results)} retained false statements, {len(def_results)} definitions "
      f"reviewed, {len(review_results)} review obligations, {len(receipts)} receipts, "
      f"{len(dispatch_entries)} dispatch log entries.")
    a("")
    a("## Retained false-statement corpus")
    a("")
    a("| id | family | executed | counterexamples | first counterexample |")
    a("|---|---|---:|---:|---|")
    for r in false_results:
        a(f"| `{r['id']}` | {r['family']} | {r['executed']} | {r['counterexamples']} | {r['first_counterexample']} |")
    a("")
    a("## Definitions reviewed")
    a("")
    a("| id | executed | mismatches | mutations moved / vacuous |")
    a("|---|---:|---:|---|")
    for r in def_results:
        a(f"| `{r['id']}` | {r['executed']} | {r['mismatches']} | {r['mutations_moved']} / {r['mutations_vacuous']} |")
    a("")
    a("## Review obligations (unexecutable definitions)")
    a("")
    a("| id | status | reason |")
    a("|---|---|---|")
    for r in review_results:
        a(f"| `{r['id']}` | {r['status']} | {r['reason'][:160]}{'…' if len(r['reason']) > 160 else ''} |")
    a("")
    a("## Dispatch-ordering ledger")
    a("")
    a(f"{len(dispatch_entries)} dispatch entries, {len(receipts)} receipts on file.")
    a("")
    if failures:
        a("## FAILURES")
        a("")
        for f in failures:
            a(f"- {f}")
    else:
        a("No failures on this run.")
    a("")
    SUMMARY.parent.mkdir(parents=True, exist_ok=True)
    SUMMARY.write_text("\n".join(w) + "\n")


def build_guard_table(
    false_results: list[dict],
    def_results: list[dict],
    review_results: list[dict],
    dispatch_entries: list[dict],
    receipts: dict[str, dict],
    corpus_pin: dict | None,
    defs_pin: dict | None,
    check_pins: bool,
) -> list[tuple[str, list[str]]]:
    """Every guard this gate runs, by NAME, in one place.

    This is the table `scripts/tests/test_falsification_screen.py` iterates
    to confirm every guard it names is actually wired in -- so a guard added
    with its own unit test but never added here (S3's own documented failure
    mode: 'three guards sat outside their suite's table until I noticed')
    fails a test immediately instead of silently never running.
    """
    table: list[tuple[str, list[str]]] = [
        ("corpus_nonempty", guard_corpus_nonempty(false_results)),
        ("zero_executed_false", guard_zero_executed_false(false_results)),
        ("false_statement_refuted", guard_false_statement_refuted(false_results)),
        ("definitions_nonempty", guard_definitions_nonempty(def_results)),
        ("zero_executed_definitions", guard_zero_executed_definitions(def_results)),
        ("correct_matches_reference", guard_correct_matches_reference(def_results)),
        ("definition_has_mutation", guard_definition_has_mutation(def_results)),
        ("mutation_moves_observation", guard_mutation_moves_observation(def_results)),
        ("review_obligations_present", guard_review_obligations_present(review_results)),
        ("review_obligations_nonempty", guard_review_obligations_nonempty(review_results)),
        ("no_id_in_both_registries", guard_no_id_in_both_registries(def_results, review_results)),
        ("dispatch_has_receipt", guard_dispatch_has_receipt(dispatch_entries, receipts)),
        ("dispatch_receipt_is_clear", guard_dispatch_receipt_is_clear(dispatch_entries, receipts)),
        ("dispatch_ordering", guard_dispatch_ordering(dispatch_entries, receipts)),
        ("receipt_ids_are_registered", guard_receipt_ids_are_registered(receipts)),
    ]
    if check_pins:
        table += [
            ("pin_drift_corpus", guard_pin_drift(false_results, corpus_pin, "false-statement-corpus.json")),
            ("pin_coverage_corpus", guard_pin_coverage(false_results, corpus_pin)),
            ("pin_drift_definitions", guard_pin_drift(def_results, defs_pin, "definitions-registry.json")),
            ("pin_coverage_definitions", guard_pin_coverage(def_results, defs_pin)),
        ]
    return table


GUARD_NAMES = [
    "corpus_nonempty",
    "zero_executed_false",
    "false_statement_refuted",
    "definitions_nonempty",
    "zero_executed_definitions",
    "correct_matches_reference",
    "definition_has_mutation",
    "mutation_moves_observation",
    "review_obligations_present",
    "review_obligations_nonempty",
    "no_id_in_both_registries",
    "dispatch_has_receipt",
    "dispatch_receipt_is_clear",
    "dispatch_ordering",
    "receipt_ids_are_registered",
    "pin_drift_corpus",
    "pin_coverage_corpus",
    "pin_drift_definitions",
    "pin_coverage_definitions",
]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true", help="regenerate the pins and summary")
    ap.add_argument("--check", action="store_true", help="explicit form of the default")
    ap.add_argument("--json", action="store_true", help="emit the full run as JSON")
    args = ap.parse_args()

    false_results = [run_false_statement(fx) for fx in FALSE_STATEMENTS]
    def_results = [run_definition(d) for d in DEFINITIONS]
    review_results = [run_review_obligation(r) for r in REVIEW_OBLIGATIONS]
    receipts = load_receipts()
    dispatch_entries = load_dispatch_log()

    corpus_pin = json.loads(CORPUS_PIN.read_text()) if CORPUS_PIN.exists() else None
    defs_pin = json.loads(DEFS_PIN.read_text()) if DEFS_PIN.exists() else None

    guard_table = build_guard_table(
        false_results, def_results, review_results, dispatch_entries, receipts,
        corpus_pin, defs_pin, check_pins=not args.write,
    )
    failures: list[str] = []
    for _name, bad in guard_table:
        failures += bad

    if args.json:
        print(
            json.dumps(
                {
                    "false_statements": false_results,
                    "definitions": def_results,
                    "review_obligations": review_results,
                    "dispatch_entries": dispatch_entries,
                    "receipts": receipts,
                    "failures": failures,
                },
                indent=2,
            )
        )
    else:
        for r in false_results:
            v = "REJECTED" if r["counterexamples"] else "NOT-REFUTED"
            print(f"{v:12s} {r['id']:48s} executed={r['executed']:6d} ce={r['counterexamples']:4d}")
        for r in def_results:
            v = "OK      " if r["mismatches"] == 0 else "MISMATCH"
            print(
                f"{v} {r['id']:26s} executed={r['executed']:5d} mismatches={r['mismatches']} "
                f"mutations moved={r['mutations_moved']} vacuous={r['mutations_vacuous']}"
            )
        for r in review_results:
            print(f"REVIEW   {r['id']:26s} status={r['status']}")
        print(
            f"false_statements={len(false_results)}|definitions={len(def_results)}|"
            f"review_obligations={len(review_results)}|receipts={len(receipts)}|"
            f"dispatch_entries={len(dispatch_entries)}"
        )

    if args.write:
        CORPUS_PIN.parent.mkdir(parents=True, exist_ok=True)
        CORPUS_PIN.write_text(json.dumps(build_pin(false_results, "false_statement"), indent=2) + "\n")
        DEFS_PIN.write_text(json.dumps(build_pin(def_results, "definition"), indent=2) + "\n")
        write_summary(false_results, def_results, review_results, dispatch_entries, receipts, failures)
        print(f"wrote {CORPUS_PIN.relative_to(ROOT)}, {DEFS_PIN.relative_to(ROOT)} and {SUMMARY.relative_to(ROOT)}")

    if failures:
        print("")
        for f in failures:
            print(f"FAIL  {f}")
        print(f"{len(failures)} failure(s)")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
