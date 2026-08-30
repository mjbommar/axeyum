#!/usr/bin/env python3
"""S0 of the trusted-library safety roadmap: measure facts x protections.

WHY THIS EXISTS. `docs/plan/trusted-library-safety-roadmap-2026-08-30.md`
(ADR-0717) names five risks that kernel acceptance alone does not cover:
kernel unsoundness, statement error, vacuity, contamination, false evidence.
An empty `axiom_footprint` addresses only part of two of them. Before any of
S1-S6 can be designed honestly, somebody has to say -- with a denominator --
which protections each proved ledger row actually carries.

WHAT IT MEASURES, AND WHAT IT REFUSES TO INFER. Every column below is read
from the fact file itself or from a ledger-wide manifest that names the fact.
Nothing is inferred from a neighbouring fact, from a family, or from the fact
being "the same kind of thing" as one that is covered. That rule is the point:
this repository has repeatedly credited a row with a protection a sibling had.

A NOTE ON WHAT A `yes` MEANS. It means the protection is PRESENT, not that it
is strong. In particular `env_footprint` is very often a prelude-wide command
shared with hundreds of other facts; `checker_fanout_max` records that, and a
row whose only footprint evidence is shared with 462 siblings is not carrying
an independent check. The summary reports both.

Usage:
    python3 scripts/gen-safety-matrix.py            # regenerate artifacts
    python3 scripts/gen-safety-matrix.py --check    # fail on drift or control loss
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
FACTS = ROOT / "artifacts/facts"
OUT_DIR = ROOT / "artifacts/safety-matrix"
MATRIX_TSV = OUT_DIR / "safety-matrix.tsv"
SUMMARY_MD = OUT_DIR / "safety-matrix-summary.md"

SETTLED = {"proved"}

# ---------------------------------------------------------------------------
# ledger-wide manifests that name individual facts.  Read, never inferred.
# ---------------------------------------------------------------------------

STATEMENT_PINS = ROOT / "artifacts/ontology/settled-fact-statement-pins.json"


def statement_pinned_ids() -> set[str]:
    """Fact ids whose `formal.statement` SHA-256 is pinned against silent drift.

    `scripts/check-settled-fact-statements.py` PASSES for a settled fact that is
    absent from this manifest -- absence is read as "newly settled", not as a
    violation -- so membership here is the only thing that distinguishes a
    protected statement from an unprotected one.
    """
    if not STATEMENT_PINS.exists():
        return set()
    data = json.loads(STATEMENT_PINS.read_text())
    return {row["fact_id"] for row in data.get("pins", []) if "fact_id" in row}


# ---------------------------------------------------------------------------
# checker_command classifiers
# ---------------------------------------------------------------------------

# A command whose exit status can depend on WHAT THE RUN FOUND rather than on
# the run completing.  Audited shapes (CLAUDE.md, 2026-08-25 re-measurement).
DISCRIMINATING = (
    re.compile(r"grep\s+-[A-Za-z]*c"),           # counting grep consuming the pipe
    re.compile(r"--require-axiom-free"),
    re.compile(r"--expect-axioms"),
    re.compile(r"--check(?![A-Za-z-])"),
    re.compile(r"\bdiff\b"),
    re.compile(r"\btest\s+\""),                  # test "$(...)" -ge N
    re.compile(r"--require-"),
)

ENV_FOOTPRINT = re.compile(
    r"(nat_axiom_inventory|prelude_axiom_inventory|ipc_soundness_inventory)"
    r"[^\n]*--require-axiom-free"
)
PER_THEOREM_FOOTPRINT = re.compile(
    r"(theorem_axiom_footprint|footprint_closure_audit|--expect-axioms"
    r"|check-imported-fact-lean-axioms)"
)
DEPENDENCY_CLOSURE = re.compile(
    r"(footprint_closure_audit|dependency-audit|check-fact-depends-derived"
    r"|kernel_declaration_projection)"
)
REAL_LEAN_REPLAY = re.compile(
    r"(real_lean_[a-z_]*replay|lean4export|check-lean-gate|elan|AXEYUM_LEAN_BIN"
    r"|check-imported-fact-lean-axioms|infeasibility_farkas_lean)"
)
NEGATIVE_CONTROL = re.compile(
    r"(negative-control|negative_control|mutation|check-adopted-controls"
    r"|scripts/tests/|-controls\.sh|_controls\.py|must-decline)"
)
SEMANTIC_KINDS = {
    "exhaustive-enumeration",
    "witness-replay",
    "instance-pin",
    "unsat-certificate",
    "cube-cover",
    "cube-tree-cover",
    "published-value-replication",
}


def is_footprint_row(ev: dict) -> bool:
    """Is this evidence row an AXIOM FOOTPRINT record wearing another `kind`?

    Measured on this ledger: 1,800 rows carry `kind: exhaustive-enumeration`
    and 100 carry `kind: instance-pin` while their `supports` reads
    `axiom_footprint: [] -- ...`.  Nothing was enumerated and no instance was
    pinned; the row records that `Kernel::axiom_footprint` came back empty.

    So the `kind` enum has lost its discriminating power on this ledger in
    exactly the way the schema's own note says `check_status: checked` did.  A
    census that read `kind` at face value would credit 1,900 rows with semantic
    falsification they do not carry -- the single largest over-count available
    here, and the reason this predicate exists.
    """
    supports = (ev.get("supports") or "")
    return "axiom_footprint" in supports[:48].lower()


# The historical fallback used by `theorem_of` in `check-fact-depends-derived.py`
# and four sibling scripts: the first dotted name in the fact's own checker
# commands.  Reproduced here ONLY to measure how much of the ledger's subject
# binding rests on it, never to credit a protection.
EXTRACT_RE = re.compile(r"\b([A-Z][A-Za-z0-9]*(?:\.[A-Za-z0-9_']+)+)")


def extracted_subject(fact: dict) -> str | None:
    """The subject a regex would guess when no explicit binding exists.

    `theorem_of`'s own docstring calls this "demonstrably NOT reliable in
    general" and names two ledger rows it got wrong.  This census therefore
    reports it as a separate, weaker column rather than folding it into
    `kernel_theorem`.
    """
    if "kernel_theorem" in (fact.get("formal") or {}):
        return None
    for ev in fact.get("evidence", []):
        found = EXTRACT_RE.search(ev.get("checker_command") or "")
        if found:
            return found.group(1)
    return None


def subject_of(fact: dict) -> str | None:
    """The fact's own kernel declaration, taken ONLY from explicit bindings.

    Deliberately does not fall back to "first dotted name mentioned in the
    evidence" the way `theorem_of` does elsewhere: this census must not credit a
    fact with a subject-specific checker on the strength of a regex guess.
    """
    formal = fact.get("formal", {})
    explicit = formal.get("kernel_theorem")
    if isinstance(explicit, str) and explicit:
        return explicit
    for ev in fact.get("evidence", []):
        decls = ev.get("kernel_declarations")
        if isinstance(decls, list) and len(decls) == 1:
            return decls[0]
        one = ev.get("kernel_declaration")
        if isinstance(one, str) and one:
            return one
    return None


COLUMNS = [
    "exact_statement",
    "kernel_theorem",
    "per_theorem_footprint",
    "env_footprint",
    "circularity",
    "semantic_falsification",
    "mutation_control",
    "independent_replay",
    "coverage_bearing_checker",
]


def load_facts() -> list[dict]:
    return [json.loads(p.read_text()) for p in sorted(FACTS.glob("*.json"))]


def build_fanout(proved: list[dict]) -> dict[str, set[str]]:
    fan: dict[str, set[str]] = collections.defaultdict(set)
    for fact in proved:
        for ev in fact.get("evidence", []):
            cmd = (ev.get("checker_command") or "").strip()
            if cmd:
                fan[cmd].add(fact["id"])
    return fan


def classify(fact: dict, pinned: set[str], fan: dict[str, set[str]]) -> dict:
    subject = subject_of(fact)
    cmds = [(ev, (ev.get("checker_command") or "").strip())
            for ev in fact.get("evidence", [])]
    semantic_rows = [
        ev for ev, _ in cmds
        if ev.get("kind") in SEMANTIC_KINDS and not is_footprint_row(ev)
    ]
    mislabelled = sum(
        1 for ev, _ in cmds
        if ev.get("kind") in SEMANTIC_KINDS and is_footprint_row(ev)
    )

    def any_cmd(rx) -> bool:
        return any(cmd and rx.search(cmd) for _, cmd in cmds)

    # The fact schema's own rule: "Two entries that share an implementation are
    # ONE check wearing two names; the value of the list is independence, not
    # length."  A row naming the PRODUCING run as one of its checkers is not
    # re-derived twice -- the production is not a re-derivation of itself.
    # `validate-facts.py` counts such a row toward "re-derived by 2+
    # independent checkers", which is why this is measured separately.
    producer_named = any(
        "producing" in name.lower() or "producing-build" in name.lower()
        for ev, _ in cmds
        for name in (ev.get("checkers") or [])
    )
    multi_checker = any(len(ev.get("checkers") or []) >= 2 for ev, _ in cmds)

    guessed = extracted_subject(fact)
    discriminating_subject = False
    discriminating_guess = False
    for _, cmd in cmds:
        if not cmd:
            continue
        if not any(rx.search(cmd) for rx in DISCRIMINATING):
            continue
        flat = cmd.replace("\\", "")
        if subject and subject in flat:
            discriminating_subject = True
        if guessed and guessed in flat:
            discriminating_guess = True

    fanouts = [len(fan.get(cmd, {fact["id"]})) for _, cmd in cmds if cmd]

    row = {
        "id": fact["id"],
        "route": fact.get("proof_route", ""),
        "curation": fact.get("provenance", {}).get("curation", ""),
        "language": fact.get("formal", {}).get("language", ""),
        "subject": subject or "",
        "n_evidence": len(cmds),
        "n_checkers": sum(1 for _, c in cmds if c),
        "checker_fanout_max": max(fanouts) if fanouts else 0,
        "checker_fanout_min": min(fanouts) if fanouts else 0,
        "exact_statement": fact["id"] in pinned,
        "kernel_theorem": subject is not None,
        "per_theorem_footprint": any_cmd(PER_THEOREM_FOOTPRINT),
        "env_footprint": any_cmd(ENV_FOOTPRINT),
        "circularity": any_cmd(DEPENDENCY_CLOSURE),
        "semantic_falsification": bool(semantic_rows),
        "footprint_rows_mislabelled": mislabelled,
        "mutation_control": any_cmd(NEGATIVE_CONTROL),
        "independent_replay": any_cmd(REAL_LEAN_REPLAY),
        "coverage_bearing_checker": discriminating_subject,
        "checkers_name_producer": producer_named,
        "checkers_multi": multi_checker,
        "subject_guessed": guessed or "",
        "coverage_by_guess_only": bool(discriminating_guess and not discriminating_subject),
    }
    row["protection_count"] = sum(1 for c in COLUMNS if row[c])
    return row


# ---------------------------------------------------------------------------
# self-controls: an empty result is not a negative result
# ---------------------------------------------------------------------------

# Each control names a fact that MUST land in the given cell.  If a classifier
# silently stops matching, the census fails here rather than reporting a
# cheerful zero.  Each was verified by hand against the fact file.  Both
# polarities are represented on purpose: a control pack of only `True` rows
# cannot catch a classifier that has started saying yes to everything.
POSITIVE_CONTROLS = [
    ("F:logic-and-left", "env_footprint", True),
    ("F:logic-and-left", "coverage_bearing_checker", True),
    ("F:logic-and-left", "independent_replay", False),
    ("F:logic-and-left", "semantic_falsification", False),
    ("F:nat-sumrange-add", "kernel_theorem", True),
    ("F:nat-sumrange-add", "exact_statement", False),
    # `F:acc-inv` carries an `exhaustive-enumeration` row whose `supports` is
    # `axiom_footprint: [] -- ...`.  Reading `kind` at face value would call it
    # semantic falsification.  This control is what keeps that fix alive.
    ("F:acc-inv", "semantic_falsification", False),
    # ... while a genuine enumeration row still counts.
    ("F:alternating-binomial-row-sum-zero", "semantic_falsification", True),
    # The generated template names `producing-build (Kernel::add_declaration)`
    # as one of two `checkers`. Both polarities pinned so the predicate cannot
    # silently start saying yes (or no) to everything.
    ("F:nat-sumrange-add", "checkers_name_producer", True),
    ("F:alternating-binomial-row-sum-zero", "checkers_name_producer", False),
]


def run_controls(by_id: dict[str, dict]) -> list[str]:
    failures = []
    for fact_id, column, expected in POSITIVE_CONTROLS:
        row = by_id.get(fact_id)
        if row is None:
            failures.append(f"control subject missing from census: {fact_id}")
            continue
        if bool(row[column]) is not expected:
            failures.append(
                f"control failed: {fact_id}.{column} is {row[column]!r}, "
                f"expected {expected!r}"
            )
    return failures


def render_tsv(rows: list[dict]) -> str:
    head = [
        "fact_id", "route", "curation", "language", "subject",
        "n_evidence", "n_checkers", "checker_fanout_min", "checker_fanout_max",
        *COLUMNS, "protection_count", "subject_guessed", "coverage_by_guess_only",
        "checkers_multi", "checkers_name_producer",
    ]
    lines = ["\t".join(head)]
    for r in rows:
        lines.append("\t".join([
            r["id"], r["route"], r["curation"] or "-", r["language"],
            r["subject"] or "-",
            str(r["n_evidence"]), str(r["n_checkers"]),
            str(r["checker_fanout_min"]), str(r["checker_fanout_max"]),
            *("yes" if r[c] else "no" for c in COLUMNS),
            str(r["protection_count"]),
            r["subject_guessed"] or "-",
            "yes" if r["coverage_by_guess_only"] else "no",
            "yes" if r["checkers_multi"] else "no",
            "yes" if r["checkers_name_producer"] else "no",
        ]))
    return "\n".join(lines) + "\n"


def render_summary(rows: list[dict], fan: dict[str, set[str]],
                   all_facts: list[dict]) -> str:
    n = len(rows)
    out: list[str] = []
    w = out.append
    w("# Safety matrix census (S0)")
    w("")
    w("Generated by `scripts/gen-safety-matrix.py`. Do not hand-edit.")
    w("")
    w(f"Ledger: {len(all_facts)} facts, {n} `proved`. Every proved fact appears")
    w("exactly once in `safety-matrix.tsv`.")
    w("")
    w("A `yes` means the protection is PRESENT for this row, not that it is")
    w("strong; `checker_fanout_max` says how many other facts share its widest")
    w("checker.")
    w("")

    w("## Protection coverage")
    w("")
    w("| protection | proved facts with it | share |")
    w("|---|---:|---:|")
    for c in COLUMNS:
        k = sum(1 for r in rows if r[c])
        w(f"| `{c}` | {k} / {n} | {100.0 * k / n:.1f}% |")
    w("")

    w("## Protections per fact")
    w("")
    hist = collections.Counter(r["protection_count"] for r in rows)
    w("| protections held | facts |")
    w("|---:|---:|")
    for k in sorted(hist):
        w(f"| {k} | {hist[k]} |")
    w("")

    w("## Checker fan-out")
    w("")
    sizes = collections.Counter(len(v) for v in fan.values())
    biggest = sorted(fan.items(), key=lambda kv: (-len(kv[1]), kv[0]))[:8]
    w(f"{len(fan)} distinct `checker_command`s cover {n} proved facts.")
    w("")
    w("| facts sharing one command | commands |")
    w("|---:|---:|")
    for k in sorted(sizes):
        w(f"| {k} | {sizes[k]} |")
    w("")
    w("Largest fan-outs:")
    w("")
    w("| facts | command |")
    w("|---:|---|")
    for cmd, ids in biggest:
        short = cmd if len(cmd) <= 110 else cmd[:107] + "..."
        short = short.replace("|", "\\|").replace("\n", " ")
        w(f"| {len(ids)} | `{short}` |")
    w("")

    w("## Thin spots")
    w("")
    only_kernel = [r for r in rows if r["protection_count"] <= 2]
    w(f"- {len(only_kernel)} / {n} proved facts hold two protections or fewer.")
    no_subject_checker = [r for r in rows if not r["coverage_bearing_checker"]]
    w(f"- {len(no_subject_checker)} / {n} have no discriminating checker naming"
      " their own subject, where the subject is taken only from an EXPLICIT")
    w("  `formal.kernel_theorem` / `kernel_declaration` binding.")
    guess_only = [r for r in rows if r["coverage_by_guess_only"]]
    w(f"- of those, {len(guess_only)} would gain one if the ledger's regex")
    w("  fallback (`theorem_of`, whose own docstring calls it \"demonstrably NOT")
    w("  reliable in general\") were trusted. That gap is the size of the")
    w("  ledger's unbound-subject debt, not a protection.")
    no_pin = [r for r in rows if not r["exact_statement"]]
    w(f"- {len(no_pin)} / {n} have no `formal.statement` drift pin.")
    no_replay = [r for r in rows if not r["independent_replay"]]
    w(f"- {len(no_replay)} / {n} have no independent Lean replay.")
    no_sem = [r for r in rows if not r["semantic_falsification"]]
    w(f"- {len(no_sem)} / {n} carry no semantic-falsification evidence row.")
    no_mut = [r for r in rows if not r["mutation_control"]]
    w(f"- {len(no_mut)} / {n} name no mutation or negative control.")
    no_percheck = [r for r in rows if not r["per_theorem_footprint"]]
    w(f"- {len(no_percheck)} / {n} have no PER-THEOREM axiom footprint check;"
      " their footprint evidence is the prelude-wide sweep.")
    shared_only = [r for r in rows if r["n_checkers"] and r["checker_fanout_min"] > 1]
    w(f"- {len(shared_only)} / {n} have NO checker of their own: every command"
      " they cite is shared with another fact.")
    no_cmd = [r for r in rows if r["n_checkers"] == 0]
    w(f"- {len(no_cmd)} / {n} cite no `checker_command` at all.")
    multi = [r for r in rows if r["checkers_multi"]]
    prod = [r for r in multi if r["checkers_name_producer"]]
    w(f"- {len(multi)} / {n} carry an evidence row listing two or more named"
      f" `checkers`, and {len(prod)} of those name the PRODUCING run as one of")
    w("  them. The production is not a re-derivation of itself, so those rows")
    w("  are one check and one re-list, not two independent checks —")
    w("  `validate-facts.py` counts them toward its \"re-derived by 2+")
    w("  independent checkers\" line.")
    mis = sum(r["footprint_rows_mislabelled"] for r in rows)
    mis_facts = sum(1 for r in rows if r["footprint_rows_mislabelled"])
    w(f"- {mis} evidence rows across {mis_facts} facts declare a semantic"
      " `kind` (`exhaustive-enumeration` / `instance-pin`) while their")
    w("  `supports` records an axiom footprint. Nothing was enumerated. Read at")
    w("  face value the `kind` enum would over-report semantic falsification by")
    w(f"  {mis} rows, so this census reads `supports`, not `kind`.")
    w("")

    w("## By curation")
    w("")
    w("| curation | facts | median protections | own-subject checker | statement pin |")
    w("|---|---:|---:|---:|---:|")
    groups: dict[str, list[dict]] = collections.defaultdict(list)
    for r in rows:
        groups[r["curation"] or "(unset)"].append(r)
    for key in sorted(groups):
        g = groups[key]
        counts = sorted(x["protection_count"] for x in g)
        med = counts[len(counts) // 2]
        w(f"| {key} | {len(g)} | {med} | "
          f"{sum(1 for x in g if x['coverage_bearing_checker'])} | "
          f"{sum(1 for x in g if x['exact_statement'])} |")
    w("")

    w("## By proof route")
    w("")
    w("| route | facts | median protections |")
    w("|---|---:|---:|")
    groups = collections.defaultdict(list)
    for r in rows:
        groups[r["route"] or "(unset)"].append(r)
    for key in sorted(groups):
        g = groups[key]
        counts = sorted(x["protection_count"] for x in g)
        w(f"| {key} | {len(g)} | {counts[len(counts) // 2]} |")
    w("")
    return "\n".join(out) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="fail if the committed artifacts differ or a control fails")
    args = parser.parse_args(argv)

    all_facts = load_facts()
    proved = [f for f in all_facts if f.get("epistemic_status") in SETTLED]
    if not proved:
        print("SAFETY_MATRIX|ERROR|no proved facts found", file=sys.stderr)
        return 2

    fan = build_fanout(proved)
    pinned = statement_pinned_ids()
    if not pinned:
        print("SAFETY_MATRIX|ERROR|statement pin manifest empty or unreadable",
              file=sys.stderr)
        return 2

    rows = [classify(f, pinned, fan) for f in proved]
    by_id = {r["id"]: r for r in rows}
    if len(by_id) != len(rows):
        print("SAFETY_MATRIX|ERROR|duplicate fact id in census", file=sys.stderr)
        return 2

    failures = run_controls(by_id)
    if failures:
        for line in failures:
            print(f"SAFETY_MATRIX|CONTROL|{line}", file=sys.stderr)
        print(f"SAFETY_MATRIX|FAIL|{len(failures)} control(s) failed", file=sys.stderr)
        return 1

    tsv = render_tsv(rows)
    summary = render_summary(rows, fan, all_facts)

    if args.check:
        drift = []
        for path, text in ((MATRIX_TSV, tsv), (SUMMARY_MD, summary)):
            if not path.exists():
                drift.append(f"{path.relative_to(ROOT)} is absent")
            elif path.read_text() != text:
                drift.append(f"{path.relative_to(ROOT)} is stale")
        if drift:
            for line in drift:
                print(f"SAFETY_MATRIX|DRIFT|{line}", file=sys.stderr)
            print("SAFETY_MATRIX|FAIL|regenerate with "
                  "`python3 scripts/gen-safety-matrix.py`", file=sys.stderr)
            return 1
    else:
        OUT_DIR.mkdir(parents=True, exist_ok=True)
        MATRIX_TSV.write_text(tsv)
        SUMMARY_MD.write_text(summary)

    digest = hashlib.sha256(tsv.encode()).hexdigest()[:12]
    print(f"SAFETY_MATRIX|proved={len(rows)}|commands={len(fan)}"
          f"|max_fanout={max(len(v) for v in fan.values())}"
          f"|controls={len(POSITIVE_CONTROLS)}|digest={digest}")
    print("SAFETY_MATRIX|PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
