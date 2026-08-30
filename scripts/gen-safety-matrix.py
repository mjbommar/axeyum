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

    NO LONGER TRUE AS OF S1 (ADR-0763): `check-settled-fact-statements.py` now
    FAILS on a settled fact absent from this manifest, bounded by a
    `coverage_floor` ratchet, and every settled fact is pinned. The docstring
    above described the defect S1 removed and is kept as the reason this column
    exists at all.
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
# A command that WALKS A DEPENDENCY CLOSURE.  Audited per alternative by
# ADR-0795; the column was measured against the tools it names, not assumed.
#
# `footprint_closure_audit` qualifies: it rebuilds the narrow and widened
# closures over the kernel's public surface and aborts if either disagrees with
# `Kernel::axiom_footprint` / `Kernel::declaration_dependency_closure`.
#
# THREE ALTERNATIVES WERE REMOVED, and the reasons differ:
#
# - `kernel_declaration_projection` matched **24 of the 38** rows this column
#   reported and walks no closure at all.  Its `--require-declaration X
#   --require-kind K` prints `found <label> <kind> <name> <footprint-size>` and
#   its own module doc says the projection "is search vocabulary and must not be
#   confused with a transitive closure".  Every one of those 24 rows names a
#   `definition`, which has no proof body to be circular in, and the committed
#   greps do not even constrain the footprint-size field.  All 24 already read
#   `coverage_bearing_checker: yes`, so removing them here loses no measurement.
# - `dependency-audit` and `check-fact-depends-derived` matched **zero**
#   commands.  A dead alternative in a classifier is not harmless: it makes the
#   pattern look broader than it is, which is how the column came to be read as
#   a coverage claim.
DEPENDENCY_CLOSURE = re.compile(r"(footprint_closure_audit)")
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


# THE NINE ARE PER-FACT EVIDENCE COLUMNS. Every one asks the same question:
# does THIS fact's own record exercise this protection? Eight read the fact's
# own `checker_command`s; `exact_statement` reads a ledger-wide manifest keyed
# by fact id, which is why it is the one that reached 100% (ADR-0763).
#
# THEY ARE NOT COVERAGE. A protection can be enforced centrally, on every
# merge, for a fact that cites nothing — and then no column here moves. ADR-0795
# measures the gap; `COVERAGE_COLUMNS` below carries the one central set that is
# publishable per fact today.
COLUMNS = [
    "kernel_theorem",
    "per_theorem_footprint",
    "env_footprint",
    "circularity",
    "semantic_falsification",
    "mutation_control",
    "independent_replay",
    "coverage_bearing_checker",
]

# CENTRALLY-ENFORCED COVERAGE, credited only from a gate's OWN published
# per-fact set. Never from a gate's headline number, never from a family, never
# from a route. A protection whose gate cannot say which facts it reached gets
# no column here — that inability is a finding about the gate (ADR-0795), and
# reporting it as coverage would be the inflation this census exists to avoid.
#
# These are reported separately from `COLUMNS` and do NOT enter
# `protection_count`: a fact does not become better protected because somebody
# else measured it, and mixing the two is exactly the confusion ADR-0795 found.
COVERAGE_COLUMNS = [
    "exact_statement",
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
    # WAS `False`, flipped by S1 (ADR-0763), which pinned every settled fact.
    # This row is now a POSITIVE control only, and the negative polarity for
    # this column moved to `UNPINNABLE_PROBE` below -- because with coverage at
    # 2117/2117 no census row can be the False side, and leaving a `False` here
    # would make the census permanently red for a reason that is good news.
    ("F:nat-sumrange-add", "exact_statement", True),
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
    # ADR-0795. `circularity` matched `kernel_declaration_projection`, which
    # walks no closure; 24 of 38 yes-rows came from it and every one named a
    # `definition`. These two pin the repair from both sides -- a genuine
    # closure walk still counts, and a projection row no longer does -- so
    # reinstating the removed alternative fails here rather than silently
    # re-inflating the column.
    ("F:cpoint-cauchy-schwarz", "circularity", True),
    ("F:complex-factorquotient", "circularity", False),
]


# The negative polarity for `exact_statement`, relocated by S1 (ADR-0763).
#
# The column is `fact["id"] in pinned`, so its failure mode is
# `statement_pinned_ids()` returning something other than what the manifest
# says -- reading the wrong field, or every fact id regardless of content. A
# census row used to catch that by being genuinely unpinned; none is, now.
#
# An id that is not in the ledger at all cannot become pinned by ordinary work,
# so this control does not rot the way an `open` fact's id would (which would
# fire the day somebody proved it, for no fault of this predicate).
UNPINNABLE_PROBE = "F:this-fact-id-does-not-exist-and-must-never-be-pinned"

# ...AND THAT PROBE ALONE IS WEAKER THAN THE CENSUS ROW IT REPLACED, which S1
# flagged for review and ADR-0795 confirms. It watches `statement_pinned_ids()`
# and nothing else, so two failures walk past it:
#
#   1. a `statement_pinned_ids()` that read the FACTS directory instead of the
#      manifest would return every real fact id, contain no probe, and report
#      `exact_statement` at 100% -- exactly today's number, from no manifest;
#   2. a `classify()` whose `exact_statement` became a constant `True` never
#      consults `pinned` at all.
#
# `SYNTHETIC_UNPINNED` restores the census-row polarity without needing an
# unpinned fact to exist: it runs the REAL `classify()` over a fact-shaped dict
# whose id is in no manifest, and requires `exact_statement` to come back False.
SYNTHETIC_UNPINNED = {
    "id": "F:synthetic-unpinned-control-not-in-any-manifest",
    "proof_route": "kernel-lean",
    "formal": {"language": "lean4", "kernel_theorem": "Synthetic.control"},
    "evidence": [],
}


def run_controls(by_id: dict[str, dict], pinned: set[str] | None = None,
                 unsettled: set[str] | None = None) -> list[str]:
    failures = []
    # ...AND NEITHER PROBE ABOVE CATCHES A PIN SET READ FROM THE WRONG SOURCE.
    # Mutation-verified 2026-08-30 (ADR-0795): replacing the manifest read with
    # `{fact["id"] for fact in FACTS}` exits 0 with ZERO control failures --
    # `exact_statement` still reads 2121/2121, from no manifest at all, and both
    # the unpinnable probe and the synthetic row are blind to it because neither
    # id is a real fact.
    #
    # This is the one that fires: the manifest pins SETTLED facts, so an `open`
    # or `refuted` fact id appearing in it means the set did not come from the
    # manifest. 145 such ids exist today, so the control has real subjects; a
    # ledger with none would make it vacuous, which is why it says so.
    if pinned is not None and unsettled is not None:
        if not unsettled:
            failures.append(
                "control vacuous: no unsettled facts exist, so the "
                "`exact_statement` source control has no subject to detect a "
                "pin set read from the ledger rather than the manifest"
            )
        leaked = sorted(pinned & unsettled)
        if leaked:
            failures.append(
                f"control failed: statement_pinned_ids() contains {len(leaked)} "
                f"UNSETTLED fact id(s), first {leaked[0]!r}. The manifest pins "
                "settled facts only, so the set is not being read from it -- "
                "`exact_statement` would report full coverage from no manifest"
            )
    if pinned is not None:
        synth = classify(SYNTHETIC_UNPINNED, pinned, {})
        if synth["exact_statement"] is not False:
            failures.append(
                "control failed: classify() reports `exact_statement` True for "
                f"{SYNTHETIC_UNPINNED['id']!r}, which is in no manifest -- the "
                "column is not being decided by manifest membership"
            )

    if pinned is not None and UNPINNABLE_PROBE in pinned:
        failures.append(
            f"control failed: statement_pinned_ids() contains {UNPINNABLE_PROBE!r}, "
            "which is in no manifest and no ledger -- the pin set is not being read "
            "from the manifest at all, and every `exact_statement` yes is worthless"
        )
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
        *COLUMNS, "protection_count", *COVERAGE_COLUMNS,
        "subject_guessed", "coverage_by_guess_only",
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
            *("yes" if r[c] else "no" for c in COVERAGE_COLUMNS),
            r["subject_guessed"] or "-",
            "yes" if r["coverage_by_guess_only"] else "no",
            "yes" if r["checkers_multi"] else "no",
            "yes" if r["checkers_name_producer"] else "no",
        ]))
    return "\n".join(lines) + "\n"


# A column whose number is an UPPER bound carries its correction ON THE ROW.
# The disclosure used to sit 36 lines below the table, which is where a reader
# scanning for a figure will not find it. An overstatement disclosed out of
# eyeshot of the number it corrects is the shape this census exists to catch.
UPPER_BOUND_COLUMNS = {
    "semantic_falsification": (
        " **UPPER BOUND — 8 demonstrated.** Counts facts whose evidence names a"
        " semantic control, not facts whose control was shown to discriminate."
    ),
}


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
        note = UPPER_BOUND_COLUMNS.get(c, "")
        w(f"| `{c}` | {k} / {n} | {100.0 * k / n:.1f}% |{note}")
    w("")

    w("## Centrally-enforced coverage (NOT the same measurement)")
    w("")
    w("The columns above are PER-FACT EVIDENCE: this fact's own record")
    w("exercises the protection. A gate that enforces the same protection on")
    w("every merge, for facts that cite nothing, moves none of them. The two")
    w("are different questions and neither dominates -- per-fact evidence is")
    w("self-describing and survives the fact being copied elsewhere; central")
    w("coverage is stronger in practice and far cheaper. ADR-0795.")
    w("")
    w("A gate earns a column here only by publishing, machine-readably, the")
    w("PER-FACT SET it reached. A headline number confers nothing on any")
    w("member, and `protection_count` above deliberately excludes these: a")
    w("fact is not better protected because somebody else measured it.")
    w("")
    w("| coverage | proved facts | share | published per-fact set |")
    w("|---|---:|---:|---|")
    for c in COVERAGE_COLUMNS:
        k = sum(1 for r in rows if r[c])
        w(f"| `{c}` | {k} / {n} | {100.0 * k / n:.1f}% | "
          "`artifacts/ontology/settled-fact-statement-pins.json` `pins[].fact_id` "
          "(S1, ADR-0763) |")
    w("")
    w("Gates that enforce a protection this census names and publish NO")
    w("machine-readable per-fact set, so they cannot be credited here. Each")
    w("row is a finding about the GATE, not about the facts; the missing")
    w("column is what the gate would have to emit (ADR-0795).")
    w("")
    w("| protection | gate | publishes | what it would have to emit |")
    w("|---|---|---|---|")
    w("| `circularity`, `per_theorem_footprint` | `scripts/check-trust-closure.py` "
      "(S2) | `subjects` / `unresolved` counts | the `subjects.resolved` fact-id "
      "set it already builds and discards |")
    w("| `semantic_falsification` | `scripts/check-semantic-control-fixtures.py` "
      "(S3) | `census.load_bearing_facts` count in `fixture-pack.json` | the "
      "`load_bearing` map keyed by fact id, which it already computes |")
    w("| `independent_replay` | `real_lean_replay_census` (S4, ADR-0760) | "
      "declaration names Lean's kernel admitted | the fact-to-declaration join, "
      "so a NAME grade becomes a FACT grade |")
    w("| `mutation_control` | "
      "`scripts/check-statement-identity-mutations.py` (S1) | one ledger-wide "
      "pass/fail | nothing -- it is not a per-fact protection and should not "
      "be read as one |")
    w("")
    w("S3's own artifact already states the direction that matters: its")
    w("`semantic_falsification` figure is an UPPER bound, counting facts with a")
    w("semantic evidence row rather than facts whose control was shown to")
    w("discriminate. Measured 2026-08-30: evidence 95, demonstrated 8.")
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

    unsettled = {
        f["id"] for f in all_facts
        if f.get("epistemic_status") not in SETTLED | {"computed"}
    }
    failures = run_controls(by_id, pinned, unsettled)
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
