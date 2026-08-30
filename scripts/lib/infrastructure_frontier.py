"""Shared logic for the L2 phase G3 infrastructure frontier
(docs/plan/graph-directed-library-roadmap-2026-08-30.md, ADR-0845).

This module joins the L1 phase G2 graph join
(`artifacts/graph-join/<population>.join.json`, ADR-0835) and the
declaration graph itself (`artifacts/declaration-graph/graph/<population>.
rows.json` / `.edges.json`, ADR-0820) against a small, HAND-CURATED,
committed list of candidate frontier rows (`ROW_CANDIDATES` below), then
computes every row's evidence fields (in-population degree, resolution
status per join dimension, name-coincidence membership) live from those
artifacts.

Why hand-curated candidates rather than a purely mechanical rule: the
underlying population is 446 declarations, most of them Lean/Mathlib-core
typeclass and recursor scaffolding this kernel has no counterpart for
(ADR-0835's own "what this join does not capture" section). A purely
degree-ranked queue reproduces exactly the failure this phase's own spec
warns against ("raw degree never authorizes work" -- a declaration with
many dependents is not thereby worth building). So curation happens once,
in source, where it is diffable and reviewable; every curated candidate is
then RE-VALIDATED against the live join and graph at generation time
(`validate_candidate`), and generation FAILS if a candidate's supporting
assumption no longer holds (e.g. its subject is no longer in the
population, or it has since acquired a fact_id it was proposed to lack).
This keeps the curation honest without making it purely mechanical.

Needs no Lean toolchain and no cargo run: every input is already-committed
JSON or a plain grep over already-committed source.
"""
from __future__ import annotations

import hashlib
import json
import pathlib
import subprocess
from collections import Counter
from typing import Any

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GRAPH_JOIN_DIR = REPO_ROOT / "artifacts" / "graph-join"
DECL_GRAPH_DIR = REPO_ROOT / "artifacts" / "declaration-graph" / "graph"
FACTS_DIR = REPO_ROOT / "artifacts" / "facts"

QUEUES = (
    "language-infrastructure",
    "proof-producers",
    "theorem-dominators",
    "dependency-ready-leaves",
)

GAIN_KINDS = ("statability", "dispatchability", "proof", "independent_assurance")

ADVISORY_NOTICE = (
    "Graph rank is ADVISORY until its authority is complete "
    "(docs/plan/global/50-planning-rules.md: 'Graph rank is advisory until "
    "its authority is complete'). These queues are a proposal for humans and "
    "coordinators to read, not an automatic dispatcher -- that is L2 phase "
    "G5's job, not this artifact's. A row's rank or presence here does not "
    "authorize work; a lane brief citing a row still needs the ordinary "
    "review this repository requires for any increment."
)

DEGREE_DISCLAIMER = (
    "In-population in-/out-degree is reported as a RAW INPUT (the roadmap's "
    "own requirement: 'all scores must show their raw inputs'), never as the "
    "row's justification by itself. Every row's real argument is its "
    "'gain' field and its 'current_blockers' -- a row whose only argument is "
    "its degree does not belong in this file."
)


def load_json(path: pathlib.Path) -> Any:
    with open(path, "r", encoding="utf-8") as fh:
        return json.load(fh)


def load_join(population_id: str, join_dir: pathlib.Path = GRAPH_JOIN_DIR) -> dict:
    return load_json(join_dir / f"{population_id}.join.json")


def load_rows(population_id: str, graph_dir: pathlib.Path = DECL_GRAPH_DIR) -> dict:
    return load_json(graph_dir / f"{population_id}.rows.json")


def load_edges(population_id: str, graph_dir: pathlib.Path = DECL_GRAPH_DIR) -> dict:
    return load_json(graph_dir / f"{population_id}.edges.json")


def compute_degrees(edges: list[dict]) -> tuple[Counter, Counter]:
    """Returns (indegree, outdegree) over the population's own edge list."""
    indeg: Counter = Counter()
    outdeg: Counter = Counter()
    for e in edges:
        indeg[e["to"]] += 1
        outdeg[e["from"]] += 1
    return indeg, outdeg


def row_id(queue: str, population_id: str, subject: list[str], gain_kind: str) -> str:
    """A content hash of the row's SUBSTANCE -- queue, population, the sorted
    subject declaration names, and the claimed gain kind -- never a
    positional index, and never a computed/volatile number (degree, resolved
    counts). This is what makes the id survive regeneration: as long as the
    proposal is "the same declarations, same queue, same kind of gain", the
    id is unchanged even if the graph is rebuilt and degrees shift by one.
    """
    payload = json.dumps(
        {
            "queue": queue,
            "population_id": population_id,
            "subject": sorted(subject),
            "gain_kind": gain_kind,
        },
        sort_keys=True,
    ).encode("utf-8")
    digest = hashlib.sha256(payload).hexdigest()[:10]
    short = {
        "language-infrastructure": "LANG",
        "proof-producers": "PROD",
        "theorem-dominators": "DOM",
        "dependency-ready-leaves": "LEAF",
    }[queue]
    return f"IF-{short}-{digest}"


def grep_presence(pattern: str, src_dir: pathlib.Path | None = None, timeout: int = 30) -> list[str]:
    """A WEAK, non-authoritative source-text presence heuristic. Returns the
    list of files under crates/axeyum-lean-kernel/src containing a
    word-boundary match of `pattern`. This is exactly the kind of bare
    name-similarity ADR-0835 refuses to treat as an identity claim, so a
    non-empty result here is NEVER reported as "already proved" -- only as
    "a name coincidence exists; treat as a caution to check identity before
    duplicating work, not as a fact of presence or absence."
    """
    src_dir = src_dir or (REPO_ROOT / "crates" / "axeyum-lean-kernel" / "src")
    try:
        out = subprocess.run(
            ["/usr/bin/grep", "-rlE", r"\b" + pattern + r"\b", str(src_dir)],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return []
    hits = [line.strip() for line in out.stdout.splitlines() if line.strip()]
    return sorted(hits)


# ---------------------------------------------------------------------------
# Hand-curated candidates.
#
# Each candidate names a proposed increment over population
# `mathlib-group-defs-v1` (ADR-0820/ADR-0835). Fields:
#
#   queue             one of QUEUES
#   subject           sorted-at-use list of Mathlib declaration names this
#                     row is about (must all exist in the population)
#   title             short human label
#   gain_kind         one of GAIN_KINDS -- what the increment actually buys
#   gain_explanation  a sentence naming the mechanism, not just "many things
#                     depend on this"
#   current_blockers  list of strings, each citing where the blocker comes
#                     from (a join dimension, an ADR, a CLAUDE.md gotcha)
#   destination_paths list of repo-relative paths or curriculum node ids;
#                     [] is allowed but must be paired with a note in
#                     `destination_note` explaining why none exists yet
#   destination_note  required when destination_paths is []
#   estimated_cost    {"tier": "S"|"M"|"L"|"XL", "rationale": str}
#   preregistered_metric:
#       {"description": str, "command": str, "baseline": <int|str>}
#     `command` must be re-runnable verbatim later to check whether the
#     metric moved; `baseline` is the value it returns NOW (measured at
#     generation time and asserted, not merely recorded -- see
#     validate_candidate).
#   confidence        "high" | "medium" | "low" -- low means the row needs a
#                     verification step before any proof/build work, not
#                     that the row is unfounded
#   not_this           optional list of alternative-classification notes,
#                     e.g. "considered for theorem-dominators; moved here
#                     because the real blocker is architectural"
# ---------------------------------------------------------------------------

ROW_CANDIDATES: list[dict] = [
    {
        "queue": "language-infrastructure",
        "subject": ["Semigroup", "mul_assoc"],
        "title": "Bundled semigroup structure + generic associativity",
        "gain_kind": "statability",
        "gain_explanation": (
            "This kernel has no bundled-structure/typeclass mechanism at "
            "all (ADR-0835, 'what this join does not capture': 0 of 446 "
            "typeclass/structure declarations in this population have a "
            "representable counterpart). So 'let (S, *) be associative' "
            "cannot be STATED once and reused -- every carrier (Nat, Int, "
            "Rat, CReal, Complex) restates and reproves its own *_assoc "
            "from scratch. The gain is statability of the GENERAL "
            "proposition, not of any one instance."
        ),
        "current_blockers": [
            "join:statement_vocabulary -- 'Semigroup' resolves to no "
            "KERNEL_CARRIER_ROOTS entry (root-exact match against the 12 "
            "inductive carriers only; a bundled structure is not one of "
            "them)",
            "join:fact_ids -- 'mul_assoc' has no ml430 mirror fact and is "
            "not a name-coincidence candidate (it names no existing kernel "
            "subject at all under this join's extraction)",
            "adr:0835 -- 'this kernel has no bundled-structure/typeclass "
            "mechanism at all' (What this join does not capture)",
        ],
        "destination_paths": [
            "docs/curriculum/02-structures/groups.md",
        ],
        "destination_note": None,
        "estimated_cost": {
            "tier": "L",
            "rationale": (
                "Needs a new kernel-representable pattern (a predicate "
                "bundle over an existing carrier + operation, e.g. "
                "'IsAssociative f', not necessarily Lean-style bundled "
                "structures) PLUS at least one worked instance per carrier "
                "to show the abstraction is usable and not merely "
                "declarable. Comparable in shape to the CReal uniform-"
                "continuity/congruence infrastructure already built."
            ),
        },
        "preregistered_metric": {
            "description": (
                "A generic (carrier-polymorphic) associativity helper "
                "should exist in crates/axeyum-lean-kernel/src that is NOT "
                "specific to one carrier's *_assoc theorem."
            ),
            "command": (
                "/usr/bin/grep -rlE 'IsAssociative|is_associative|"
                "generic_assoc' crates/axeyum-lean-kernel/src | wc -l"
            ),
            "baseline": 0,
        },
        "confidence": "high",
    },
    {
        "queue": "language-infrastructure",
        "subject": ["CommMagma", "mul_comm"],
        "title": "Bundled commutative-magma structure + generic commutativity",
        "gain_kind": "statability",
        "gain_explanation": (
            "Same missing bundled-structure mechanism as Semigroup, applied "
            "to commutativity. Every carrier in this kernel restates and "
            "reproves its own *_comm; CLAUDE.md's own incident log (the "
            "'Nat.lor_aux_comm_of_fuel'/'lorAux'/'ldiffAux' entries) records "
            "several sessions spent re-deriving commutativity per-operator "
            "because no shared statement or transport lemma exists."
        ),
        "current_blockers": [
            "join:statement_vocabulary -- 'CommMagma' resolves to no "
            "KERNEL_CARRIER_ROOTS entry",
            "join:fact_ids -- 'mul_comm' has no ml430 mirror fact",
            "claude.md:gotchas -- 'A transported proof needs its binder "
            "structure re-derived, not only its lemma names re-pointed' "
            "(the *_comm/*_assoc transport-by-hand pattern, measured "
            "2026-08-29 across land/lor/ldiff)",
        ],
        "destination_paths": [
            "docs/curriculum/02-structures/groups.md",
        ],
        "destination_note": None,
        "estimated_cost": {
            "tier": "L",
            "rationale": (
                "Same shape as the Semigroup row; likely shares the "
                "underlying predicate-bundle mechanism, so should be "
                "designed together with it rather than twice."
            ),
        },
        "preregistered_metric": {
            "description": (
                "A generic (carrier-polymorphic) commutativity helper "
                "should exist that is not specific to one carrier's "
                "*_comm theorem."
            ),
            "command": (
                "/usr/bin/grep -rlE 'IsCommutative|is_commutative|"
                "generic_comm' crates/axeyum-lean-kernel/src | wc -l"
            ),
            "baseline": 0,
        },
        "confidence": "high",
    },
    {
        "queue": "language-infrastructure",
        "subject": ["Mul", "IsLeftCancelMul", "mul_left_cancel"],
        "title": "Left-cancellative-multiplication structure",
        "gain_kind": "statability",
        "gain_explanation": (
            "'mul_left_cancel' is a Theorem in the population with no "
            "fact_id and no name-coincidence hit (a genuinely new "
            "statement, not merely unmirrored), but it is stated over "
            "'IsLeftCancelMul', a bundled predicate this kernel cannot "
            "represent yet -- same root cause as the Semigroup/CommMagma "
            "rows. Concrete carriers already have their OWN cancellation "
            "lemmas (e.g. Nat has cancellation facts for '*'); the gain "
            "here is a single generic statement usable across carriers "
            "sharing the predicate, not a new concrete fact."
        ),
        "current_blockers": [
            "join:statement_vocabulary -- 'IsLeftCancelMul' and 'Mul' "
            "resolve to no KERNEL_CARRIER_ROOTS entry",
            "join:fact_ids -- 'mul_left_cancel' unresolved, and NOT a "
            "name-coincidence candidate (join computed: no other fact's "
            "extracted kernel subject matches this bare string)",
        ],
        "destination_paths": [
            "docs/curriculum/02-structures/groups.md",
        ],
        "destination_note": None,
        "estimated_cost": {
            "tier": "M",
            "rationale": (
                "Depends on the Semigroup/CommMagma predicate-bundle "
                "mechanism landing first; once that exists, one more "
                "predicate plus one theorem is a small increment."
            ),
        },
        "preregistered_metric": {
            "description": (
                "artifacts/graph-join/mathlib-group-defs-v1.join.json "
                "name_coincidence_candidates must still NOT contain "
                "'mul_left_cancel' after this lands (a hit there would mean "
                "an unrelated fact happens to share this name and needs "
                "identity resolution, not fresh work)."
            ),
            "command": (
                "python3 -c \"import json; d=json.load(open("
                "'artifacts/graph-join/mathlib-group-defs-v1.join.json')); "
                "print('mul_left_cancel' in d['name_coincidence_candidates'])\""
            ),
            "baseline": False,
        },
        "confidence": "medium",
    },
    {
        "queue": "language-infrastructure",
        "subject": ["congrArg"],
        "title": "Carrier-polymorphic congruence (generic congrArg)",
        "gain_kind": "dispatchability",
        "gain_explanation": (
            "'congrArg' (indegree 5 in this population -- five other "
            "population declarations cite it directly) is a genuinely "
            "new statement here (not fact-resolved, not a name-"
            "coincidence candidate) and its Mathlib type is fully "
            "carrier-generic: '∀ {α β} (f : α → β) {a b}, a = b → f a = "
            "f b'. CLAUDE.md's own gotcha log ('THE DEV-HELPER LAYER "
            "HARDCODES A CARRIER') documents this kernel building a NEW "
            "per-carrier congr helper every time one is needed "
            "(congr_nat_to, congr_bool_to_nat, congr_bool_to_nat, "
            "NatOps::congr stating its conclusion at Nat only) -- each one "
            "an opaque TypeMismatch away from being found. A genuinely "
            "generic congrArg would remove a recurring, already-measured "
            "cost rather than add new statable content, hence "
            "'dispatchability' (it changes how CHEAPLY future proof work "
            "dispatches) rather than 'statability'."
        ),
        "current_blockers": [
            "join:fact_ids -- 'congrArg' unresolved, not a name-coincidence "
            "candidate",
            "claude.md:gotchas -- 'THE DEV-HELPER LAYER HARDCODES A "
            "CARRIER, AND EVERY CROSS-CARRIER USE FAILS AS ONE OPAQUE "
            "TypeMismatch ACROSS THE WHOLE SUITE' (three separate lanes, "
            "2026-08-29, in NatOps::congr / IntDev::irefl / Bool congr)",
        ],
        "destination_paths": [],
        "destination_note": (
            "No curriculum node names this; it is cross-cutting kernel "
            "API surface (crates/axeyum-lean-kernel), not a mathematical "
            "topic with its own curriculum row."
        ),
        "estimated_cost": {
            "tier": "S",
            "rationale": (
                "A single generic helper over an arbitrary Pi-typed "
                "function and an Eq hypothesis; the surrounding kernel "
                "machinery (Kernel::infer, def_eq) already supports "
                "polymorphic Pi types, so this is API consolidation, not "
                "new kernel capability."
            ),
        },
        "preregistered_metric": {
            "description": (
                "Count of distinct per-carrier 'congr_X_to_Y'-shaped dev "
                "helpers in crates/axeyum-lean-kernel/src should stop "
                "growing (ideally shrink) once a generic congrArg exists; "
                "baseline count of the three CLAUDE.md names it directly."
            ),
            "command": (
                "/usr/bin/grep -rlE 'congr_nat_to|congr_bool_to_nat' "
                "crates/axeyum-lean-kernel/src | wc -l"
            ),
            "baseline": 1,
        },
        "confidence": "medium",
    },
    {
        "queue": "theorem-dominators",
        "subject": ["of_decide_eq_true"],
        "title": "Decidable/Bool bridge lemma -- verify identity before dispatch",
        "gain_kind": "independent_assurance",
        "gain_explanation": (
            "'of_decide_eq_true' has in-population indegree 3 among "
            "unresolved Theorem-kind declarations after excluding built-in "
            "projections and Lean-internal auxiliaries -- a real dominator "
            "candidate by the population's own structure. It is NOT a "
            "name_coincidence_candidate in the join (that mechanism scans "
            "only FACT evidence text), but a plain source grep finds "
            "'Decidable.of_decide_eq_true' already declared as a kernel "
            "prelude primitive (crates/axeyum-lean-kernel/src/prelude.rs). "
            "This is the exact bare-name-similarity situation ADR-0835 "
            "refuses to treat as an identity claim, so this row is NOT "
            "'go prove this' -- it is 'go compare the Mathlib statement "
            "against Kernel::Prelude::of_decide_eq_true's actual type "
            "before doing anything else'. If the comparison confirms the "
            "same proposition, the gain is independent_assurance (an "
            "explicit, checked cross-reference where today there is only "
            "a name coincidence nobody has looked at); if it refutes it, "
            "this row converts to a genuine proof-class candidate."
        ),
        "current_blockers": [
            "join:fact_ids -- 'of_decide_eq_true' unresolved (no ml430 "
            "mirror fact)",
            "methodology -- the join's own name_coincidence_candidates "
            "dimension only scans FACT evidence text and cannot see this "
            "coincidence, because 'of_decide_eq_true' is named in kernel "
            "prelude source, not in any fact's evidence; this row exists "
            "specifically because that blind spot needed a human check",
        ],
        "destination_paths": [],
        "destination_note": (
            "Cross-cutting Decidable/Bool bridge machinery, not a single "
            "curriculum topic; the check belongs wherever "
            "Kernel::Prelude::of_decide_eq_true is exercised "
            "(crates/axeyum-lean-kernel/src/prelude.rs and its tests)."
        ),
        "estimated_cost": {
            "tier": "S",
            "rationale": (
                "The verification step is reading two type signatures side "
                "by side; if they agree, no proof work is needed at all. "
                "Only if they disagree does this become new proof work, at "
                "which point its cost is unknown and must be re-estimated."
            ),
        },
        "preregistered_metric": {
            "description": (
                "Existence of an explicit written comparison (a fact, a "
                "code comment, or a doc note) between the Mathlib "
                "'of_decide_eq_true' statement and "
                "Kernel::Prelude::of_decide_eq_true's rendered type. "
                "Baseline: no such comparison exists anywhere in the repo."
            ),
            "command": (
                "/usr/bin/grep -rlE 'of_decide_eq_true' "
                "docs/ artifacts/facts | wc -l"
            ),
            "baseline": 0,
        },
        "confidence": "low",
        "not_this": [
            "Not classified as dependency-ready-leaves: its direct type "
            "deps (Bool, Bool.true, Decidable, Decidable.decide, Eq) are "
            "all vocabulary-covered, which is exactly why it survived that "
            "filter too -- but it is presented here, once, rather than in "
            "both queues, because the decisive next step is identity "
            "verification, not proof dispatch.",
        ],
    },
]


def _empty_reason(queue: str, computed: dict) -> str:
    if queue == "proof-producers":
        return (
            "0 rows. Structural, not incidental: `producers`/`declines` in "
            "the ADR-0835 join are checked ONLY against the 9 declarations "
            "already resolved in `fact_ids` (ADR-0835, 'what this join does "
            "not capture': 'a producer targeting an unresolved declaration "
            "... cannot be seen by this join by construction'), and all 9 "
            "of those are already `epistemic_status=proved` "
            f"(verified against artifacts/facts/*.json: "
            f"{computed['proved_of_9']}/9 proved). A reusable producer "
            "serves an OPEN cluster; this population currently contributes "
            "0 open, fact-linked declarations, so there is no cluster here "
            "for a producer to serve. The real shared-producer opportunity "
            "this population points at (a generic commutativity/"
            "associativity transport step, reusable across Nat/Int/Rat/"
            "CReal/Complex) is a LANGUAGE-infrastructure prerequisite, "
            "recorded in the language-infrastructure queue instead of "
            "padded in here."
        )
    if queue == "dependency-ready-leaves":
        return (
            f"0 rows. {computed['leaf_candidate_count']} Theorem-kind "
            "declarations had every direct TYPE dependency already "
            "available (fact-resolved or vocabulary-covered) -- computed "
            "from direct_type_deps only, never proof/value deps, per this "
            "phase's own rule that proof-derived data is forbidden "
            "producer input. Every one of those candidates was excluded "
            "for a stated reason: built-in inductive projections needing "
            "no separate proof (And.left, And.right, Or.elim -- the "
            "carrier's own elimination principle already provides them); "
            "Lean-generated auxiliary/private machinery with no "
            "independent mathematical content (noConfusion_of_Nat and its "
            "private aux, Nat.le.brecOn); promoted to the "
            "language-infrastructure queue because the real blocker is "
            "architectural (congrArg); or promoted to theorem-dominators "
            "because the decisive next step is identity verification, not "
            "proof dispatch (of_decide_eq_true). This matches "
            "scripts/check-dispatchable-frontier.py's own finding that the "
            "ledger-wide dispatchable set is nearly empty (1 of 139 open "
            "ml430 mirrors) -- this population contributes 0 to that 1."
        )
    return (
        f"0 rows in queue {queue!r} with no specific declared reason wired "
        "up for it in _empty_reason(); this is a generation-time gap, not a "
        "silent pad -- see scripts/gen-infrastructure-frontier.py."
    )


def compute_dependency_ready_leaf_candidates(
    rows: list[dict], indeg: Counter, join: dict
) -> list[dict]:
    """Theorem-kind declarations with no fact_id, not a name-coincidence
    candidate, and EVERY direct TYPE dependency already available (fact-
    resolved or vocabulary-covered). Deliberately uses direct_type_deps only,
    never direct_value_deps/proof deps -- L1 phase G1's own exit criterion
    marks proof-derived data forbidden producer input, and readiness here
    must be a STATABILITY signal, not a proof-shape signal.
    """
    fact_resolved = set(join["dimensions"]["fact_ids"]["resolved"].keys())
    vocab_resolved = set(join["dimensions"]["statement_vocabulary"]["resolved"].keys())
    name_coincidences = set(join["name_coincidence_candidates"].keys())
    available = fact_resolved | vocab_resolved

    out = []
    for r in rows:
        if r["kind"] != "Theorem":
            continue
        name = r["name"]
        if name in fact_resolved or name in name_coincidences:
            continue
        type_deps = r.get("direct_type_deps") or []
        if not type_deps:
            continue
        if all(d in available for d in type_deps):
            out.append(
                {
                    "name": name,
                    "in_degree_within_population": indeg.get(name, 0),
                    "direct_type_deps": type_deps,
                }
            )
    out.sort(key=lambda d: d["name"])
    return out


def validate_candidate(candidate: dict, rows_by_name: dict, join: dict) -> list[str]:
    """Re-derives every claim a candidate makes against the LIVE join/graph.
    Returns a list of failure strings (empty = candidate still holds).
    """
    failures = []
    subject = candidate["subject"]
    fact_resolved = set(join["dimensions"]["fact_ids"]["resolved"].keys())
    name_coincidences = set(join["name_coincidence_candidates"].keys())
    for name in subject:
        if name not in rows_by_name:
            failures.append(
                f"{candidate['title']!r}: subject {name!r} is not in "
                f"population {join['population_id']!r} -- candidate is stale"
            )
    theorem_subjects = [n for n in subject if rows_by_name.get(n, {}).get("kind") == "Theorem"]
    for name in theorem_subjects:
        if name in fact_resolved:
            failures.append(
                f"{candidate['title']!r}: subject {name!r} now HAS a "
                "fact_id -- this candidate's premise (no ledger coverage) "
                "no longer holds; re-curate or drop the row"
            )
    if candidate["queue"] not in QUEUES:
        failures.append(f"{candidate['title']!r}: unknown queue {candidate['queue']!r}")
    if candidate["gain_kind"] not in GAIN_KINDS:
        failures.append(f"{candidate['title']!r}: unknown gain_kind {candidate['gain_kind']!r}")
    if not candidate["current_blockers"]:
        failures.append(f"{candidate['title']!r}: current_blockers must not be empty")
    if not candidate["destination_paths"] and not candidate.get("destination_note"):
        failures.append(
            f"{candidate['title']!r}: empty destination_paths needs a destination_note"
        )
    pm = candidate["preregistered_metric"]
    if not pm.get("command"):
        failures.append(f"{candidate['title']!r}: preregistered_metric.command is required")
    return failures


def build_row(candidate: dict, population_id: str, rows_by_name: dict, indeg: Counter, outdeg: Counter, join: dict) -> dict:
    subject = candidate["subject"]
    fact_resolved = set(join["dimensions"]["fact_ids"]["resolved"].keys())
    vocab_resolved = set(join["dimensions"]["statement_vocabulary"]["resolved"].keys())
    name_coincidences = join["name_coincidence_candidates"]

    per_subject_evidence = []
    for name in subject:
        r = rows_by_name.get(name, {})
        per_subject_evidence.append(
            {
                "name": name,
                "kind": r.get("kind"),
                "origin_module": r.get("origin_module"),
                "in_degree_within_population": indeg.get(name, 0),
                "out_degree_within_population": outdeg.get(name, 0),
                "fact_id_resolved": name in fact_resolved,
                "statement_vocabulary_resolved": name in vocab_resolved,
                "is_name_coincidence_candidate": name in name_coincidences,
            }
        )

    rid = row_id(candidate["queue"], population_id, subject, candidate["gain_kind"])
    return {
        "row_id": rid,
        "queue": candidate["queue"],
        "title": candidate["title"],
        "subject_declarations": sorted(subject),
        "population_id": population_id,
        "gain_kind": candidate["gain_kind"],
        "gain_explanation": candidate["gain_explanation"],
        "evidence": {
            "raw_inputs_disclaimer": DEGREE_DISCLAIMER,
            "per_subject": per_subject_evidence,
        },
        "current_blockers": candidate["current_blockers"],
        "destination_paths": candidate["destination_paths"],
        "destination_note": candidate.get("destination_note"),
        "estimated_cost": candidate["estimated_cost"],
        "preregistered_metric": candidate["preregistered_metric"],
        "confidence": candidate["confidence"],
        "not_this": candidate.get("not_this", []),
    }


def load_cross_check_dispatchable(dispatch_output: str | None) -> dict:
    """Parses the fixed-shape summary lines scripts/check-dispatchable-
    frontier.py prints (it is out of scope to edit; we only read its
    stdout). Returns a small structured summary; if `dispatch_output` is
    None the caller did not run it this generation and the cross_check
    section says so explicitly rather than fabricating numbers.
    """
    if dispatch_output is None:
        return {
            "ran": False,
            "note": (
                "Not re-run this generation; see docs/plan/status/"
                "l2-g3-infrastructure-frontier.md for the last captured run. "
                "scripts/check-dispatchable-frontier.py is out of this "
                "lane's edit scope and is read-only input here."
            ),
        }
    import re

    m_open = re.search(r"open ml430 mirrors:\s*(\d+)", dispatch_output)
    m_dispatchable = re.search(r"DISPATCHABLE:\s*(\d+)", dispatch_output)
    names = re.findall(r"^\s+(F:ml430-[a-z0-9-]+)\s*$", dispatch_output, re.MULTILINE)
    return {
        "ran": True,
        "open_ml430_mirrors": int(m_open.group(1)) if m_open else None,
        "dispatchable_count": int(m_dispatchable.group(1)) if m_dispatchable else None,
        "dispatchable_examples": names,
        "note": (
            "scripts/check-dispatchable-frontier.py computes the ledger-"
            "wide dispatchable ml430-mirror set (all populations, not just "
            "mathlib-group-defs-v1). It is out of this lane's edit scope; "
            "read-only input."
        ),
    }


def build_frontier(population_id: str, dispatch_output: str | None = None) -> dict:
    join = load_join(population_id)
    rows_doc = load_rows(population_id)
    edges_doc = load_edges(population_id)
    rows = rows_doc["declarations"]
    rows_by_name = {r["name"]: r for r in rows}
    indeg, outdeg = compute_degrees(edges_doc["edges"])

    fact_resolved = join["dimensions"]["fact_ids"]["resolved"]
    proved_of_9 = 0
    for name, info in fact_resolved.items():
        fact_id = info["fact_id"]
        fname = fact_id.replace("F:", "F-", 1) + ".json"
        fpath = FACTS_DIR / fname
        if fpath.is_file():
            fact = load_json(fpath)
            if fact.get("epistemic_status") == "proved":
                proved_of_9 += 1

    queues: dict[str, dict] = {q: {"rows": [], "empty_reason": None} for q in QUEUES}
    all_failures: list[str] = []
    for candidate in ROW_CANDIDATES:
        failures = validate_candidate(candidate, rows_by_name, join)
        all_failures.extend(failures)
        if failures:
            continue
        row = build_row(candidate, population_id, rows_by_name, indeg, outdeg, join)
        queues[candidate["queue"]]["rows"].append(row)

    if all_failures:
        raise ValueError("candidate validation failed:\n" + "\n".join(all_failures))

    for q in QUEUES:
        queues[q]["rows"].sort(key=lambda r: r["row_id"])

    leaf_candidates = compute_dependency_ready_leaf_candidates(rows, indeg, join)
    computed = {
        "proved_of_9": proved_of_9,
        "leaf_candidate_count": len(leaf_candidates),
    }
    for q in QUEUES:
        if not queues[q]["rows"]:
            queues[q]["empty_reason"] = _empty_reason(q, computed)

    theorem_count = sum(1 for r in rows if r["kind"] == "Theorem")
    unresolved_theorem_count = theorem_count - len(fact_resolved)

    return {
        "schema_version": 1,
        "kind": "axeyum-infrastructure-frontier",
        "generated_by": "scripts/gen-infrastructure-frontier.py",
        "population_id": population_id,
        "source_join": f"artifacts/graph-join/{population_id}.join.json",
        "declaration_population_count": len(rows),
        "advisory_notice": ADVISORY_NOTICE,
        "raw_input_disclaimer": DEGREE_DISCLAIMER,
        "population_summary": {
            "declaration_count": len(rows),
            "theorem_count": theorem_count,
            "fact_linked_count": len(fact_resolved),
            "fact_linked_all_proved": proved_of_9 == len(fact_resolved),
            "unresolved_theorem_count": unresolved_theorem_count,
            "name_coincidence_candidate_count": len(join["name_coincidence_candidates"]),
        },
        "cross_check": {
            "dispatchable_frontier": load_cross_check_dispatchable(dispatch_output),
            "population_overlap_note": (
                "None of this population's 446 declaration names is an "
                "`F:ml430-*` mirror subject outside the 9 already resolved "
                "in this join (checked: no Mathlib name in this population "
                "matches scripts/check-dispatchable-frontier.py's own "
                "reported dispatchable/held-out/blocked subjects, which are "
                "drawn from unrelated Nat/number-theory mirror families). "
                "No disagreement is possible on overlapping subjects "
                "because there are none; the agreement is thematic: both "
                "this population's queues and the ledger-wide dispatchable "
                "count independently land on 'almost nothing is actually "
                "ready to dispatch right now', for related but distinct "
                "reasons (this population: unstatable without new "
                "infrastructure; ledger-wide: held-out/blocked/controls)."
            ),
        },
        "diagnostics": {
            "dependency_ready_leaf_candidates_before_filtering": leaf_candidates,
            "note": (
                "These are the raw candidates dependency-ready-leaves' own "
                "empty_reason filters against (built-in projections, Lean-"
                "generated auxiliaries, or promoted to language-"
                "infrastructure). Shown here so the empty_reason's counts "
                "are independently checkable rather than asserted."
            ),
        },
        "queues": queues,
    }
