"""Shared logic for L3 phase D2's structural theorem index.

Owned by lane `l3-d2-structural-index`
(`docs/plan/status/l3-d2-structural-index.md`, ADR-0905). Both
`scripts/gen-structural-index.py` (builds the committed artifacts) and
`scripts/check-structural-index.py` (the gate) import this module rather
than each re-deriving the query engine and the held-out exclusion, the same
"one computation, two callers" shape `scripts/lib/graph_join.py` uses for
its own gate pair.

Two things this module is deliberately built to make impossible rather than
merely documented:

1. **A held-out Mathlib fact leaking into a goal-feature record.**
   `select_eligible_mathlib_facts` is the ONLY function that reads the raw
   nursery entries, and it returns a brand-new list containing just
   `{"fact_id", "family"}` for every entry whose `partition != "held-out"`.
   Nothing downstream of that call ever holds a reference to the raw
   nursery entries again -- there is no second code path that could read a
   held-out entry's `partition` field and decide to include it anyway,
   because the raw list is not in scope.

2. **A proof value entering `mathlib-goal-features.json`.**
   `project_mathlib_goal_features` destructures exactly four keys
   (`fact_id`, `family`, `goal_head`, `hyp_count`) out of a parsed
   `formal.statement` GOAL string. It never reads `evidence`, `provenance`,
   or any field but `formal.statement` from the fact JSON, mirroring
   ADR-0800's `project_type_only`: a function that cannot leak a field it
   does not name.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NURSERY_FILES = [
    REPO_ROOT / "artifacts" / "autogenesis" / "nursery-v1.json",
    REPO_ROOT / "artifacts" / "autogenesis" / "nursery-v2-extension.json",
]
FACTS_DIR = REPO_ROOT / "artifacts" / "facts"
INDEX_DIR = REPO_ROOT / "artifacts" / "structural-index"

# The only keys a Mathlib goal-feature record is EVER allowed to carry. A
# guard (`check_no_goal_feature_leak` in the checker) asserts every emitted
# record's key set equals this one exactly.
GOAL_FEATURE_KEYS = frozenset({"fact_id", "family", "goal_head", "hyp_count"})


def sha256_of_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_nursery_raw_entries() -> list[dict[str, Any]]:
    """Read every entry from both nursery files. Callers outside this module
    should not call this directly for anything Mathlib-goal-feature-related
    -- use `select_eligible_mathlib_facts` / `held_out_fact_ids`, which are
    the two functions that ever look at `partition`."""
    entries: list[dict[str, Any]] = []
    for path in NURSERY_FILES:
        data = json.loads(path.read_text(encoding="utf-8"))
        for entry in data.get("entries", []):
            entries.append(entry)
    return entries


def held_out_fact_ids(entries: list[dict[str, Any]] | None = None) -> set[str]:
    """The external authority for exclusion -- computed fresh from the
    nursery files every time, never read back from anything this phase
    itself writes. This is the ADR-0800 MISSING-guard shape applied to
    exclusion instead of inclusion: the check must re-derive the forbidden
    set from a source the artifact under test does not control."""
    if entries is None:
        entries = load_nursery_raw_entries()
    return {e["fact_id"] for e in entries if e.get("partition") == "held-out"}


def select_eligible_mathlib_facts(
    entries: list[dict[str, Any]] | None = None,
) -> list[dict[str, str]]:
    """Held-out exclusion, applied BEFORE any feature is built.

    Returns only `{"fact_id", "family"}` pairs for entries that are BOTH not
    held-out AND sourced from Mathlib (`provenance_class ==
    "external-transcribed"`) -- this phase's "Mathlib goal features" join is
    about Mathlib-sourced propositions specifically, not this project's own
    bootstrap/mutation facts, which render their `formal.statement` in a
    different (kernel-rendered, ASCII-arrow) style this module's parser does
    not target.

    This is the one place the raw entry list is read; every other function
    in this module and in `gen-structural-index.py` / `check-structural-
    index.py` consumes only this function's return value or `mathlib-goal-
    features.json`, never the raw nursery entries again.
    """
    if entries is None:
        entries = load_nursery_raw_entries()
    eligible = []
    for e in entries:
        if e.get("partition") == "held-out":
            continue
        if e.get("provenance_class") != "external-transcribed":
            continue
        eligible.append({"fact_id": e["fact_id"], "family": e.get("family", "")})
    return eligible


_QUANTIFIER_RE = re.compile(r"[∀∃]")  # ∀ ∃
_ARROW_RE = re.compile(r"→|->")  # → or ASCII ->


def _fact_path(fact_id: str) -> Path:
    slug = fact_id.replace(":", "-", 1)
    return FACTS_DIR / f"{slug}.json"


def parse_goal_head(statement: str) -> str:
    """A coarse, honest heuristic over Lean-surface text -- not a parser.

    Strips leading quantifiers/hypotheses (crudely, by looking only at
    everything after the LAST top-level `→` this regex-based scan can find,
    which is wrong for a statement with a parenthesised hypothesis
    containing its own `→`, and this function does not pretend otherwise)
    and classifies by the first relation-like token it finds.
    """
    # Drop everything up to and including the last top-level-looking arrow.
    # This is intentionally simple: a bounded, declared heuristic, not a
    # Lean parser.
    parts = _ARROW_RE.split(statement)
    tail = parts[-1] if parts else statement
    if "↔" in tail:  # ↔
        return "Iff"
    if "≠" in tail:  # ≠
        return "Ne"
    if "≤" in tail:  # ≤
        return "Le"
    if "≥" in tail:  # ≥
        return "Ge"
    if "<" in tail:
        return "Lt"
    if ">" in tail:
        return "Gt"
    if "∣" in tail:  # ∣
        return "Dvd"
    if "=" in tail:
        return "Eq"
    if "∃" in tail:
        return "Exists"
    # Fallback for a kernel-rendered (ASCII-arrow, `Eq.{1}`-style) statement
    # that reached this parser despite the provenance filter above -- a
    # bare word-boundary constant name rather than a unicode operator.
    for token, head in (
        ("Iff", "Iff"),
        ("Eq", "Eq"),
        ("Ne", "Ne"),
        ("Le", "Le"),
        ("Lt", "Lt"),
        ("Dvd", "Dvd"),
    ):
        if re.search(rf"\b{token}\b", tail):
            return head
    return "other"


def parse_hyp_count(statement: str) -> int:
    """Number of top-level quantifiers/arrows as a coarse binder-count proxy."""
    return len(_QUANTIFIER_RE.findall(statement)) + max(
        0, len(_ARROW_RE.split(statement)) - 1
    )


def project_mathlib_goal_features(
    fact_id: str, family: str, formal_statement: str
) -> dict[str, Any]:
    """The type-only-style projection for a Mathlib-sourced fact: exactly
    `GOAL_FEATURE_KEYS`, derived only from `formal_statement` -- never from
    `evidence`, `provenance`, or any other fact-ledger field."""
    record = {
        "fact_id": fact_id,
        "family": family,
        "goal_head": parse_goal_head(formal_statement),
        "hyp_count": parse_hyp_count(formal_statement),
    }
    assert set(record.keys()) == GOAL_FEATURE_KEYS
    return record


def build_mathlib_goal_features() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    """Held-out exclusion first, THEN feature construction -- the ordering
    the D2 exit criterion asks for, made structural: `select_eligible_
    mathlib_facts` runs and returns before any fact file is even opened."""
    raw_entries = load_nursery_raw_entries()
    held_out = held_out_fact_ids(raw_entries)
    eligible = select_eligible_mathlib_facts(raw_entries)
    del raw_entries  # not read again below

    features: list[dict[str, Any]] = []
    missing_on_disk = 0
    for item in eligible:
        fact_id = item["fact_id"]
        path = _fact_path(fact_id)
        if not path.exists():
            missing_on_disk += 1
            continue
        fact = json.loads(path.read_text(encoding="utf-8"))
        statement = fact.get("formal", {}).get("statement", "")
        features.append(project_mathlib_goal_features(fact_id, item["family"], statement))

    manifest = {
        "held_out_excluded_count": len(held_out),
        "eligible_count": len(eligible),
        "features_built_count": len(features),
        "missing_on_disk_count": missing_on_disk,
        "source_files": [
            {"path": str(p.relative_to(REPO_ROOT)), "sha256": sha256_of_file(p)}
            for p in NURSERY_FILES
        ],
        "held_out_fact_ids": sorted(held_out),
    }
    return features, manifest


# --------------------------------------------------------------------------
# Query engine over artifacts/structural-index/theorems.json
# --------------------------------------------------------------------------


def load_theorems(path: Path) -> list[dict[str, Any]]:
    return json.loads(path.read_text(encoding="utf-8"))


def _full_deps(record: dict[str, Any]) -> set[str]:
    return (
        set(record.get("theorem_dependencies", []))
        | set(record.get("recursors_used", []))
        | set(record.get("definitions_used", []))
    )


def build_dependency_index(records: list[dict[str, Any]]) -> dict[str, set[str]]:
    """`dependency name -> set of declaration names whose direct
    theorem/recursor/definition dependencies include it`. The inverted index
    a `has_dependencies` query runs against."""
    index: dict[str, set[str]] = {}
    for record in records:
        for dep in _full_deps(record):
            index.setdefault(dep, set()).add(record["name"])
    return index


def normalize_local_name(name: str) -> str:
    """Spelling-insensitive local-name key: last namespace segment, lower
    case, `_` and internal capitals collapsed -- mirrors
    `shape_index::spelling_insensitive`'s intent without importing Rust."""
    local = name.rsplit(".", 1)[-1]
    return re.sub(r"[_]", "", local).lower()


class Unanswerable(Exception):
    """Raised when a query names a dependency string absent from the WHOLE
    index's dependency vocabulary -- distinct from a genuine empty match,
    mirroring `shape_index::Outcome::Unanswerable`."""


def run_query(
    records: list[dict[str, Any]],
    dep_index: dict[str, set[str]],
    query: dict[str, Any],
) -> list[dict[str, Any]]:
    """Run one fixed query and return rows with three SEPARATE signal
    columns -- `identity_match`, `structural_match`, `lexical_score` -- never
    merged into one combined score. Raises `Unanswerable` for a
    `has_dependencies` query naming an unknown dependency.

    Query kinds:
      {"kind": "dependency", "has_dependencies": [names...]}  -- AND
      {"kind": "identity", "name": "Exact.Name"}
      {"kind": "lexical", "name_like": "snake_or_camel_guess"}
    """
    kind = query["kind"]
    all_names = {r["name"] for r in records}

    if kind == "dependency":
        deps = query["has_dependencies"]
        known_vocab = set(dep_index.keys())
        unknown = [d for d in deps if d not in known_vocab]
        if unknown:
            raise Unanswerable(f"unknown dependency name(s): {unknown}")
        candidates = None
        for dep in deps:
            hits = dep_index.get(dep, set())
            candidates = hits if candidates is None else (candidates & hits)
        candidates = candidates or set()
        return [
            {
                "name": name,
                "identity_match": None,
                "structural_match": True,
                "lexical_score": None,
            }
            for name in sorted(candidates)
        ]

    if kind == "identity":
        target = query["name"]
        if target not in all_names:
            return []
        return [
            {
                "name": target,
                "identity_match": True,
                "structural_match": None,
                "lexical_score": None,
            }
        ]

    if kind == "lexical":
        needle = re.sub(r"[_]", "", query["name_like"]).lower()
        exact = query.get("name")
        rows = []
        for name in sorted(all_names):
            key = normalize_local_name(name)
            if needle in key:
                rows.append(
                    {
                        "name": name,
                        "identity_match": (name == exact) if exact else False,
                        "structural_match": None,
                        "lexical_score": 1,
                    }
                )
        return rows

    raise ValueError(f"unknown query kind {kind!r}")
