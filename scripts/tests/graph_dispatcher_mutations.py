"""Fixtures for scripts/tests/test-graph-dispatcher-mutations.sh.

One `good_*`/`bad_<GUARD>` pair per guard in scripts/check-graph-dispatcher.py.
Each `bad_<GUARD>` fixture is built to fail EXACTLY the guard named in its
own suffix and pass every other guard -- mirroring
scripts/tests/infrastructure_frontier_mutations.py's own convention.
"""
from __future__ import annotations

import copy
from pathlib import Path

ADR_0865 = "docs/research/09-decisions/adr-0865-two-of-three-g4-pilots-retain-the-graph-ranking-one-category-untested.md"
ADR_0845 = "docs/research/09-decisions/adr-0845-the-infrastructure-frontier-curates-candidates-and-validates-them-live.md"
PLANNING_RULES = "docs/plan/global/50-planning-rules.md"

PILOTED_POPULATION = "mathlib-group-defs-v1"


def write_curriculum_and_frontier(base: Path) -> tuple[Path, Path]:
    """A minimal, real, on-disk curriculum.toml + one *.frontier.json under
    base, for the MISSING_INPUTS good/bad fixtures (which need real paths,
    not just dicts -- the guard reads the filesystem)."""
    base.mkdir(parents=True, exist_ok=True)
    curriculum = base / "curriculum.toml"
    curriculum.write_text(
        '[[node]]\nid = "sets"\ntitle = "Sets"\nlayer = 0\narea = "foundations"\n'
        'prerequisites = []\nunlocks = []\n',
        encoding="utf-8",
    )
    frontier_dir = base / "frontier"
    frontier_dir.mkdir(exist_ok=True)
    (frontier_dir / "fake-pop.frontier.json").write_text(
        '{"population_id": "fake-pop", "queues": {}}', encoding="utf-8")
    return curriculum, frontier_dir


def good_row() -> dict:
    return {
        "row_id": "IF-LANG-4f071ea9a3",
        "title": "Bundled commutative-magma structure + generic commutativity",
        "subject_declarations": ["CommMagma", "mul_comm"],
        "gain_kind": "statability",
        "preregistered_metric": {
            "description": "d", "command": "true", "baseline": 0,
            "expected_change": "increases",
        },
        "destination_paths": ["docs/curriculum/02-structures/groups.md"],
    }


def good_destination() -> dict:
    return {
        "node_id": "groups", "title": "Groups", "layer": 2,
        "path": "docs/curriculum/02-structures/groups.md",
        "selection_reason": "3 rows", "candidates_considered": [],
    }


def good_capability() -> dict:
    row = good_row()
    return {
        "population_id": PILOTED_POPULATION,
        "queue": "language-infrastructure",
        "row": row,
        "authority": "authoritative",
        "authority_reason": "in scope",
        "candidates_considered": [],
    }


def good_frontier_docs() -> dict:
    return {
        PILOTED_POPULATION: {
            "population_id": PILOTED_POPULATION,
            "queues": {"language-infrastructure": {"rows": [good_row()]}},
        }
    }


def good_recommendation() -> dict:
    row = good_row()
    return {
        "schema_version": 1,
        "adr_citations": [ADR_0865, ADR_0845, PLANNING_RULES],
        "destination": {
            "node_id": "groups", "title": "Groups", "layer": 2,
            "path": "docs/curriculum/02-structures/groups.md",
            "selection_reason": "3 rows", "candidates_considered": [],
        },
        "capability": {
            "population_id": PILOTED_POPULATION,
            "queue": "language-infrastructure",
            "row_id": row["row_id"],
            "title": row["title"],
            "subject_declarations": row["subject_declarations"],
            "gain_kind": row["gain_kind"],
            "preregistered_metric": row["preregistered_metric"],
            "authority": "authoritative",
            "authority_reason": "in scope",
            "candidates_considered": [],
        },
        "legal_target": {
            "fact_id": "F:ml430-nat-and-div-two-1a2f7c33",
            "match_kind": "fallback",
            "matched_identifier": None,
            "authority": "advisory",
            "authority_reason": "unlinked fallback",
        },
        "override": None,
    }


# ---- MISSING_INPUTS ----------------------------------------------------

def missing_inputs_good(base: Path) -> tuple[Path, Path]:
    return write_curriculum_and_frontier(base)


def missing_inputs_bad_curriculum(base: Path) -> tuple[Path, Path]:
    _, frontier_dir = write_curriculum_and_frontier(base)
    return base / "does-not-exist.toml", frontier_dir


def missing_inputs_bad_frontier(base: Path) -> tuple[Path, Path]:
    curriculum, _ = write_curriculum_and_frontier(base)
    return curriculum, base / "empty-frontier-dir-not-created"


# ---- NO_DESTINATION / NO_CAPABILITY -------------------------------------

def no_destination_good() -> tuple[dict | None, str | None]:
    return good_destination(), None


def no_destination_bad() -> tuple[dict | None, str | None]:
    return None, "no destination found"


def no_capability_good() -> tuple[dict | None, str | None]:
    return good_capability(), None


def no_capability_bad() -> tuple[dict | None, str | None]:
    return None, "no capability found"


# ---- UPSTREAM_GUARD_PROPAGATION -----------------------------------------

def upstream_good_refused() -> dict | None:
    return None  # composition correctly raised DispatcherError already


def upstream_good_clean() -> dict:
    return {"_exit_code": 0, "guard_failures": []}


def upstream_bad() -> dict:
    # Upstream failed (nonzero exit / guard_failures) but the composition
    # kept a live dispatch_result instead of refusing -- exactly the bug this
    # guard exists to catch.
    return {"_exit_code": 1, "guard_failures": ["G4 empty-dispatchable-set: ..."]}


# ---- LEGAL_TARGET_PRESENT ------------------------------------------------

def legal_target_present_good() -> tuple[int, str | None]:
    return 5, "F:ml430-nat-and-self-06a84ccc"


def legal_target_present_good_empty() -> tuple[int, str | None]:
    return 0, None


def legal_target_present_bad() -> tuple[int, str | None]:
    return 0, "F:ml430-nat-and-self-06a84ccc"


# ---- HELD_OUT_NEVER_PROPOSED ----------------------------------------------

def held_out_good() -> tuple[str | None, list[str], set[str]]:
    return "F:ml430-nat-and-self-06a84ccc", [], {"F:ml430-held-out-fact"}


def held_out_bad_default() -> tuple[str | None, list[str], set[str]]:
    return "F:ml430-held-out-fact", [], {"F:ml430-held-out-fact"}


def held_out_bad_override() -> tuple[str | None, list[str], set[str]]:
    return "F:ml430-nat-and-self-06a84ccc", ["F:ml430-held-out-fact"], {"F:ml430-held-out-fact"}


# ---- AUTHORITY_SCOPE -------------------------------------------------------

def authority_scope_good() -> dict:
    return good_recommendation()


def authority_scope_bad_capability_out_of_scope() -> dict:
    rec = copy.deepcopy(good_recommendation())
    rec["capability"]["population_id"] = "some-other-population"
    rec["capability"]["authority"] = "authoritative"  # WRONG: out of scope
    return rec


def authority_scope_bad_fallback_authoritative() -> dict:
    rec = copy.deepcopy(good_recommendation())
    rec["legal_target"]["match_kind"] = "fallback"
    rec["legal_target"]["authority"] = "authoritative"  # WRONG: fallback never authoritative
    return rec


# ---- ROW_CITATION_VALID -----------------------------------------------------

def row_citation_good() -> tuple[dict, dict]:
    return good_recommendation(), good_frontier_docs()


def row_citation_bad() -> tuple[dict, dict]:
    rec = copy.deepcopy(good_recommendation())
    rec["capability"]["title"] = "a title the real row does not have"
    return rec, good_frontier_docs()


# ---- OVERRIDE_LEDGER_COMPLETE -----------------------------------------------

def override_ledger_good() -> list[dict]:
    return [{
        "overridden_to": "F:ml430-nat-and-self-06a84ccc",
        "evidence_note": "Overriding to F:ml430-nat-and-self-06a84ccc because reasons.",
        "lane": "some-lane",
    }]


def override_ledger_bad_short_note() -> list[dict]:
    return [{
        "overridden_to": "F:ml430-nat-and-self-06a84ccc",
        "evidence_note": "ok",
        "lane": "some-lane",
    }]


def override_ledger_bad_unnamed() -> list[dict]:
    return [{
        "overridden_to": "F:ml430-nat-and-self-06a84ccc",
        "evidence_note": "this note is long enough but names nothing at all here",
        "lane": "some-lane",
    }]


def override_ledger_bad_no_lane() -> list[dict]:
    return [{
        "overridden_to": "F:ml430-nat-and-self-06a84ccc",
        "evidence_note": "Overriding to F:ml430-nat-and-self-06a84ccc because reasons.",
        "lane": "unknown",
    }]


# ---- ADR_CITATION_PRESENT ---------------------------------------------------

def adr_citation_good() -> list[str]:
    return [ADR_0865, ADR_0845, PLANNING_RULES]


def adr_citation_bad_missing_0865() -> list[str]:
    return [ADR_0845, PLANNING_RULES]


def adr_citation_bad_nonexistent_path() -> list[str]:
    return [ADR_0865, "docs/research/09-decisions/adr-9999-does-not-exist.md"]
