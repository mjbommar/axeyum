#!/usr/bin/env python3
"""Functional tests for the L2 phase G5 graph dispatcher
(scripts/lib/graph_dispatcher.py, scripts/gen-graph-dispatcher.py,
scripts/check-graph-dispatcher.py).

Guard-deletion mutation testing lives separately
(scripts/tests/test-graph-dispatcher-mutations.sh) -- this file exercises
the LOGIC (each layer's absence path, the held-out refusal, the override
ledger) against real and synthetic fixtures, run directly (no pytest
dependency, matching this repository's other `scripts/tests/*.py` files).

Every synthetic fixture that needs an isolated `overrides.jsonl` or a
missing curriculum/frontier input uses a `tempfile.TemporaryDirectory` and
monkeypatches the relevant module GLOBAL rather than mutating the real
committed `artifacts/graph-dispatcher/` -- a test run must never leave a
demo override entry in the real ledger.

Usage:
    python3 scripts/tests/test-graph-dispatcher.py
"""
from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lib"))
import graph_dispatcher as gd  # noqa: E402


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


gen_mod = load_module("gen_graph_dispatcher", REPO_ROOT / "scripts" / "gen-graph-dispatcher.py")

FAILURES: list[str] = []


def check(name: str, condition: bool, detail: str = "") -> None:
    if condition:
        print(f"PASS: {name}")
    else:
        print(f"FAIL: {name} {detail}")
        FAILURES.append(name)


def expect_dispatcher_error(name: str, fn, *args, **kwargs) -> None:
    try:
        fn(*args, **kwargs)
    except gd.DispatcherError as exc:
        check(name, True, f"(raised: {exc})")
    else:
        check(name, False, "-- expected DispatcherError, none raised")


# ---------------------------------------------------------------------------
# Layer 1: curriculum
# ---------------------------------------------------------------------------

expect_dispatcher_error(
    "missing_curriculum_file_raises",
    gd.load_curriculum_nodes, Path("/nonexistent/curriculum.toml"),
)

with tempfile.TemporaryDirectory() as td:
    empty_toml = Path(td) / "curriculum.toml"
    empty_toml.write_text("# no nodes\n", encoding="utf-8")
    expect_dispatcher_error(
        "curriculum_with_zero_nodes_raises",
        gd.load_curriculum_nodes, empty_toml,
    )

# select_destination raises when no curriculum path is referenced by any
# frontier row -- a real "layer produced no answer" case, tested with
# synthetic inputs so it does not depend on the live population ever staying
# unreferenced.
_fake_nodes = {
    "unserved-node": {
        "node_id": "unserved-node", "layer": 9, "area": "nowhere",
        "status": "planned", "title": "Nothing references this",
        "path": "docs/curriculum/09-nowhere/unserved-node.md",
    }
}
_fake_frontier_no_match = {
    "fake-pop": {
        "population_id": "fake-pop",
        "queues": {"language-infrastructure": {"rows": [
            {"row_id": "IF-LANG-deadbeef", "title": "irrelevant",
             "subject_declarations": ["Foo"], "gain_kind": "statability",
             "destination_paths": ["docs/curriculum/00-foundations/sets.md"],
             "preregistered_metric": {"description": "d", "command": "true",
                                       "baseline": 0, "expected_change": "increases"}},
        ]}},
    }
}
expect_dispatcher_error(
    "select_destination_with_no_supporting_row_raises",
    gd.select_destination, _fake_nodes, _fake_frontier_no_match,
)

# ---------------------------------------------------------------------------
# Layer 2: infrastructure frontier
# ---------------------------------------------------------------------------

with tempfile.TemporaryDirectory() as td:
    expect_dispatcher_error(
        "missing_frontier_dir_raises",
        gd.load_frontier_documents, Path(td) / "does-not-exist",
    )
    empty_dir = Path(td) / "empty"
    empty_dir.mkdir()
    expect_dispatcher_error(
        "empty_frontier_dir_raises",
        gd.load_frontier_documents, empty_dir,
    )

_destination = {"path": "docs/curriculum/00-foundations/nowhere-referenced.md", "node_id": "nowhere-referenced", "layer": 0, "title": "Nothing"}
expect_dispatcher_error(
    "select_capability_with_zero_rows_for_destination_raises",
    gd.select_capability, _destination, _fake_frontier_no_match,
)

# select_capability picks the FIRST tier with rows, and labels authority
# correctly for the piloted population/queue vs. everything else.
_dest_matched = {"path": "docs/curriculum/02-structures/groups.md", "node_id": "groups", "layer": 2, "title": "Groups"}
_frontier_two_tiers = {
    gd.PILOTED_POPULATION: {
        "population_id": gd.PILOTED_POPULATION,
        "queues": {
            "language-infrastructure": {"rows": [
                {"row_id": "IF-LANG-aaa", "title": "t1", "subject_declarations": ["X"],
                 "gain_kind": "statability", "destination_paths": ["docs/curriculum/02-structures/groups.md"],
                 "preregistered_metric": {"description": "d", "command": "true", "baseline": 0, "expected_change": "increases"}},
            ]},
            "theorem-dominators": {"rows": [
                {"row_id": "IF-DOM-bbb", "title": "t2", "subject_declarations": ["Y"],
                 "gain_kind": "independent_assurance", "destination_paths": ["docs/curriculum/02-structures/groups.md"],
                 "preregistered_metric": {"description": "d", "command": "true", "baseline": 0, "expected_change": "increases"}},
            ]},
        },
    },
}
_cap = gd.select_capability(_dest_matched, _frontier_two_tiers)
check("select_capability_prefers_higher_tier", _cap["row"]["row_id"] == "IF-LANG-aaa",
      f"-- got {_cap['row']['row_id']!r}")
check("select_capability_authoritative_in_scope", _cap["authority"] == "authoritative")

_frontier_other_pop = {
    "some-other-population": {
        "population_id": "some-other-population",
        "queues": {"language-infrastructure": {"rows": [
            {"row_id": "IF-LANG-ccc", "title": "t3", "subject_declarations": ["Z"],
             "gain_kind": "statability", "destination_paths": ["docs/curriculum/02-structures/groups.md"],
             "preregistered_metric": {"description": "d", "command": "true", "baseline": 0, "expected_change": "increases"}},
        ]}},
    }
}
_cap2 = gd.select_capability(_dest_matched, _frontier_other_pop)
check("select_capability_advisory_outside_piloted_population", _cap2["authority"] == "advisory")

# ---------------------------------------------------------------------------
# Layer 3: legal target matching -- linked vs fallback, never held-out
# ---------------------------------------------------------------------------

with tempfile.TemporaryDirectory() as td:
    facts_dir = Path(td)
    fact_path = facts_dir / "F-fake-bar-baz-deadbeef.json"
    fact_path.write_text(json.dumps({
        "id": "F:fake-bar-baz-deadbeef",
        "title": "Mathlib v4.30 source proposition Foo.bar_baz",
    }), encoding="utf-8")
    old_facts_dir = gd.FACTS_DIR
    gd.FACTS_DIR = facts_dir
    try:
        linked = gd.match_legal_target(
            {"subject_declarations": ["bar_baz"]}, ["F:fake-bar-baz-deadbeef"])
        check("match_legal_target_links_on_exact_identifier_component",
              linked["match_kind"] == "linked" and linked["fact_id"] == "F:fake-bar-baz-deadbeef",
              f"-- got {linked}")

        fallback = gd.match_legal_target(
            {"subject_declarations": ["totally_unrelated"]}, ["F:fake-bar-baz-deadbeef"])
        check("match_legal_target_falls_back_when_disjoint",
              fallback["match_kind"] == "fallback" and fallback["fact_id"] == "F:fake-bar-baz-deadbeef",
              f"-- got {fallback}")

        empty = gd.match_legal_target({"subject_declarations": ["x"]}, [])
        check("match_legal_target_empty_when_no_dispatchable_ids",
              empty["match_kind"] == "empty" and empty["fact_id"] is None)

        # Spurious-token guard: a stopword-shaped subject ("left") must NOT
        # link to a fact whose identifier merely happens to contain it as one
        # component among several unrelated ones.
        left_fact = facts_dir / "F-fake-and-or-distrib-left-cafef00d.json"
        left_fact.write_text(json.dumps({
            "id": "F:fake-and-or-distrib-left-cafef00d",
            "title": "Mathlib v4.30 source proposition Nat.and_or_distrib_left",
        }), encoding="utf-8")
        no_spurious = gd.match_legal_target(
            {"subject_declarations": ["IsLeftCancelMul", "mul_left_cancel"]},
            ["F:fake-and-or-distrib-left-cafef00d"])
        check(
            "match_legal_target_does_not_spuriously_link_on_shared_substring",
            no_spurious["match_kind"] == "fallback",
            f"-- got {no_spurious} (subject_declarations must match a WHOLE "
            "dot-separated identifier component, not a shared substring)",
        )
    finally:
        gd.FACTS_DIR = old_facts_dir

# ---------------------------------------------------------------------------
# forbidden_fact_ids composition
# ---------------------------------------------------------------------------

_dispatch_fixture = {
    "held_out": ["F:h1", "F:h2"],
    "mutation": ["F:m1"],
    "blocked": [{"fact": "F:b1", "blockers": []}],
    "dispatchable": ["F:d1"],
}
_forbidden = gd.forbidden_fact_ids(_dispatch_fixture)
check("forbidden_fact_ids_union_is_correct",
      _forbidden == {"F:h1", "F:h2", "F:m1", "F:b1"}, f"-- got {_forbidden}")
check("forbidden_fact_ids_excludes_dispatchable", "F:d1" not in _forbidden)

# ---------------------------------------------------------------------------
# End-to-end: the real, committed tree
# ---------------------------------------------------------------------------

_rec = gd.build_recommendation()
check("build_recommendation_succeeds_on_real_tree", _rec["legal_target"]["fact_id"] is not None)
check("build_recommendation_legal_target_not_held_out",
      _rec["legal_target"]["fact_id"] not in set(
          gd.run_dispatchable_frontier().get("held_out", [])))

proc = subprocess.run(
    [sys.executable, str(REPO_ROOT / "scripts" / "check-graph-dispatcher.py")],
    cwd=REPO_ROOT, capture_output=True, text=True,
)
check("check_graph_dispatcher_passes_on_committed_artifacts", proc.returncode == 0,
      f"-- exit {proc.returncode}\n{proc.stdout}\n{proc.stderr}")

proc2 = subprocess.run(
    [sys.executable, str(REPO_ROOT / "scripts" / "gen-graph-dispatcher.py"), "--check"],
    cwd=REPO_ROOT, capture_output=True, text=True,
)
check("gen_graph_dispatcher_check_matches_committed", proc2.returncode == 0,
      f"-- exit {proc2.returncode}\n{proc2.stdout}\n{proc2.stderr}")

# ---------------------------------------------------------------------------
# Override mechanism: held-out is refused BY NAME, with no ledger write; a
# real dispatchable target with a proper note succeeds and appends exactly
# one entry. Uses an isolated overrides.jsonl -- never the real ledger.
# ---------------------------------------------------------------------------

_live_dispatch = gd.run_dispatchable_frontier()
_held_out_id = sorted(_live_dispatch["held_out"])[0]
_dispatchable_id = sorted(_live_dispatch["dispatchable"])[0]

with tempfile.TemporaryDirectory() as td:
    isolated_ledger = Path(td) / "overrides.jsonl"
    old_ledger = gen_mod.OVERRIDES_JSONL
    gen_mod.OVERRIDES_JSONL = isolated_ledger
    try:
        note_path = Path(td) / "note.txt"

        # (a) held-out: refused, no ledger write, names the fact.
        note_path.write_text(f"override to {_held_out_id} because reasons reasons", encoding="utf-8")
        rec_copy = json.loads(json.dumps(_rec))
        status = gen_mod.do_override(_held_out_id, note_path, rec_copy)
        check("override_to_held_out_is_refused", status != 0)
        check("override_to_held_out_writes_no_ledger_entry", not isolated_ledger.is_file())

        # (b) missing note file: refused.
        status = gen_mod.do_override(_dispatchable_id, Path(td) / "does-not-exist.txt", rec_copy)
        check("override_with_missing_note_file_is_refused", status != 0)

        # (c) note too short: refused.
        short_note = Path(td) / "short.txt"
        short_note.write_text("no", encoding="utf-8")
        status = gen_mod.do_override(_dispatchable_id, short_note, rec_copy)
        check("override_with_short_note_is_refused", status != 0)

        # (d) note that does not name the target: refused.
        unrelated_note = Path(td) / "unrelated.txt"
        unrelated_note.write_text("this note is plenty long but names nothing relevant at all", encoding="utf-8")
        status = gen_mod.do_override(_dispatchable_id, unrelated_note, rec_copy)
        check("override_with_note_not_naming_target_is_refused", status != 0)

        # (e) legitimate override: succeeds, appends exactly one entry.
        good_note = Path(td) / "good.txt"
        good_note.write_text(
            f"Overriding to {_dispatchable_id} for this test's own reasons.",
            encoding="utf-8",
        )
        status = gen_mod.do_override(_dispatchable_id, good_note, rec_copy)
        check("override_with_valid_note_succeeds", status == 0)
        check("override_appends_exactly_one_ledger_entry",
              isolated_ledger.is_file() and len(isolated_ledger.read_text().splitlines()) == 1)
        entry = json.loads(isolated_ledger.read_text().splitlines()[0])
        check("override_ledger_entry_names_the_target", entry["overridden_to"] == _dispatchable_id)
        check("override_ledger_entry_has_evidence_note", len(entry["evidence_note"]) >= gd.MIN_EVIDENCE_NOTE_CHARS)
        check("override_reflected_in_recommendation",
              rec_copy["legal_target"]["fact_id"] == _dispatchable_id
              and rec_copy["legal_target"]["authority"] == "override")
    finally:
        gen_mod.OVERRIDES_JSONL = old_ledger

print()
if FAILURES:
    print(f"FAIL: {len(FAILURES)} test(s) failed: {FAILURES}")
    sys.exit(1)
print("OK: all graph-dispatcher functional tests passed")
