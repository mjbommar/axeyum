"""`axeyum.knowledge.facts` must agree with `scripts/validate-facts.py`.

The test that matters is the differential one: a corrupt fixture ledger is run
through both implementations and the **exact error strings** are compared. A
count comparison over the committed ledger proves little, because the committed
ledger has zero errors -- both a working validator and a validator that never
reports anything pass that. So every semantic rule gets a fixture that the
script must reject, and this module must reject identically.
"""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

from axeyum.knowledge import facts
from axeyum.knowledge._paths import repo_root

ROOT = repo_root()
VALIDATOR = ROOT / "scripts" / "validate-facts.py"


# --------------------------------------------------------------------------
# fixture ledgers
# --------------------------------------------------------------------------


def _good_fact(fact_id: str = "F:fixture-one", **overrides) -> dict:
    fact = {
        "schema_version": 1,
        "id": fact_id,
        "title": "A fixture",
        "statement": "A statement held only by this fixture.",
        "formal": {
            "language": "lean4",
            "statement": "theorem fixture : True",
            "fragment": "Nat",
        },
        "epistemic_status": "open",
        "depends_on": [],
        "evidence": [],
        "provenance": {"date": "2026-08-24"},
    }
    fact.update(overrides)
    return fact


def _write_fixture_root(tmp_path: Path, ledger: list[dict], *, name: str = "ledger") -> Path:
    """Build a miniature checkout the canonical validator can be pointed at.

    The script resolves its own root from ``__file__``, so the fixture tree needs
    a ``scripts/`` copy and the schema next to the facts.
    """
    root = tmp_path / name
    (root / "scripts").mkdir(parents=True)
    (root / "artifacts" / "facts").mkdir(parents=True)
    (root / "artifacts" / "ontology").mkdir(parents=True)
    shutil.copy2(VALIDATOR, root / "scripts" / "validate-facts.py")
    shutil.copy2(
        ROOT / "artifacts" / "ontology" / "fact.schema.json",
        root / "artifacts" / "ontology" / "fact.schema.json",
    )
    for entry in ledger:
        fact = dict(entry)
        filename = fact.pop(
            "_filename", str(fact.get("id", "F:unnamed")).replace("F:", "F-") + ".json"
        )
        (root / "artifacts" / "facts" / filename).write_text(
            json.dumps(fact, indent=2) + "\n", encoding="utf-8"
        )
    return root


def _script_errors(root: Path) -> tuple[int, list[str]]:
    """Run the canonical validator over a fixture root; return (exit, errors)."""
    completed = subprocess.run(
        [sys.executable, str(root / "scripts" / "validate-facts.py")],
        capture_output=True,
        text=True,
        timeout=120,
        check=False,
    )
    errors = [
        line[len("  ERROR ") :]
        for line in completed.stderr.splitlines()
        if line.startswith("  ERROR ")
    ]
    return completed.returncode, errors


def _our_errors(root: Path) -> list[str]:
    return facts.load(root, refresh=True).validate()


# --------------------------------------------------------------------------
# the committed ledger
# --------------------------------------------------------------------------


def test_committed_ledger_matches_the_canonical_validator() -> None:
    completed = subprocess.run(
        [sys.executable, str(VALIDATOR)],
        capture_output=True,
        text=True,
        timeout=300,
        check=False,
        cwd=str(ROOT),
    )
    assert completed.returncode == 0, completed.stderr
    headline = completed.stdout.splitlines()[0]
    counted = int(headline.split(" facts checked", 1)[0])
    assert counted > 0, "a validator that examined zero facts is an inert gate"

    ledger = facts.load(ROOT, refresh=True)
    assert len(ledger) == counted
    assert ledger.validate() == []


def test_status_spread_matches_the_validator_line() -> None:
    completed = subprocess.run(
        [sys.executable, str(VALIDATOR)], capture_output=True, text=True, timeout=300, check=False
    )
    assert completed.returncode == 0
    spread = completed.stdout.splitlines()[0].split("(", 1)[1].rstrip(")")
    reported = {
        pair.split("=")[0]: int(pair.split("=")[1]) for pair in spread.split() if "=" in pair
    }
    assert reported, "no status spread parsed -- the format changed"
    assert facts.load(ROOT).status_counts() == reported


def test_novel_matches_the_validator_report() -> None:
    completed = subprocess.run(
        [sys.executable, str(VALIDATOR)], capture_output=True, text=True, timeout=300, check=False
    )
    assert completed.returncode == 0
    line = [ln for ln in completed.stdout.splitlines() if "NOVEL" in ln]
    reported = set()
    if line:
        reported = {item.strip() for item in line[0].split(":", 1)[1].split(",")}
    ours = {fact.id for fact in facts.novel(ROOT)}
    assert ours == reported


def test_axiom_free_count_matches_and_is_scoped_to_one_route() -> None:
    completed = subprocess.run(
        [sys.executable, str(VALIDATOR)], capture_output=True, text=True, timeout=300, check=False
    )
    routes_line = [ln for ln in completed.stdout.splitlines() if ln.strip().startswith("routes:")]
    assert routes_line, "the validator no longer prints a routes line"
    reported = int(routes_line[0].split(";", 1)[1].strip().split(" ", 1)[0])
    ledger = facts.load(ROOT)
    assert len(ledger.axiom_free()) == reported
    assert all(f.proof_route == "kernel-lean" for f in ledger.axiom_free())


def test_route_counts_match_the_validator() -> None:
    completed = subprocess.run(
        [sys.executable, str(VALIDATOR)], capture_output=True, text=True, timeout=300, check=False
    )
    routes_line = [ln for ln in completed.stdout.splitlines() if ln.strip().startswith("routes:")]
    body = routes_line[0].split("routes:", 1)[1].split(";", 1)[0]
    reported = {pair.split("=")[0]: int(pair.split("=")[1]) for pair in body.split() if "=" in pair}
    assert reported
    assert facts.load(ROOT).route_counts() == reported


# --------------------------------------------------------------------------
# corrupt fixtures: both implementations must reject, identically
# --------------------------------------------------------------------------


CORRUPT_CASES: list[tuple[str, list[dict]]] = [
    (
        "settled-with-nothing-checked",
        [
            _good_fact(
                epistemic_status="proved",
                proof_route="kernel-lean",
                axiom_footprint=[],
                evidence=[
                    {
                        "id": "e1",
                        "kind": "kernel-term",
                        "supports": "the statement",
                        "check_status": "not-checked",
                    }
                ],
            )
        ],
    ),
    (
        "open-carrying-evidence",
        [
            _good_fact(
                epistemic_status="open",
                evidence=[
                    {
                        "id": "e1",
                        "kind": "kernel-term",
                        "supports": "the statement",
                        "check_status": "checked",
                    }
                ],
            )
        ],
    ),
    (
        "axiom-freedom-on-a-route-that-cannot-deliver-it",
        [
            _good_fact(
                epistemic_status="proved",
                proof_route="smt-term-level",
                axiom_footprint=[],
                evidence=[
                    {
                        "id": "e1",
                        "kind": "unsat-certificate",
                        "supports": "the statement",
                        "check_status": "checked",
                    }
                ],
            )
        ],
    ),
    (
        "dangling-dependency",
        [_good_fact(depends_on=["F:does-not-exist"])],
    ),
    (
        "proved-without-a-footprint",
        [
            _good_fact(
                epistemic_status="proved",
                proof_route="kernel-lean",
                evidence=[
                    {
                        "id": "e1",
                        "kind": "kernel-term",
                        "supports": "the statement",
                        "check_status": "checked",
                    }
                ],
            )
        ],
    ),
    (
        "external-settled-without-prior-art",
        [_good_fact(external_status="proved")],
    ),
    (
        "missing-required-field",
        [{k: v for k, v in _good_fact().items() if k != "provenance"}],
    ),
    (
        "duplicate-id",
        [
            _good_fact(),
            _good_fact(
                title="A second file claiming the same id",
                _filename="F-fixture-two.json",
            ),
        ],
    ),
    (
        "settled-without-a-route",
        [
            _good_fact(
                epistemic_status="computed",
                evidence=[
                    {
                        "id": "e1",
                        "kind": "exhaustive-enumeration",
                        "supports": "the statement",
                        "check_status": "checked",
                    }
                ],
            )
        ],
    ),
    (
        "claim-ref-pointing-nowhere",
        [
            _good_fact(
                epistemic_status="computed",
                proof_route="search-certificate",
                evidence=[
                    {
                        "id": "e1",
                        "kind": "claim-ref",
                        "supports": "the statement",
                        "check_status": "checked",
                        "artifact": "artifacts/claims/nope/nope/claim.json",
                    }
                ],
            )
        ],
    ),
    (
        "unchecked-smtcomp-invocation",
        [
            _good_fact(
                epistemic_status="proved",
                proof_route="smt-term-level",
                axiom_footprint=["axeyum-ir.bool-evaluator"],
                evidence=[
                    {
                        "id": "e1",
                        "kind": "unsat-certificate",
                        "supports": "the statement",
                        "check_status": "checked",
                        "checker_command": "smtcomp_cli --evidence foo.smt2",
                    }
                ],
            )
        ],
    ),
]


@pytest.mark.parametrize("label,ledger", CORRUPT_CASES, ids=[c[0] for c in CORRUPT_CASES])
def test_corrupt_fixture_is_rejected_identically(tmp_path: Path, label: str, ledger: list) -> None:
    root = _write_fixture_root(tmp_path, ledger, name=label)
    exit_code, script_errors = _script_errors(root)
    ours = _our_errors(root)

    assert exit_code == 1, f"{label}: the canonical validator accepted a corrupt fixture"
    assert script_errors, f"{label}: the validator exited 1 but named no error"
    assert ours, f"{label}: our validator accepted what the script rejected"
    assert sorted(ours) == sorted(script_errors)


def test_clean_fixture_is_accepted_by_both(tmp_path: Path) -> None:
    """The positive control: without it, an always-reject mirror would pass."""
    ledger = [
        _good_fact("F:fixture-base"),
        _good_fact(
            "F:fixture-derived",
            depends_on=["F:fixture-base"],
            epistemic_status="proved",
            proof_route="kernel-lean",
            axiom_footprint=[],
            external_status="proved",
            provenance={"date": "2026-08-24", "prior_art": ["somebody, 1970"]},
            evidence=[
                {
                    "id": "e1",
                    "kind": "kernel-term",
                    "supports": "the statement",
                    "check_status": "checked",
                }
            ],
        ),
    ]
    root = _write_fixture_root(tmp_path, ledger, name="clean")
    exit_code, script_errors = _script_errors(root)
    assert exit_code == 0, script_errors
    assert script_errors == []
    assert _our_errors(root) == []
    assert len(facts.load(root)) == 2


# --------------------------------------------------------------------------
# accessor semantics
# --------------------------------------------------------------------------


def test_get_raises_key_error_for_an_absent_fact() -> None:
    with pytest.raises(KeyError):
        facts.get("F:there-is-no-such-fact", ROOT)


def test_missing_directory_raises_file_not_found(tmp_path: Path) -> None:
    root = _write_fixture_root(tmp_path, [], name="empty")
    (root / "artifacts" / "facts").rmdir()
    with pytest.raises(FileNotFoundError) as excinfo:
        facts.load(root, refresh=True)
    assert "artifacts/facts" in str(excinfo.value)


def test_empty_directory_is_an_empty_ledger_not_an_error(tmp_path: Path) -> None:
    root = _write_fixture_root(tmp_path, [], name="none")
    ledger = facts.load(root, refresh=True)
    assert len(ledger) == 0
    assert ledger.directory.is_dir(), "an empty answer must come from a directory we read"
    assert ledger.validate() == []


def test_by_status_partitions_every_fact() -> None:
    ledger = facts.load(ROOT)
    grouped = ledger.by_status()
    assert sum(len(v) for v in grouped.values()) == len(ledger)
    assert set(grouped) <= set(facts.STATUSES) | {"?"}


def test_two_status_axes_are_kept_apart() -> None:
    ledger = facts.load(ROOT)
    internal = ledger.by_status()
    external = ledger.by_external_status()
    assert sum(len(v) for v in external.values()) == len(ledger)
    # They are different questions and must not coincide by construction.
    assert internal != external


def test_axiom_free_is_defined_by_footprint_not_by_absence() -> None:
    ledger = facts.load(ROOT)
    for fact in ledger:
        if fact.axiom_footprint is None:
            assert not fact.is_axiom_free, f"{fact.id}: absence read as axiom-freedom"


def test_imported_facts_are_reported_apart_from_constructed_ones() -> None:
    ledger = facts.load(ROOT)
    imported = [f for f in ledger if f.is_imported]
    assert all(f.proof_route == "imported-kernel-lean" for f in imported)
    assert all(f.provenance.prior_art for f in imported)
