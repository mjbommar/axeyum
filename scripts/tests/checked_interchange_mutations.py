"""Fixtures for `scripts/tests/test-checked-interchange-mutations.sh`.

One `good_*` fixture per input `check-checked-interchange.py` consumes, and
one `bad_*` fixture per guard -- each `bad_*` fixture is "surgically"
constructed: every OTHER self-referential field an attacker could plausibly
keep consistent stays consistent, so a guard's removal cannot be rescued by a
different guard catching the same mutation by accident (the same discipline
`library_artifact_mutations.py` and `graph_join_mutations.py` use).
"""
from __future__ import annotations


def good_population() -> dict:
    return {
        "population_id": "credited-roots-v1",
        "expected_roots": ["Nat.a", "Nat.b", "Nat.c"],
    }


def good_live_credited_roots() -> set[str]:
    return {"Nat.a", "Nat.b", "Nat.c"}


def _root(name: str, accepted: bool = True) -> dict:
    return {
        "name": name,
        "fact_id": f"F:ml430-{name.lower()}",
        "representable": True,
        "reimport_accepted": True,
        "reimport_type_matches": True,
        "lean_accepted_stream": True,
        "lean_admitted_by_name": True,
        "status": "accepted" if accepted else "declined",
    }


def good_census() -> dict:
    return {
        "schema_version": 1,
        "population_id": "credited-roots-v1",
        "credited_roots_replay": {
            "expected": 3,
            "attempted": 3,
            "accepted": 3,
            "declined_typed": 0,
            "missing": 0,
            "extra": 0,
            "roots": [_root("Nat.a"), _root("Nat.b"), _root("Nat.c")],
        },
        "decline_mechanism_probe": {
            "synthetic": True,
            "subject": "__probe",
            "status": "declined",
            "reason": "theorem-type-not-prop",
        },
    }


# --- one bad fixture per guard ---------------------------------------------


def bad_missing_census() -> dict:
    """A root in the population's expected_roots is absent from the census's
    own roots list -- accounting counters tidied to hide it (expected/attempted
    dropped to 2, so ACCOUNTING and MANDATORY_MISSING_ZERO stay green)."""
    census = good_census()
    replay = census["credited_roots_replay"]
    replay["roots"] = [_root("Nat.a"), _root("Nat.b")]  # Nat.c dropped
    replay["expected"] = 2
    replay["attempted"] = 2
    replay["accepted"] = 2
    return census


def bad_stale_live_credited_roots() -> set[str]:
    """The live join disagrees with the population snapshot's expected_roots."""
    return {"Nat.a", "Nat.b", "Nat.z"}


def bad_accounting_census() -> dict:
    """accepted + declined_typed + missing != expected, with the roots LIST
    length kept at expected so len(roots) == expected still holds -- isolating
    the arithmetic check from the length check."""
    census = good_census()
    replay = census["credited_roots_replay"]
    replay["accepted"] = 2  # 2 + 0 + 0 != 3
    return census


def bad_mandatory_missing_nonzero_census() -> dict:
    """missing=1, with every OTHER counter kept internally consistent
    (2 + 0 + 1 == 3), so ACCOUNTING alone cannot catch this."""
    census = good_census()
    replay = census["credited_roots_replay"]
    replay["accepted"] = 2
    replay["missing"] = 1
    return census


def bad_bare_name_accept_census() -> dict:
    """One root claims status=accepted while Lean never admitted its name --
    reimport_type_matches stays True and the top-level counters stay
    untouched, isolating this from BARE_TYPE_ACCEPT and ACCOUNTING."""
    census = good_census()
    census["credited_roots_replay"]["roots"][0]["lean_admitted_by_name"] = False
    return census


def bad_bare_type_accept_census() -> dict:
    """One root claims status=accepted while its reimported type did not
    match -- lean_admitted_by_name stays True, isolating this from
    BARE_NAME_ACCEPT."""
    census = good_census()
    census["credited_roots_replay"]["roots"][0]["reimport_type_matches"] = False
    return census


def bad_decline_probe_vacuous_census() -> dict:
    """The decline probe is reported as accepted -- proving nothing about the
    decline path -- while the 9 real roots stay untouched."""
    census = good_census()
    census["decline_mechanism_probe"]["status"] = "accepted"
    return census
