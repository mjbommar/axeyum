#!/usr/bin/env python3
"""Validate `artifacts/carrier-correspondence/carrier-correspondence-v1.json`.

WHAT THIS EXISTS TO STOP
-------------------------

`docs/math-department/14-lean-lang.md` Next Ten item 4 found that reviewers 03
(classical analysis), 05 (geometry), 07 (combinatorics) and 08 (probability)
each have a carrier this repository shares with Mathlib in name only, with no
written mapping saying whether "we proved the theorem Mathlib has" is actually
true. Reviewer 03's exact complaint: a theorem this library shares with Mathlib
"may be a different theorem" because `CReal` is a Bishop setoid and Mathlib's
`Real` is a classical Cauchy quotient (ADR-0512). Before this ledger, the only
gate protecting statement identity across the Lean boundary was
`check-mirror-statement-fidelity.py`, which hash-pins ℕ/ℤ statement TEXT for the
`F:ml430-*` mirrors -- nothing recorded, per CARRIER PAIR, whether a
shared-looking theorem is the same statement, a strictly stronger or weaker
constructive one, a different object, or has no counterpart at all.

A row in the ledger is a CLAIM: "carrier X here corresponds to carrier Y in
Mathlib, graded G, because of theorem pair W." Nothing stops a row from citing a
kernel declaration that does not exist, or a grade that is not one of the five
this repository has agreed to use, or asserting a grade with no witness to back
it. This script is that stop.

WHAT IT CHECKS
--------------

  * STRUCTURE against `artifacts/ontology/carrier-correspondence.schema.json`
    (via `jsonschema` when importable, a hand-rolled subset otherwise -- see
    `validate-docir.py` for the same fallback pattern; `--require-jsonschema`
    turns the fallback into a hard failure instead of a warning).
  * The GRADE is one of the five in the closed enum -- checked again here,
    independently of the schema, because a rule this load-bearing should not
    have exactly one enforcement point.
  * WITNESS is present (non-empty) for every grade except `no-counterpart`,
    and EMPTY for `no-counterpart` -- checked independently of the schema's
    own `if`/`then` for the same reason.
  * Every name marked `verified-in-kernel-projection` (a row's `axeyum.carrier`
    read together with `axeyum.source_location`, and every
    `witness[].axeyum_theorem`) actually resolves as an `id` in
    `artifacts/autogenesis/kernel-dependency-projection-v1.json`. A row that
    claims kernel-projection verification for a name the projection does not
    have is a violation, not a warning -- this is the check that stops a
    plausible-sounding but unverified name from posing as a checked one.
  * IDs are unique across `rows[]` (the schema's own item pattern cannot
    enforce uniqueness across siblings).
  * COVERAGE: `docs/math-department/14-lean-lang.md` Next Ten item 4 names
    a minimum set of carrier pairs this ledger must hold. A row whose
    `axeyum.carrier` does not mention one of the required family names is
    invisible to this check, so deleting a row silently shrinks coverage
    without the count itself moving in an obviously wrong direction -- this
    guard catches that.
  * NON-VACUITY on `rows` (a ledger with zero rows is not evidence of
    anything) and on the kernel-projection lookup (a projection file that
    fails to parse must not be silently treated as "nothing resolves,
    everything unverified").

Exit status depends on what was found: 0 only on a non-empty, schema-valid,
fully-resolving ledger; 1 on any violation; 2 on a malformed/unreadable input.
"""

from __future__ import annotations

import argparse
import glob
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "artifacts" / "carrier-correspondence" / "carrier-correspondence-v1.json"
SCHEMA = ROOT / "artifacts" / "ontology" / "carrier-correspondence.schema.json"
KERNEL_PROJECTION = ROOT / "artifacts" / "autogenesis" / "kernel-dependency-projection-v1.json"

GRADES = {
    "same-statement",
    "constructively-stronger",
    "constructively-weaker",
    "different-object",
    "no-counterpart",
}

AXEYUM_VERIFICATIONS = {"verified-in-kernel-projection", "verified-in-source-only", "unverified"}
MATHLIB_VERIFICATIONS = {"verified-in-pinned-checkout", "unverified", "not-applicable"}

# Next Ten item 4's own list (docs/math-department/14-lean-lang.md), one
# substring per required pair. A row's `axeyum.carrier` must contain at least
# one of these for the pair to count as covered. Matched case-sensitively
# against the exact spellings the brief and the source tree both use.
REQUIRED_COVERAGE = [
    "CReal",
    "Nat.Finset",
    "Nat.Multiset",
    "AlgS.Group",
    "AlgS.CommRing",
    "AlgS.Field",
    "CPoint",
    "Nat.Graph",
    "Complex",
    "Rat matrices",
    "Rat.IsDistribution",
    "Metric",
    "IntSpace",
    "Nat.RM",
    "Provable",  # the ipc_* logic family's actual kernel namespace
]

ID_RE = re.compile(r"^CC:[a-z0-9]+(?:-[a-z0-9]+)*$")


class CarrierCorrespondenceError(RuntimeError):
    pass


def load_json(path: Path) -> Any:
    try:
        with path.open(encoding="utf-8") as fh:
            return json.load(fh)
    except OSError as exc:
        raise CarrierCorrespondenceError(f"cannot read {path}: {exc}") from exc
    except ValueError as exc:
        raise CarrierCorrespondenceError(f"malformed JSON in {path}: {exc}") from exc


def load_kernel_declaration_ids(problems: list[str]) -> set[str]:
    """The set of kernel declaration ids the projection has actually observed.

    A missing or malformed projection is NOT treated as "nothing resolves" --
    that would silently downgrade every kernel-projection-verified row to an
    unexplained failure with a misleading message. It is its own violation.
    """
    if not KERNEL_PROJECTION.exists():
        problems.append(
            f"{KERNEL_PROJECTION} does not exist -- cannot resolve any "
            "`verified-in-kernel-projection` name. Regenerate with "
            "`python3 scripts/gen-autogenesis-kernel-dependency-projection.py`."
        )
        return set()
    try:
        doc = load_json(KERNEL_PROJECTION)
    except CarrierCorrespondenceError as exc:
        problems.append(str(exc))
        return set()
    declarations = doc.get("declarations")
    if not isinstance(declarations, list) or not declarations:
        problems.append(
            f"{KERNEL_PROJECTION} carries no `declarations` array -- "
            "the projection itself looks broken, not merely stale"
        )
        return set()
    ids = {d.get("id") for d in declarations if isinstance(d, dict) and isinstance(d.get("id"), str)}
    if not ids:
        problems.append(f"{KERNEL_PROJECTION}'s `declarations` carried zero usable ids")
    return ids


def schema_check(doc: Any, problems: list[str], require_jsonschema: bool) -> None:
    try:
        import jsonschema  # type: ignore
    except ImportError:
        if require_jsonschema:
            problems.append("jsonschema is not importable and --require-jsonschema was given")
            return
        _hand_rolled_schema_check(doc, problems)
        return
    schema = load_json(SCHEMA)
    validator = jsonschema.Draft202012Validator(schema)
    for error in sorted(validator.iter_errors(doc), key=lambda e: list(e.absolute_path)):
        path = "/".join(str(p) for p in error.absolute_path) or "<root>"
        problems.append(f"schema violation at {path}: {error.message}")


def _hand_rolled_schema_check(doc: Any, problems: list[str]) -> None:
    """The subset worth having when `jsonschema` is not importable."""
    if not isinstance(doc, dict):
        problems.append("top-level document is not an object")
        return
    if doc.get("schema_version") != 1:
        problems.append("top-level `schema_version` must be 1")
    if doc.get("kind") != "axeyum-carrier-correspondence-ledger":
        problems.append("top-level `kind` must be `axeyum-carrier-correspondence-ledger`")
    rows = doc.get("rows")
    if not isinstance(rows, list):
        problems.append("`rows` must be an array")
        return
    required_row = {
        "schema_version", "kind", "id", "title", "axeyum", "mathlib",
        "grade", "reason", "witness", "provenance",
    }
    for i, row in enumerate(rows):
        if not isinstance(row, dict):
            problems.append(f"rows[{i}] is not an object")
            continue
        missing = required_row - row.keys()
        if missing:
            problems.append(f"rows[{i}] ({row.get('id', '?')}) missing required field(s): {sorted(missing)}")
        if not isinstance(row.get("id"), str) or not ID_RE.match(row.get("id", "")):
            problems.append(f"rows[{i}]: `id` {row.get('id')!r} does not match ^CC:[a-z0-9-]+$")
        title = row.get("title")
        if not isinstance(title, str) or len(title) < 16:
            problems.append(f"rows[{i}] ({row.get('id', '?')}): `title` missing or shorter than 16 chars")
        reason = row.get("reason")
        if not isinstance(reason, str) or len(reason) < 40:
            problems.append(f"rows[{i}] ({row.get('id', '?')}): `reason` missing or shorter than 40 chars")
        axeyum = row.get("axeyum")
        if not isinstance(axeyum, dict) or not axeyum.get("carrier"):
            problems.append(f"rows[{i}] ({row.get('id', '?')}): `axeyum.carrier` missing")
        mathlib = row.get("mathlib")
        if not isinstance(mathlib, dict):
            problems.append(f"rows[{i}] ({row.get('id', '?')}): `mathlib` missing")
        witness = row.get("witness")
        if not isinstance(witness, list):
            problems.append(f"rows[{i}] ({row.get('id', '?')}): `witness` must be an array")


def semantic_checks(doc: Any, kernel_ids: set[str], problems: list[str]) -> dict[str, int]:
    """Everything the JSON Schema either cannot express or should not be the
    only thing enforcing, given how load-bearing the rule is."""
    stats: dict[str, int] = {"rows": 0, "grades": {g: 0 for g in GRADES}, "witnesses": 0, "kernel_verified_names": 0}
    rows = doc.get("rows") if isinstance(doc, dict) else None
    if not isinstance(rows, list):
        return stats

    seen_ids: set[str] = set()
    for row in rows:
        if not isinstance(row, dict):
            continue
        stats["rows"] += 1
        rid = row.get("id", "<no id>")

        # G0 -- ids unique across rows[] (the schema's item pattern cannot
        # enforce cross-item uniqueness).
        if rid in seen_ids:
            problems.append(f"{rid}: duplicate `id` across rows[] -- ids must be unique")
        seen_ids.add(rid)

        # G1 -- the grade is one of the five, independently of the schema enum.
        grade = row.get("grade")
        if grade not in GRADES:
            problems.append(f"{rid}: `grade` {grade!r} is not one of {sorted(GRADES)}")
        else:
            stats["grades"][grade] += 1

        # G2 -- witness required for every grade except no-counterpart, and
        # forbidden for no-counterpart. Independent of the schema's own
        # if/then for the same field, per this checker's own discipline
        # (CLAUDE.md: "a checker that cannot fail is worse than no checker").
        witness = row.get("witness")
        witness_list = witness if isinstance(witness, list) else []
        if grade == "no-counterpart":
            if witness_list:
                problems.append(f"{rid}: grade is `no-counterpart` but `witness` is non-empty")
        else:
            if not witness_list:
                problems.append(f"{rid}: grade is {grade!r} but `witness` is empty -- every grade "
                                 "except no-counterpart requires at least one witness theorem pair")
        stats["witnesses"] += len(witness_list)

        # G3 -- no-counterpart rows must have a fully-null mathlib side.
        mathlib = row.get("mathlib") if isinstance(row.get("mathlib"), dict) else {}
        if grade == "no-counterpart":
            for field in ("counterpart", "module_path", "source_location"):
                if mathlib.get(field) is not None:
                    problems.append(f"{rid}: grade is `no-counterpart` but mathlib.{field} is not null")
            if mathlib.get("verification") != "not-applicable":
                problems.append(f"{rid}: grade is `no-counterpart` but mathlib.verification "
                                 f"is {mathlib.get('verification')!r}, not `not-applicable`")
        else:
            if not isinstance(mathlib.get("counterpart"), str) or not mathlib.get("counterpart"):
                problems.append(f"{rid}: grade is {grade!r} but mathlib.counterpart is not a "
                                 "non-empty string")

        # G4 -- every name claimed verified-in-kernel-projection actually
        # resolves. This is the check that makes "verified" mean something.
        axeyum = row.get("axeyum") if isinstance(row.get("axeyum"), dict) else {}
        av = axeyum.get("verification")
        if av not in AXEYUM_VERIFICATIONS:
            problems.append(f"{rid}: axeyum.verification {av!r} is not one of {sorted(AXEYUM_VERIFICATIONS)}")
        for w in witness_list:
            if not isinstance(w, dict):
                problems.append(f"{rid}: a witness entry is not an object")
                continue
            wv = w.get("axeyum_verification")
            if wv not in AXEYUM_VERIFICATIONS:
                problems.append(f"{rid}: witness {w.get('axeyum_theorem')!r} has "
                                 f"axeyum_verification {wv!r} not in {sorted(AXEYUM_VERIFICATIONS)}")
            if wv == "verified-in-kernel-projection":
                name = w.get("axeyum_theorem")
                stats["kernel_verified_names"] += 1
                if not isinstance(name, str) or name not in kernel_ids:
                    problems.append(
                        f"{rid}: witness names {name!r} as `verified-in-kernel-projection`, "
                        "but that id is not in artifacts/autogenesis/kernel-dependency-projection-v1.json "
                        "-- either the name is wrong or the verification tag is a guess"
                    )
            # G8 -- mathlib_theorem/mathlib_location must be null together or
            # present together (a lone null hides which half is unverified).
            mv = w.get("mathlib_theorem")
            ml = w.get("mathlib_location")
            if (mv is None) != (ml is None):
                problems.append(
                    f"{rid}: witness has mathlib_theorem={mv!r} but mathlib_location={ml!r} -- "
                    "the two must be null together or present together"
                )

    # G5 -- non-vacuity on the ledger itself.
    if stats["rows"] == 0:
        problems.append("the ledger has ZERO rows -- an empty ledger is not evidence of anything")

    # G6 -- non-vacuity on the kernel-projection cross-check specifically,
    # independent of G5: a broken projection lookup would otherwise silently
    # make every verified-in-kernel-projection witness fail with the SAME
    # generic message as a genuinely wrong name, hiding a tooling failure
    # behind what looks like 40 unrelated content failures.
    if stats["rows"] > 0 and stats["kernel_verified_names"] == 0:
        problems.append(
            "zero witnesses across the ledger claim `verified-in-kernel-projection` -- "
            "either the ledger stopped citing the kernel projection at all, or this "
            "check's own field name drifted from what the ledger writes"
        )

    # G7 -- coverage floor named by docs/math-department/14-lean-lang.md's
    # Next Ten item 4. A future edit that deletes a required row should fail
    # here even though `stats["rows"]` alone would not obviously look wrong.
    carriers = [row.get("axeyum", {}).get("carrier", "") for row in rows if isinstance(row, dict)]
    carrier_text = "\n".join(c for c in carriers if isinstance(c, str))
    missing_coverage = [req for req in REQUIRED_COVERAGE if req not in carrier_text]
    if missing_coverage:
        problems.append(
            "coverage floor (docs/math-department/14-lean-lang.md Next Ten item 4) is missing "
            f"row(s) for: {missing_coverage}"
        )

    return stats


def check_document(
    doc: Any,
    kernel_ids: set[str],
    require_jsonschema: bool = False,
) -> tuple[list[str], dict[str, int]]:
    """Run every guard over an already-loaded ledger document and an
    already-loaded kernel-projection id set. Split out from `check()` so the
    control suite can drive each guard with an in-memory fixture rather than
    writing a temp file and a temp projection for every case."""
    problems: list[str] = []
    schema_check(doc, problems, require_jsonschema)
    stats = semantic_checks(doc, kernel_ids, problems)
    stats["kernel_declaration_ids"] = len(kernel_ids)
    return problems, stats


def check(
    ledger_path: Path = LEDGER,
    require_jsonschema: bool = False,
) -> tuple[list[str], dict[str, int]]:
    doc = load_json(ledger_path)
    problems: list[str] = []
    kernel_ids = load_kernel_declaration_ids(problems)
    more_problems, stats = check_document(doc, kernel_ids, require_jsonschema)
    problems.extend(more_problems)
    return problems, stats


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0] if __doc__ else "")
    parser.add_argument("ledger", nargs="?", type=Path, default=LEDGER, help="ledger JSON file (default: the committed one)")
    parser.add_argument("--check", action="store_true", help="accepted for interface parity with the other `--check` gates; this script always checks")
    parser.add_argument("--require-jsonschema", action="store_true", help="fail instead of falling back when `jsonschema` is not importable")
    args = parser.parse_args(argv)

    try:
        problems, stats = check(args.ledger, args.require_jsonschema)
    except CarrierCorrespondenceError as exc:
        print(f"CARRIER_CORRESPONDENCE|ERROR|{exc}")
        return 2

    grades = ",".join(f"{g}:{n}" for g, n in sorted(stats.get("grades", {}).items()))
    print(
        "CARRIER_CORRESPONDENCE|rows=%d|witnesses=%d|kernel_verified_names=%d"
        "|kernel_declaration_ids=%d|grades=%s|violations=%d|verdict=%s"
        % (
            stats.get("rows", 0),
            stats.get("witnesses", 0),
            stats.get("kernel_verified_names", 0),
            stats.get("kernel_declaration_ids", 0),
            grades,
            len(problems),
            "FAIL" if problems else "PASS",
        )
    )
    for p in problems:
        print("  !! " + p)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
