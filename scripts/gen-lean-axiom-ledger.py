#!/usr/bin/env python3
"""Generate and gate the reconstruction-prelude axiom ledger from a measurement.

Every number this ledger publishes is **derived**, never authored.  That is not
style: the previous version hard-coded ``integer: 34`` in five places (a Python
constant, two row-count assertions, a trust-policy literal, and the rendered
prose), plus a unit test and ten documents.  The Int development was proved
down to **one** assumption and the published figure did not move, so this
project's own axiom ledger overstated its trusted base by 33 rows -- the rare
and embarrassing direction for a trust number to be wrong in.  The count went
stale precisely because it had been transcribed.  So it is transcribed nowhere
now, and ``--check`` is the gate that keeps it that way.

Two independent measurements, cross-checked against each other
--------------------------------------------------------------

``prelude_axiom_inventory``
    Constructs `real`, `integer` and `string` in isolated kernels and emits one
    row per admitted ``Declaration::Axiom``: ``prelude<TAB>name<TAB>type-hex``.
    This is the row-level source: names and canonical types, SHA-256 bound.

``nat_axiom_inventory --include-constructed``
    Constructs **eight** preludes -- `logic`, `nat`, `real`, `integer`, `rat`,
    `string`, and (only under the flag) the constructed `creal` and `complex`
    -- and emits the whole *trusted surface* (``axiom`` + ``opaque`` +
    ``quotient``), plus a per-prelude count line on stderr **for every prelude
    it built, including the axiom-free ones**.

The second exists because an axiom-free prelude emits no rows, so absence and
zero are indistinguishable in the first tool's output -- this repository's
standing trap, that "an empty result from a tool that was never pointed at your
subject is indistinguishable from a strong negative result".  The stderr
coverage lines are the tool declaring what it looked at.  The manifest records
the prelude set, so a prelude silently dropping out of the measurement fails
the gate rather than shrinking the published total.

The two are then cross-checked: per prelude, ``Declaration::Axiom`` row counts
must agree, the name sets must agree, and the canonical types must agree
byte-for-byte.  A filter bug in either tool (``Axiom``-only versus the full
trusted surface) shows up as a disagreement rather than as a smaller number.

What ``--check`` fails on
-------------------------

* any drift in the derived block (counts, trusted surface, prelude set) --
  reported per prelude and **with its direction**, because a rise and a fall are
  different events: a rise means something previously proved is now assumed, a
  fall is a result the ledger has not published yet.  Both fail the gate; see
  ``describe_measurement_drift``;
* any drift in a row's name or canonical type digest;
* a ledger population change -- rows added or removed -- which requires a
  deliberate ``--accept-population-change`` run that files the departed rows in
  ``retired_entries`` rather than deleting them, so a *reduction in the trusted
  surface is published as a reduction* instead of quietly shrinking a table;
* a stale count in any document listed in the manifest's ``live_documents``.

Scope limit of the document scan, stated plainly: it gates the *anchored*
count phrasings in ``COUNT_CLAIM_PATTERNS`` and requires every declared
document to yield at least one of them (so a document that stops citing the
ledger is a gate failure, not a silent pass).  Unanchored prose numbers
elsewhere in those files are not gated.
"""

from __future__ import annotations

import argparse
import datetime as _datetime
import hashlib
import json
import os
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs" / "plan" / "lean-axiom-ledger-v1.json"
OUT_MD = ROOT / "docs" / "plan" / "generated" / "lean-axiom-ledger.md"

AXIOM_ROWS_EXAMPLE = "prelude_axiom_inventory"
TRUSTED_SURFACE_EXAMPLE = "nat_axiom_inventory"

AXIOM_ROWS_COMMAND = (
    f"cargo run --quiet -p axeyum-lean-kernel --example {AXIOM_ROWS_EXAMPLE}"
)

# `--include-constructed` is NOT optional here, and the profile is not a taste
# call.  Without the flag `nat_axiom_inventory` never builds `CReal` (ADR-0512)
# or `Complex` (ADR-0521), so the two developments this repository most recently
# staked a trust claim on emit no coverage line and no rows -- an empty answer to
# a question the tool was never asked, which reads identically to "measured, and
# axiom-free".  `EXPECTED_PRELUDES` is what makes dropping the flag a gate
# failure rather than a quieter ledger.
#
# `--release` because the flag costs kernel type-checking, and the profile
# changes that by 12x: measured 2026-08-18 on this host, `--include-constructed`
# runs in 2m03s debug and 10.3s release, against a one-off marginal rebuild cost
# of 8.9s release versus 6.4s debug.  Two minutes on a gate that also runs in
# `scripts/check.sh` is the kind of cost lanes route around.
#
# Keeping the row source in DEBUG is deliberate too: the cross-check below then
# compares two profiles as well as two enumerations, so a measurement that
# depended on optimisation settings would surface as a disagreement.
TRUSTED_SURFACE_COMMAND = (
    f"cargo run --quiet --release -p axeyum-lean-kernel "
    f"--example {TRUSTED_SURFACE_EXAMPLE} -- --include-constructed"
)
TYPE_IDENTITY = "sha256 of Kernel::render_lean(declaration.ty) UTF-8 bytes"

SOURCE_PATHS = {
    "logic": "crates/axeyum-lean-kernel/src/prelude.rs",
    "nat": "crates/axeyum-lean-kernel/src/nat_prelude.rs",
    "real": "crates/axeyum-lean-kernel/src/arith_prelude.rs",
    "integer": "crates/axeyum-lean-kernel/src/int_prelude.rs",
    "rat": "crates/axeyum-lean-kernel/src/rat_prelude.rs",
    "string": "crates/axeyum-lean-kernel/src/string_prelude.rs",
    "creal": "crates/axeyum-lean-kernel/src/creal.rs",
    "complex": "crates/axeyum-lean-kernel/src/complex.rs",
}
TRUSTED_KINDS = ("axiom", "opaque", "quotient")

CLASSIFICATIONS = {
    "unclassified",
    "primitive-interface",
    "external-assumption",
    "derivable-theorem",
    "defect",
}
DISCHARGE_STATES = {
    "unreviewed",
    "retained",
    "planned",
    "in-progress",
    "discharged",
    "rejected",
}

SURFACE_COUNT_LINE = re.compile(
    r"^(?P<prelude>[A-Za-z][A-Za-z0-9_-]*): "
    r"axiom=(?P<axiom>\d+) opaque=(?P<opaque>\d+) "
    r"quotient=(?P<quotient>\d+) total_trusted=(?P<total_trusted>\d+)$"
)
ISO_DATE = re.compile(r"^\d{4}-\d{2}-\d{2}$")

# The preludes the kernel is expected to construct, as a CONSTANT rather than as
# whatever the measurement happened to report.
#
# `Measurement.preludes` is derived from `surface_counts`, so it cannot police
# coverage: delete a prelude from the measurement and it disappears from the
# derived list too, and the loop over "preludes that have axiom rows" never looks
# at it.  That blind spot was harmless while every prelude carried at least one
# axiom.  It stopped being harmless when `integer` reached zero on 2026-08-16 --
# the ledger's STRONGEST claim is precisely "axiom-free, declared by the
# measurement rather than inferred from an empty result", and for the three
# axiom-free preludes (`logic`, `nat`, `integer`) that claim rested on a
# coverage line whose absence nothing detected.  An axiom-free prelude silently
# dropping out of the inventory would have read as "still axiom-free".
#
# `test_a_prelude_dropping_out_of_coverage_fails` is the control, and it went
# green-for-the-wrong-reason the moment `integer` hit zero.
#
# Extended 2026-08-18 with `rat`, `creal` and `complex`.  `rat` had been in the
# measurement since 2026-08-17 but not in this tuple, so the second-line coverage
# guard did not cover it.  `creal`/`complex` were in NEITHER: they need
# `--include-constructed`, and a gate that pins a number for a prelude the
# command never builds passes vacuously.  Their membership here is precisely what
# makes silently dropping that flag fail.
EXPECTED_PRELUDES: tuple[str, ...] = (
    "complex",
    "creal",
    "integer",
    "logic",
    "nat",
    "rat",
    "real",
    "string",
)

# Anchored count phrasings.  Each entry is (label, pattern, quantity-per-group).
# Anchoring on ledger vocabulary -- prelude names, "ledger", "prelude
# assumptions" -- is what keeps the scan from matching unrelated integers in
# large documents.  A pattern that would match "34-row ESBMC gate" is not worth
# having.  Neither is one that matches nothing: a dead pattern gates nothing
# while looking like coverage, so `test_every_anchored_pattern_recognises_a_
# current_claim` requires each of these to fire on a declared document.  Two
# drafted patterns were deleted rather than kept for tidiness when that test
# reported them dead.
COUNT_CLAIM_PATTERNS: tuple[tuple[str, re.Pattern[str], tuple[str, ...]], ...] = (
    (
        "real N, integer N, string N",
        re.compile(r"real (\d+), integer (\d+), string (\d+)"),
        ("real", "integer", "string"),
    ),
    (
        "N real, N integer, N string",
        re.compile(r"(\d+) real, (\d+) integer, (\d+) string"),
        ("real", "integer", "string"),
    ),
    (
        "real N + integer N + string ... N",
        re.compile(r"real (\d+) \+ integer (\d+) \+ string [^0-9\n]{0,24}(\d+)"),
        ("real", "integer", "string"),
    ),
    ("N-row ledger", re.compile(r"(\d+)-row [^\n]{0,32}?ledger"), ("total",)),
    ("N prelude assumptions", re.compile(r"(\d+) prelude assumptions"), ("total",)),
    ("N prelude axioms", re.compile(r"(\d+) prelude axioms"), ("total",)),
    (
        "integer prelude's N assumptions",
        re.compile(r"integer prelude(?:'|\u2019)s (\d+) assumptions?"),
        ("integer",),
    ),
)


class LedgerError(RuntimeError):
    """The source inventory or ledger is malformed."""


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def entry_key(entry: dict[str, Any]) -> tuple[str, str]:
    return str(entry["prelude"]), str(entry["name"])


def digest(canonical_type: str) -> str:
    return hashlib.sha256(canonical_type.encode()).hexdigest()


def decode_type(field: str, where: str) -> str:
    try:
        return bytes.fromhex(field).decode("utf-8")
    except (ValueError, UnicodeDecodeError) as error:
        raise LedgerError(f"{where}: invalid UTF-8 type hex") from error


def run_example(command: str) -> tuple[str, str]:
    environment = os.environ.copy()
    environment["CARGO_TERM_COLOR"] = "never"
    completed = subprocess.run(
        command.split(),
        cwd=ROOT,
        env=environment,
        check=False,
        capture_output=True,
        text=True,
    )
    if completed.returncode != 0:
        raise LedgerError(
            f"inventory command failed ({completed.returncode}): {command}: "
            f"{completed.stderr.strip()}"
        )
    return completed.stdout, completed.stderr


class Measurement:
    """What the kernel actually admits, as two cross-checked enumerations."""

    def __init__(
        self,
        axiom_rows: list[dict[str, str]],
        surface_rows: list[dict[str, str]],
        surface_counts: dict[str, dict[str, int]],
    ) -> None:
        self.axiom_rows = axiom_rows
        self.surface_rows = surface_rows
        self.surface_counts = surface_counts

    @property
    def preludes(self) -> list[str]:
        return sorted(self.surface_counts)

    @property
    def axiom_counts(self) -> dict[str, int]:
        counted = Counter(row["prelude"] for row in self.axiom_rows)
        counts = {prelude: counted.get(prelude, 0) for prelude in self.preludes}
        counts["total"] = sum(counts.values())
        return counts

    def derived_block(self) -> dict[str, Any]:
        return {
            "axiom_rows_command": AXIOM_ROWS_COMMAND,
            "trusted_surface_command": TRUSTED_SURFACE_COMMAND,
            "type_identity": TYPE_IDENTITY,
            "preludes": self.preludes,
            "trusted_surface": {
                prelude: dict(self.surface_counts[prelude])
                for prelude in self.preludes
            },
            "axiom_counts": self.axiom_counts,
        }

    def derived_trust_policy(self, authored: dict[str, Any]) -> dict[str, Any]:
        names = sorted(
            row["name"] for row in self.axiom_rows if row["prelude"] == "integer"
        )
        count = len(names)
        noun = "assumption" if count == 1 else "assumptions"
        if count == 0:
            disclosure = (
                "The integer prelude admits no assumption; a checked dependency "
                "closure using it inherits nothing from this ledger."
            )
        else:
            listed = ", ".join(f"`{name}`" for name in names) if count <= 4 else ""
            suffix = f" ({listed})" if listed else ""
            disclosure = (
                f"Any checked dependency closure using the integer prelude must "
                f"disclose {count} {noun}{suffix}; credited Rado rigidity uses "
                f"the zero-axiom Nat prefix-deficit encoding instead."
            )
        return {
            "adr": authored.get("adr"),
            "supersedes": authored.get("supersedes"),
            "integer_assumptions": count,
            "integer_assumption_names": names,
            "publication_rule": disclosure,
        }


def parse_axiom_rows(stdout: str) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for number, line in enumerate(stdout.splitlines(), start=1):
        parts = line.split("\t")
        if len(parts) != 3:
            raise LedgerError(
                f"axiom inventory line {number} must have three tab-separated fields"
            )
        prelude, name, type_hex = parts
        if not prelude or not name:
            raise LedgerError(f"axiom inventory line {number}: empty prelude or name")
        canonical_type = decode_type(type_hex, f"axiom inventory line {number}")
        rows.append(
            {
                "prelude": prelude,
                "name": name,
                "canonical_type": canonical_type,
                "type_sha256": digest(canonical_type),
            }
        )
    keys = [entry_key(row) for row in rows]
    if keys != sorted(keys):
        raise LedgerError("axiom inventory must be sorted by prelude and name")
    if len(set(keys)) != len(keys):
        raise LedgerError("axiom inventory contains duplicate prelude/name keys")
    return rows


def parse_trusted_surface(
    stdout: str, stderr: str
) -> tuple[list[dict[str, str]], dict[str, dict[str, int]]]:
    counts: dict[str, dict[str, int]] = {}
    for line in stderr.splitlines():
        match = SURFACE_COUNT_LINE.match(line.strip())
        if match is None:
            continue
        prelude = match.group("prelude")
        if prelude in counts:
            raise LedgerError(f"trusted surface declares {prelude!r} twice")
        counts[prelude] = {
            kind: int(match.group(kind)) for kind in (*TRUSTED_KINDS, "total_trusted")
        }
    if not counts:
        # Liveness: the coverage declaration is the entire reason this second
        # measurement exists.  A run that produced none of it has told us
        # nothing, and must never read as "no axioms anywhere".
        raise LedgerError(
            "trusted surface command emitted no per-prelude coverage lines; "
            "the measurement cannot be distinguished from a tool that ran "
            "against nothing"
        )

    rows: list[dict[str, str]] = []
    for number, line in enumerate(stdout.splitlines(), start=1):
        parts = line.split("\t")
        if len(parts) != 4:
            raise LedgerError(
                f"trusted surface line {number} must have four tab-separated fields"
            )
        prelude, kind, name, type_hex = parts
        if kind not in TRUSTED_KINDS:
            raise LedgerError(f"trusted surface line {number}: unknown kind {kind!r}")
        if prelude not in counts:
            raise LedgerError(
                f"trusted surface line {number}: prelude {prelude!r} emitted a row "
                "but declared no coverage line"
            )
        canonical_type = decode_type(type_hex, f"trusted surface line {number}")
        rows.append(
            {
                "prelude": prelude,
                "kind": kind,
                "name": name,
                "canonical_type": canonical_type,
                "type_sha256": digest(canonical_type),
            }
        )

    for prelude, declared in counts.items():
        for kind in TRUSTED_KINDS:
            observed = sum(
                1 for row in rows if row["prelude"] == prelude and row["kind"] == kind
            )
            if observed != declared[kind]:
                raise LedgerError(
                    f"trusted surface {prelude}: declared {kind}={declared[kind]} "
                    f"but emitted {observed} rows"
                )
        if declared["total_trusted"] != sum(declared[kind] for kind in TRUSTED_KINDS):
            raise LedgerError(
                f"trusted surface {prelude}: total_trusted disagrees with its parts"
            )
    return rows, counts


def cross_check(measurement: Measurement) -> None:
    """The two enumerations must agree, or neither is trustworthy."""
    axiom_by_key = {entry_key(row): row for row in measurement.axiom_rows}
    surface_by_key = {
        entry_key(row): row for row in measurement.surface_rows if row["kind"] == "axiom"
    }
    for prelude, declared in measurement.surface_counts.items():
        observed = sum(
            1 for row in measurement.axiom_rows if row["prelude"] == prelude
        )
        if observed != declared["axiom"]:
            raise LedgerError(
                f"the two inventories disagree on {prelude}: "
                f"{AXIOM_ROWS_EXAMPLE} emitted {observed} axiom rows, "
                f"{TRUSTED_SURFACE_EXAMPLE} declared "
                f"axiom={declared['axiom']}"
            )
    for prelude in EXPECTED_PRELUDES:
        if prelude not in measurement.surface_counts:
            raise LedgerError(
                f"{prelude!r} has no coverage line in the trusted surface "
                "measurement; an axiom-free prelude that vanishes reads as "
                "'still axiom-free', which is the one thing this ledger must "
                "never say by omission"
            )
    for prelude in {row["prelude"] for row in measurement.axiom_rows}:
        if prelude not in measurement.surface_counts:
            raise LedgerError(
                f"{prelude!r} has axiom rows but no coverage line in the trusted "
                "surface measurement"
            )
    covered = {row["prelude"] for row in measurement.axiom_rows}
    left = {key for key in axiom_by_key if key[0] in covered}
    right = {key for key in surface_by_key if key[0] in covered}
    if left != right:
        raise LedgerError(
            "the two inventories name different axioms: "
            f"only in axiom rows {sorted(left - right)}, "
            f"only in trusted surface {sorted(right - left)}"
        )
    for key in sorted(left):
        if axiom_by_key[key]["canonical_type"] != surface_by_key[key]["canonical_type"]:
            raise LedgerError(
                f"{key[0]}::{key[1]}: the two inventories render different "
                "canonical types"
            )


def measure() -> Measurement:
    axiom_stdout, _ = run_example(AXIOM_ROWS_COMMAND)
    surface_stdout, surface_stderr = run_example(TRUSTED_SURFACE_COMMAND)
    measurement = Measurement(
        parse_axiom_rows(axiom_stdout),
        *parse_trusted_surface(surface_stdout, surface_stderr),
    )
    cross_check(measurement)
    return measurement


def load_manifest() -> dict[str, Any]:
    with MANIFEST.open(encoding="utf-8") as handle:
        return json.load(handle)


def scan_live_document(
    path: str, text: str, counts: dict[str, int]
) -> list[str]:
    """Gate a document's anchored ledger-count claims; require at least one."""
    failures: list[str] = []
    matched = 0
    for label, pattern, quantities in COUNT_CLAIM_PATTERNS:
        for match in pattern.finditer(text):
            matched += 1
            for group, quantity in enumerate(quantities, start=1):
                claimed = int(match.group(group))
                actual = counts.get(quantity)
                if claimed != actual:
                    failures.append(
                        f"{path}: stale ledger count in {label!r}: claims "
                        f"{quantity}={claimed}, measured {actual} "
                        f"(context: {match.group(0)!r})"
                    )
    if matched == 0:
        failures.append(
            f"{path}: declared as a live ledger citation but states no recognised "
            "count claim; either restore the citation or drop the path from "
            "live_documents"
        )
    return failures


REPIN = "python3 scripts/gen-lean-axiom-ledger.py"
REPIN_POPULATION = (
    "python3 scripts/gen-lean-axiom-ledger.py --accept-population-change "
    "--retirement-note '<why it left>' --retirement-evidence <path>"
)

# The stable, greppable half of every drift failure.  The directional half is
# appended after it; callers and older greps key on this.
STALE = "measurement block is stale"


def _kind_breakdown(before: dict[str, Any], after: dict[str, Any]) -> str:
    return ", ".join(
        f"{kind} {before.get(kind)} -> {after.get(kind)}"
        for kind in TRUSTED_KINDS
        if before.get(kind) != after.get(kind)
    )


def describe_measurement_drift(
    committed: Any, derived: dict[str, Any]
) -> list[str]:
    """Say WHICH WAY a trusted-surface number moved, and what to do about it.

    The previous form of this check emitted two whole JSON blobs and left the
    reader to diff them.  That is adequate for a number that only ever grows and
    useless for one that moves both ways, which this one does: `integer` fell
    34 -> 1 -> 0 and `string` 1 -> 0 while the example's own doc comment still
    asserted 1 for both.

    The two directions are not the same event and must not read the same:

    * a **rise** is a regression -- something that used to be proved is now
      assumed, and the ledger is the only place that would say so;
    * a **fall** is a *result*.  The flywheel is supposed to notice that a
      prelude became axiom-free and hand out the next goal, and a gate that
      merely says "stale" invites the lane to re-run the generator without ever
      registering that the trusted base shrank.

    Both fail.  A gate whose exit status did not depend on the finding would be
    worse than no gate; what changes with direction is what the operator is told
    to do next.
    """
    if committed == derived:
        return []
    if not isinstance(committed, dict):
        return [f"{STALE}: it is not an object; run {REPIN}"]

    failures: list[str] = []
    committed_surface = committed.get("trusted_surface")
    derived_surface = derived["trusted_surface"]
    if isinstance(committed_surface, dict):
        for prelude in sorted(set(committed_surface) | set(derived_surface)):
            before = committed_surface.get(prelude)
            after = derived_surface.get(prelude)
            if before == after:
                continue
            if after is None:
                failures.append(
                    f"{STALE} -- COVERAGE LOST: `{prelude}` is pinned at "
                    f"{before.get('total_trusted') if isinstance(before, dict) else before}"
                    " but the measurement no longer builds it. An unmeasured "
                    "prelude and an axiom-free one print the same zero, so this "
                    "must never be resolved by deleting the pin: restore the "
                    "prelude to the inventory (or the `--include-constructed` "
                    "flag to its command) instead."
                )
                continue
            if before is None:
                failures.append(
                    f"{STALE} -- COVERAGE ADDED: `{prelude}` is newly measured at "
                    f"trusted surface {after['total_trusted']} and is not pinned "
                    f"yet. Pin it: {REPIN}"
                )
                continue
            if not isinstance(before, dict):
                failures.append(f"{STALE}: `{prelude}` pin is not an object; run {REPIN}")
                continue
            was = before.get("total_trusted")
            now = after["total_trusted"]
            detail = _kind_breakdown(before, after) or "kinds unchanged"
            if isinstance(was, int) and now > was:
                failures.append(
                    f"{STALE} -- REGRESSION: `{prelude}` trusted surface ROSE "
                    f"{was} -> {now} ({detail}). Something previously proved is "
                    "now assumed. Do not re-pin until you know which declaration "
                    f"lost its proof body; then: {REPIN_POPULATION}"
                )
            elif isinstance(was, int) and now < was:
                failures.append(
                    f"{STALE} -- IMPROVEMENT: `{prelude}` trusted surface FELL "
                    f"{was} -> {now} ({detail}). The trusted base shrank and "
                    "nothing recorded it -- that is a result to publish, not a "
                    "gate to satisfy. Re-pin, which files the departed rows as "
                    f"retired rather than deleting them: {REPIN_POPULATION}"
                )
            else:
                failures.append(
                    f"{STALE} -- RESHAPED: `{prelude}` trusted surface is still "
                    f"{now} but its kinds moved ({detail}). `opaque` and "
                    "`quotient` are trusted for different reasons than `axiom`; "
                    f"re-pin only once you know which: {REPIN}"
                )

    for key in sorted(set(committed) | set(derived)):
        if key == "trusted_surface" or committed.get(key) == derived.get(key):
            continue
        failures.append(
            f"{STALE}: {key} committed "
            f"{json.dumps(committed.get(key), sort_keys=True)} vs measured "
            f"{json.dumps(derived.get(key), sort_keys=True)}; run {REPIN}"
        )

    if not failures:
        failures.append(
            f"{STALE}; committed {json.dumps(committed, sort_keys=True)} vs "
            f"measured {json.dumps(derived, sort_keys=True)}"
        )
    return failures


def validate_manifest(data: dict[str, Any], measurement: Measurement) -> list[str]:
    failures: list[str] = []
    if data.get("version") != 2:
        failures.append("manifest version must be 2")

    population_as_of = data.get("population_as_of")
    if not isinstance(population_as_of, str) or not ISO_DATE.match(population_as_of):
        failures.append("population_as_of must be an ISO date")

    derived = measurement.derived_block()
    failures.extend(describe_measurement_drift(data.get("measurement"), derived))

    authored_policy = data.get("trust_policy")
    if not isinstance(authored_policy, dict):
        failures.append("trust_policy must be an object")
        authored_policy = {}
    expected_policy = measurement.derived_trust_policy(authored_policy)
    if authored_policy != expected_policy:
        failures.append(
            "trust_policy is stale; its counts and publication rule are derived "
            f"from the measurement: expected {json.dumps(expected_policy, sort_keys=True)}"
        )
    for field in ("adr", "supersedes"):
        value = authored_policy.get(field)
        if field == "supersedes" and value is None:
            continue
        if not isinstance(value, str) or not (ROOT / value).is_file():
            failures.append(f"trust_policy.{field} must name an existing file")

    if set(data.get("classification_definitions", {})) != CLASSIFICATIONS:
        failures.append("classification definitions do not match the allowed states")
    if set(data.get("discharge_definitions", {})) != DISCHARGE_STATES:
        failures.append("discharge definitions do not match the allowed states")

    entries = data.get("entries")
    retired = data.get("retired_entries")
    if not isinstance(entries, list) or not all(isinstance(e, dict) for e in entries):
        return failures + ["entries must be a list of objects"]
    if not isinstance(retired, list) or not all(isinstance(e, dict) for e in retired):
        return failures + ["retired_entries must be a list of objects"]

    failures.extend(validate_rows(entries, measurement))
    failures.extend(validate_retired(retired, entries, measurement))

    live_documents = data.get("live_documents")
    if not isinstance(live_documents, list) or not live_documents:
        failures.append("live_documents must be a non-empty list")
    else:
        if live_documents != sorted(live_documents):
            failures.append("live_documents must be sorted")
        counts = measurement.axiom_counts
        for path_text in live_documents:
            if not isinstance(path_text, str):
                failures.append("live_documents entries must be strings")
                continue
            target = ROOT / path_text
            if not target.is_file():
                failures.append(f"live_documents path does not exist: {path_text}")
                continue
            failures.extend(
                scan_live_document(
                    path_text, target.read_text(encoding="utf-8"), counts
                )
            )
    return failures


def validate_rows(
    entries: list[dict[str, Any]], measurement: Measurement
) -> list[str]:
    failures: list[str] = []
    keys = [entry_key(entry) for entry in entries]
    if keys != sorted(keys):
        failures.append("entries must be sorted by prelude and name")
    if len(set(keys)) != len(keys):
        failures.append("entries contain duplicate prelude/name keys")

    actual_by_key = {entry_key(row): row for row in measurement.axiom_rows}
    ledger_by_key = {entry_key(row): row for row in entries}
    missing = sorted(set(actual_by_key) - set(ledger_by_key))
    extra = sorted(set(ledger_by_key) - set(actual_by_key))
    if missing:
        failures.append(
            f"ledger is missing admitted axioms {missing}; rerun with "
            "--accept-population-change"
        )
    if extra:
        failures.append(
            f"ledger carries rows the kernel no longer admits {extra}; rerun with "
            "--accept-population-change to file them as retired rather than "
            "deleting the record of a discharged assumption"
        )

    for entry in entries:
        key = entry_key(entry)
        label = f"{key[0]}::{key[1]}"
        actual = actual_by_key.get(key)
        if actual is not None:
            if entry.get("canonical_type") != actual["canonical_type"]:
                failures.append(f"{label}: canonical type drift")
            if entry.get("type_sha256") != actual["type_sha256"]:
                failures.append(f"{label}: type digest drift")
        failures.extend(validate_common_row(entry, label))
        if entry.get("classification") not in CLASSIFICATIONS:
            failures.append(f"{label}: invalid classification")
        if entry.get("discharge_status") not in DISCHARGE_STATES:
            failures.append(f"{label}: invalid discharge_status")
        evidence = entry.get("discharge_evidence")
        if not isinstance(evidence, list):
            failures.append(f"{label}: discharge_evidence must be a list")
            evidence = []
        for path_text in evidence:
            if not isinstance(path_text, str) or not (ROOT / path_text).is_file():
                failures.append(f"{label}: missing discharge evidence {path_text!r}")
        if entry.get("discharge_status") == "discharged" and not evidence:
            failures.append(f"{label}: discharged row requires retained evidence")
        if (
            entry.get("classification") == "derivable-theorem"
            and entry.get("discharge_status") == "retained"
        ):
            failures.append(f"{label}: derivable theorem cannot be retained as an axiom")
    return failures


def validate_common_row(entry: dict[str, Any], label: str) -> list[str]:
    failures: list[str] = []
    stored_digest = str(entry.get("type_sha256", ""))
    if len(stored_digest) != 64 or any(
        char not in "0123456789abcdef" for char in stored_digest
    ):
        failures.append(f"{label}: type_sha256 must be lowercase 64-hex")
    canonical_type = entry.get("canonical_type")
    if not isinstance(canonical_type, str) or not canonical_type:
        failures.append(f"{label}: canonical_type is required")
    elif digest(canonical_type) != stored_digest:
        failures.append(f"{label}: stored type and digest disagree")
    prelude = entry.get("prelude")
    source_path = entry.get("source_path")
    if source_path != SOURCE_PATHS.get(prelude):
        failures.append(f"{label}: wrong source_path")
    elif not (ROOT / source_path).is_file():
        failures.append(f"{label}: source_path does not exist")
    for field in ("owner", "review_owner", "note"):
        if not entry.get(field):
            failures.append(f"{label}: missing non-empty {field}")
    return failures


def validate_retired(
    retired: list[dict[str, Any]],
    entries: list[dict[str, Any]],
    measurement: Measurement,
) -> list[str]:
    failures: list[str] = []
    keys = [entry_key(entry) for entry in retired]
    if keys != sorted(keys):
        failures.append("retired_entries must be sorted by prelude and name")
    if len(set(keys)) != len(keys):
        failures.append("retired_entries contain duplicate prelude/name keys")
    live = {entry_key(entry) for entry in entries}
    admitted = {entry_key(row) for row in measurement.axiom_rows}
    for entry in retired:
        key = entry_key(entry)
        label = f"{key[0]}::{key[1]}"
        if key in live:
            failures.append(f"{label}: is both live and retired")
        if key in admitted:
            failures.append(
                f"{label}: is retired but the kernel still admits it as an axiom"
            )
        failures.extend(validate_common_row(entry, label))
        retired_on = entry.get("retired_on")
        if not isinstance(retired_on, str) or not ISO_DATE.match(retired_on):
            failures.append(f"{label}: retired_on must be an ISO date")
        if not entry.get("retirement_note"):
            failures.append(f"{label}: missing non-empty retirement_note")
        evidence = entry.get("retirement_evidence")
        if not isinstance(evidence, list) or not evidence:
            failures.append(f"{label}: retirement_evidence must be a non-empty list")
            evidence = []
        for path_text in evidence:
            if not isinstance(path_text, str) or not (ROOT / path_text).is_file():
                failures.append(f"{label}: missing retirement evidence {path_text!r}")
    return failures


def md_escape(value: str) -> str:
    return value.replace("|", "\\|").replace("\n", " ")


def render(data: dict[str, Any]) -> str:
    entries = data["entries"]
    retired = data["retired_entries"]
    block = data["measurement"]
    counts = block["axiom_counts"]
    surface = block["trusted_surface"]
    policy = data["trust_policy"]
    classifications = Counter(entry["classification"] for entry in entries)
    discharges = Counter(entry["discharge_status"] for entry in entries)
    real_names = {entry["name"] for entry in entries if entry["prelude"] == "real"}
    int_names = {entry["name"] for entry in entries if entry["prelude"] == "integer"}
    shared = sorted(real_names & int_names)
    axiom_free = [
        prelude
        for prelude in block["preludes"]
        if surface[prelude]["total_trusted"] == 0
    ]
    with_axioms = [
        prelude for prelude in block["preludes"] if counts[prelude] > 0
    ]
    triple = ", ".join(f"{prelude} {counts[prelude]}" for prelude in with_axioms)
    retired_by_date: Counter[str] = Counter(
        entry["retired_on"] for entry in retired
    )
    adr_number = re.search(r"adr-(\d{4})", policy["adr"] or "")
    adr_label = f"ADR-{adr_number.group(1)}" if adr_number else "the trust-policy ADR"
    adr_link = f"../../research/09-decisions/{Path(policy['adr']).name}"

    lines = [
        "# Lean reconstruction prelude axiom ledger",
        "",
        "> **Generated; do not edit by hand.** Source: "
        "[`docs/plan/lean-axiom-ledger-v1.json`](../lean-axiom-ledger-v1.json). "
        "Regenerate with `python3 scripts/gen-lean-axiom-ledger.py`; use `--check` "
        "to rebuild the isolated kernel preludes and reject name/type/count drift.",
        "",
        "This ledger inventories declarations actually admitted as trusted after "
        "constructing each reconstruction prelude. It is not a call-site grep, and "
        "type well-formedness is not a proof that an assumption is true.",
        "",
        "**No number below is authored.** Every count is derived from the two "
        "measurements named under [Machine-checked contract](#machine-checked-contract) "
        "and re-derived by `--check`. The previous revision hard-coded them, and "
        "when the Int development was proved down this ledger kept publishing a "
        "trusted base 33 rows larger than the one the kernel actually admits.",
        "",
        "## Snapshot",
        "",
        f"- **{counts['total']} total assumptions:** {triple}.",
        "- Axiom-free preludes, enumerated rather than inferred from absence: "
        + (", ".join(f"`{prelude}`" for prelude in axiom_free) if axiom_free else "none")
        + ". An axiom-free prelude emits no rows, so the measurement declares its "
        "own coverage; a prelude that silently stopped being built fails the gate "
        "instead of shrinking the total.",
        f"- {len(shared)} names are shared by the isolated real and integer "
        "preludes; ADR-0387's `Int.*` / `Real.*` namespaces make the packages "
        "composable.",
        f"- Integer trust policy: [{adr_label}]({adr_link}) — "
        + policy["publication_rule"],
        f"- **{len(retired)} assumptions have been retired** from the trusted "
        "surface since this ledger was first frozen; they are kept below rather "
        "than deleted, because a reduction in the trusted base is the result, not "
        "a smaller table.",
        "- Classification: "
        + ", ".join(f"{key} {classifications[key]}" for key in sorted(classifications))
        + ".",
        "- Discharge: "
        + ", ".join(f"{key} {discharges[key]}" for key in sorted(discharges))
        + ".",
        "",
        "## Trusted surface by prelude",
        "",
        "Counts are over the whole trusted surface, not `Declaration::Axiom` alone: "
        "`Opaque` has no proof body and `Quotient` admits `Quot.sound`.",
        "",
        "| Prelude | Axiom | Opaque | Quotient | Trusted total | Ledger rows |",
        "|---|---|---|---|---|---|",
    ]
    for prelude in block["preludes"]:
        row = surface[prelude]
        lines.append(
            f"| `{prelude}` | {row['axiom']} | {row['opaque']} | {row['quotient']} | "
            f"{row['total_trusted']} | {counts[prelude]} |"
        )

    lines.extend(
        [
            "",
            "## Machine-checked contract",
            "",
            f"- Row source: `{block['axiom_rows_command']}`.",
            f"- Coverage source: `{block['trusted_surface_command']}` — enumerates "
            f"{len(block['preludes'])} preludes and declares a per-prelude count "
            "line for each, including the axiom-free ones.",
            "- The two are cross-checked against each other: per-prelude axiom "
            "counts, name sets, and canonical types must all agree, so a filter "
            "bug in either shows up as a disagreement rather than as a smaller "
            "number.",
            f"- Type identity: {block['type_identity']}.",
            "- Any added/removed axiom, renamed declaration, or canonical type "
            "change fails validation before the generated ledger can remain "
            "current. A population change additionally requires an explicit "
            "`--accept-population-change` run.",
            "- **Every prelude above is pinned by value, and a moved number is "
            "reported with its direction.** A *rise* is a regression — something "
            "previously proved is now assumed. A *fall* is a result this ledger "
            "has not published yet, and it is the direction a blanket "
            "axiom-free assertion structurally cannot see, because that "
            "assertion only ever becomes more true. Both fail the gate; what "
            "differs is what the operator is told to do next.",
            "- Every row has source, semantic classification, owner, review owner, "
            "discharge state, and retained-evidence fields.",
            "- `discharged` requires a real repository evidence path; a "
            "`derivable-theorem` may not be marked `retained`.",
            "- Documents that cite these counts are listed in the manifest's "
            "`live_documents` and scanned: a stale count fails the gate, and so "
            "does a document that stops citing the ledger at all.",
            "",
            "## Ledger",
            "",
            "| Prelude | Name | Type SHA-256 | Classification | Discharge | Owner | Source |",
            "|---|---|---|---|---|---|---|",
        ]
    )
    for entry in entries:
        source = f"[source](../../../{entry['source_path']})"
        lines.append(
            f"| `{entry['prelude']}` | `{md_escape(entry['name'])}` | "
            f"`{entry['type_sha256']}` | `{entry['classification']}` | "
            f"`{entry['discharge_status']}` | `{entry['owner']}` / "
            f"`{entry['review_owner']}` | {source} |"
        )

    lines.extend(
        [
            "",
            "## Retired assumptions",
            "",
            "Rows the kernel no longer admits. They are retained because the "
            "interesting fact about a trust ledger is which way it moved.",
            "",
        ]
    )
    if retired:
        lines.append(
            "Retired by date: "
            + ", ".join(
                f"{date} ({retired_by_date[date]})"
                for date in sorted(retired_by_date)
            )
            + "."
        )
        lines.extend(
            [
                "",
                "| Prelude | Name | Retired | Type SHA-256 | Note |",
                "|---|---|---|---|---|",
            ]
        )
        for entry in retired:
            lines.append(
                f"| `{entry['prelude']}` | `{md_escape(entry['name'])}` | "
                f"{entry['retired_on']} | `{entry['type_sha256']}` | "
                f"{md_escape(entry['retirement_note'])} |"
            )
    else:
        lines.append("None yet.")

    lines.extend(
        [
            "",
            "## Shared real/integer names",
            "",
            "ADR-0387 requires this set to remain empty so integer and real "
            "packages can coexist without declaration aliasing:",
            "",
            (", ".join(f"`{name}`" for name in shared) if shared else "None") + ".",
            "",
            "Read this weakly: it compares **ledger rows**, and the integer "
            f"prelude now contributes {counts.get('integer', 0)} of them, so an "
            "empty intersection here is close to arithmetically forced. The "
            "aliasing hazard ADR-0387 names is over whole environments, and that "
            "is checked in the kernel, not here.",
            "",
            "## Next classification gate",
            "",
            "Every live row must hold exactly one of `primitive-interface`, "
            "`external-assumption`, `derivable-theorem`, or `defect`, with a "
            "discharge target, and must preserve its type digest while the "
            "assumption remains live. An axiom-reduction claim is credited only "
            "when this ledger observes the runtime population fall — which is now "
            "the same event that updates this file.",
            "",
        ]
    )
    return "\n".join(lines)


def refresh(data: dict[str, Any], measurement: Measurement) -> dict[str, Any]:
    data["measurement"] = measurement.derived_block()
    data["trust_policy"] = measurement.derived_trust_policy(
        data.get("trust_policy") or {}
    )
    return data


def accept_population_change(
    data: dict[str, Any],
    measurement: Measurement,
    retired_on: str,
    note: str,
    evidence: list[str],
) -> tuple[list[str], list[str]]:
    admitted = {entry_key(row): row for row in measurement.axiom_rows}
    entries: list[dict[str, Any]] = list(data.get("entries", []))
    retired: list[dict[str, Any]] = list(data.get("retired_entries", []))
    live_keys = {entry_key(entry) for entry in entries}

    departed = [entry for entry in entries if entry_key(entry) not in admitted]
    for entry in departed:
        record = {
            key: entry[key]
            for key in ("prelude", "name", "canonical_type", "type_sha256", "source_path")
        }
        record.update(
            {
                "owner": entry.get("owner", "axeyum-lean-kernel"),
                "review_owner": entry.get("review_owner", "TL3.2"),
                "note": entry.get("note", ""),
                "retired_on": retired_on,
                "retirement_note": note,
                "retirement_evidence": list(evidence),
            }
        )
        retired.append(record)
    entries = [entry for entry in entries if entry_key(entry) in admitted]

    arrived = [key for key in sorted(admitted) if key not in live_keys]
    for key in arrived:
        row = admitted[key]
        entries.append(
            {
                **row,
                "source_path": SOURCE_PATHS[row["prelude"]],
                "classification": "unclassified",
                "owner": "axeyum-lean-kernel",
                "review_owner": "TL3.2",
                "discharge_status": "unreviewed",
                "discharge_evidence": [],
                "note": "Type is admitted and well-formed; truth or intended "
                "semantics are not yet classified.",
            }
        )
    entries.sort(key=entry_key)
    retired.sort(key=entry_key)
    data["entries"] = entries
    data["retired_entries"] = retired
    data["population_as_of"] = retired_on
    return [f"{key[0]}::{key[1]}" for key in arrived], [
        f"{entry['prelude']}::{entry['name']}" for entry in departed
    ]


def write_manifest(data: dict[str, Any]) -> None:
    ordered = {
        key: data[key]
        for key in (
            "version",
            "title",
            "population_as_of",
            "measurement",
            "trust_policy",
            "classification_definitions",
            "discharge_definitions",
            "live_documents",
            "entries",
            "retired_entries",
        )
        if key in data
    }
    ordered.update({key: value for key, value in data.items() if key not in ordered})
    MANIFEST.write_text(
        json.dumps(ordered, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check", action="store_true", help="fail on stale generated output"
    )
    parser.add_argument(
        "--accept-population-change",
        action="store_true",
        help="file rows the kernel no longer admits as retired, and add new ones "
        "as unclassified; required whenever the trusted population moves",
    )
    parser.add_argument("--retired-on", help="ISO date recorded on retired rows")
    parser.add_argument("--retirement-note", help="why the rows left the trusted surface")
    parser.add_argument(
        "--retirement-evidence",
        action="append",
        default=[],
        help="repository path evidencing the retirement (repeatable)",
    )
    args = parser.parse_args()

    try:
        measurement = measure()
    except LedgerError as error:
        print(f"LEAN_AXIOM_LEDGER_ERROR|{error}", file=sys.stderr)
        return 1

    if not MANIFEST.is_file():
        print(f"missing ledger: {relative(MANIFEST)}", file=sys.stderr)
        return 1
    data = load_manifest()

    if args.accept_population_change:
        if args.check:
            print("--check and --accept-population-change are exclusive", file=sys.stderr)
            return 1
        retired_on = args.retired_on or _datetime.date.today().isoformat()
        if not ISO_DATE.match(retired_on):
            print("--retired-on must be an ISO date", file=sys.stderr)
            return 1
        if not args.retirement_note or not args.retirement_evidence:
            print(
                "--accept-population-change requires --retirement-note and at least "
                "one --retirement-evidence path",
                file=sys.stderr,
            )
            return 1
        arrived, departed = accept_population_change(
            data, measurement, retired_on, args.retirement_note, args.retirement_evidence
        )
        print(
            f"LEAN_AXIOM_LEDGER_POPULATION|added={len(arrived)}|"
            f"retired={len(departed)}|{','.join(arrived) or '-'}|"
            f"{','.join(departed) or '-'}"
        )

    if not args.check:
        refresh(data, measurement)

    failures = validate_manifest(data, measurement)
    if failures:
        for failure in failures:
            print(f"LEAN_AXIOM_LEDGER_ERROR|{failure}", file=sys.stderr)
        return 1

    rendered = render(data)
    if args.check:
        if not OUT_MD.is_file() or OUT_MD.read_text(encoding="utf-8") != rendered:
            print(
                f"stale generated file: {relative(OUT_MD)}; run "
                "python3 scripts/gen-lean-axiom-ledger.py",
                file=sys.stderr,
            )
            return 1
    else:
        write_manifest(data)
        OUT_MD.parent.mkdir(parents=True, exist_ok=True)
        OUT_MD.write_text(rendered, encoding="utf-8")

    counts = data["measurement"]["axiom_counts"]
    surface = data["measurement"]["trusted_surface"]
    print(
        "LEAN_AXIOM_LEDGER|"
        + f"total={counts['total']}|"
        + "|".join(
            f"{prelude}={counts[prelude]}" for prelude in data["measurement"]["preludes"]
        )
        + f"|retired={len(data['retired_entries'])}"
        + f"|axiom_free={sum(1 for p in surface if surface[p]['total_trusted'] == 0)}"
        + f"|unclassified={sum(entry['classification'] == 'unclassified' for entry in data['entries'])}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
