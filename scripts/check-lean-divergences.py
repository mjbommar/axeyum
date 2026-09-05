#!/usr/bin/env python3
"""ADR-1663 gate: the Lean divergence ledger, in lean4lean's shape.

`docs/plan/lean-divergences.md` carries the standing rule lean4lean's
`divergences.md` made the ecosystem's most copyable artifact:

    Unless specified here, any divergence between this kernel and Lean 4 is a bug.

That rule is worth nothing unless something enforces it. This script does, and
the enforcement runs in the direction that matters: it reads the AUTHORITIES,
collects every divergence they currently report, and fails if the ledger does
not name it. It never carries a list of divergences of its own -- a checker
whose subject is a literal inside itself measures the maintainer's memory, not
the tree.

Three authorities, three key namespaces:

  `conformance:<case>`   every full-mode row in
                         `artifacts/kernel-conformance/summary.json` whose
                         verdict is not the corpus's expected outcome
                         (ADR-1663, the public Lean Kernel Arena corpus).
  `differential:<name>`  every entry of `EXPLAINED_INCOMPLETENESS` in
                         `crates/axeyum-lean-kernel/tests/kernel_differential.rs`
                         (ADR-0780).
  `census:<reason>`      every non-representable class of the replay census,
                         read from `Representability::reason`'s match arms in
                         `crates/axeyum-lean-kernel/tests/support/creal_representability.rs`
                         (ADR-0760).

Guards, each deletable to see exactly one failure:

  L1  the ledger exists and parses to at least one entry
  L2  every authority key is listed by some ledger entry
  L3  no OPEN ledger entry claims a key no authority reports (a stale entry);
      entries marked closed are exempt, since a closed divergence is precisely
      one the authorities no longer report
  L4  the standing rule sentence is present verbatim -- without it the file is
      a list, not a ledger
  L5  every authority yielded a NONZERO number of keys. A missing or renamed
      authority would otherwise make L2 pass vacuously, which is the exact
      failure mode this repository has shipped before

Usage:
    scripts/check-lean-divergences.py
    scripts/check-lean-divergences.py --self-test
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "docs" / "plan" / "lean-divergences.md"
CONFORMANCE = ROOT / "artifacts" / "kernel-conformance" / "summary.json"
DIFFERENTIAL = ROOT / "crates" / "axeyum-lean-kernel" / "tests" / "kernel_differential.rs"
CENSUS = (
    ROOT
    / "crates"
    / "axeyum-lean-kernel"
    / "tests"
    / "support"
    / "creal_representability.rs"
)

STANDING_RULE = (
    "Unless specified here, any divergence between this kernel and Lean 4 is a bug."
)

ENTRY_RE = re.compile(r"^###\s+(?P<id>D\d+)\s+—\s+(?P<title>.+?)\s*$")
STATUS_RE = re.compile(r"^\*\*Status:\*\*\s*(?P<status>[a-z-]+)")
KEYS_RE = re.compile(r"^\*\*Keys:\*\*\s*(?P<keys>.+?)\s*$")
BACKTICKED = re.compile(r"`([^`]+)`")


# --------------------------------------------------------------------------
# Authorities
# --------------------------------------------------------------------------
def conformance_keys(path: Path) -> set[str]:
    if not path.exists():
        return set()
    summary = json.loads(path.read_text())
    return {f"conformance:{row['case']}" for row in summary.get("divergences", [])}


def differential_keys(path: Path) -> set[str]:
    """`EXPLAINED_INCOMPLETENESS`'s map keys, read from the Rust source.

    The constant is the differential suite's own registry of divergences it
    tolerates, so it is the authority; parsing it here rather than restating it
    is what makes a new registered incompleteness fail this gate.
    """
    if not path.exists():
        return set()
    text = path.read_text()
    # Anchor on the DECLARATION, not the first mention: the module doc comment
    # names the constant several lines earlier, and a scan from there reads
    # prose instead of the registry.
    start = text.find("const EXPLAINED_INCOMPLETENESS")
    if start < 0:
        return set()
    # The literal ends at the first `];`, whether rustfmt puts the closing paren
    # on its own line or beside it. A parse that reads too little yields zero
    # keys, which L5 turns into a failure rather than a vacuous pass.
    end = text.find("];", start)
    if end < 0:
        return set()
    body = text[start:end]
    return {f"differential:{name}" for name in re.findall(r'\(\s*"([^"]+)"\s*,', body)}


def census_keys(path: Path) -> set[str]:
    """The replay census's typed non-representable classes.

    Read from `Representability::reason`'s match arms, which is the definition
    of the census's wire vocabulary. `representable` is the agreeing class and
    is not a divergence.
    """
    if not path.exists():
        return set()
    text = path.read_text()
    start = text.find("fn reason(")
    if start < 0:
        return set()
    body = text[start : text.find("\n    }", start)]
    tokens = re.findall(r'=>\s*"([a-z0-9-]+)"', body)
    return {f"census:{token}" for token in tokens if token != "representable"}


# --------------------------------------------------------------------------
# Ledger
# --------------------------------------------------------------------------
def parse_ledger(text: str) -> list[dict]:
    entries: list[dict] = []
    current: dict | None = None
    for line in text.splitlines():
        match = ENTRY_RE.match(line)
        if match:
            current = {
                "id": match.group("id"),
                "title": match.group("title"),
                "status": None,
                "keys": [],
            }
            entries.append(current)
            continue
        if current is None:
            continue
        status = STATUS_RE.match(line)
        if status:
            current["status"] = status.group("status")
            continue
        keys = KEYS_RE.match(line)
        if keys:
            current["keys"].extend(BACKTICKED.findall(keys.group("keys")))
    return entries


# --------------------------------------------------------------------------
# Pure gate logic
# --------------------------------------------------------------------------
def evaluate(
    text: str | None,
    authorities: dict[str, set[str]],
) -> list[str]:
    failures: list[str] = []

    # L5 first: an authority that reports nothing makes L2 vacuous.
    for name, keys in sorted(authorities.items()):
        if not keys:
            failures.append(
                f"L5 authority-live: authority {name!r} yielded zero keys -- it is "
                "missing, renamed, or no longer parsed, and L2 would pass vacuously"
            )

    if text is None:
        failures.append(f"L1 ledger-exists: {LEDGER.relative_to(ROOT)} is absent")
        return failures

    entries = parse_ledger(text)
    if not entries:
        failures.append("L1 ledger-exists: the ledger parsed to zero entries")

    if STANDING_RULE not in text:
        failures.append(
            "L4 standing-rule: the ledger does not carry the standing rule "
            f"verbatim ({STANDING_RULE!r})"
        )

    listed = {key for entry in entries for key in entry["keys"]}
    reported = {key for keys in authorities.values() for key in keys}

    # L2 -- the direction that matters.
    for key in sorted(reported - listed):
        failures.append(
            f"L2 divergence-listed: `{key}` is reported by an authority and the "
            "ledger does not list it. Per the standing rule that makes it a bug: "
            "fix it, or add an entry saying why it stands."
        )

    # L3 -- stale open entries. Only keys in an authority's own namespace are
    # policed: a `manual:` key names a divergence no authority reports
    # automatically, and the entry itself must name the command that shows it.
    # Downgrading a real key to `manual:` does not hide it -- L2 requires the
    # authority's exact key, in its own namespace, to appear.
    policed = tuple(f"{name}:" for name in authorities)
    open_keys = {
        key
        for entry in entries
        if (entry["status"] or "open") != "closed"
        for key in entry["keys"]
        if key.startswith(policed)
    }
    for key in sorted(open_keys - reported):
        failures.append(
            f"L3 no-stale-entry: `{key}` is listed as an OPEN divergence but no "
            "authority reports it any more -- close the entry or fix the key"
        )
    return failures


# --------------------------------------------------------------------------
def self_test() -> int:
    good_authorities = {
        "conformance": {"conformance:tutorial/012_nonPropThm"},
        "differential": {"differential:quotient::quot_sound_absent"},
        "census": {"census:theorem-type-not-prop"},
    }
    good_text = "\n".join(
        [
            "# ledger",
            "",
            STANDING_RULE,
            "",
            "### D1 — a divergence",
            "",
            "**Status:** open",
            "**Keys:** `conformance:tutorial/012_nonPropThm`, "
            "`census:theorem-type-not-prop`",
            "",
            "### D2 — another",
            "",
            "**Status:** open",
            "**Keys:** `differential:quotient::quot_sound_absent`",
            "",
            "### D3 — a closed one",
            "",
            "**Status:** closed",
            "**Keys:** `conformance:gone`",
            "",
        ]
    )
    ok = True
    baseline = evaluate(good_text, good_authorities)
    if baseline:
        print(f"SELF-TEST FAIL baseline: expected no failures, got {baseline}")
        ok = False
    else:
        print("SELF-TEST ok baseline: a well-formed ledger passes")

    cases: list[tuple[str, str | None, dict[str, set[str]]]] = [
        ("L1", None, good_authorities),
        ("L1", "# empty ledger\n" + STANDING_RULE + "\n", good_authorities),
        # L2: an authority reports a key nothing lists.
        (
            "L2",
            good_text,
            {
                **good_authorities,
                "conformance": good_authorities["conformance"] | {"conformance:new"},
            },
        ),
        # L3: an OPEN entry names a key no authority reports.
        (
            "L3",
            good_text.replace("`census:theorem-type-not-prop`", "`census:vanished`"),
            {**good_authorities, "census": {"census:theorem-type-not-prop"}},
        ),
        # L4: the standing rule is gone.
        ("L4", good_text.replace(STANDING_RULE, "be nice to each other"), good_authorities),
        # L5: an authority went silent.
        ("L5", good_text, {**good_authorities, "differential": set()}),
    ]
    for guard, text, authorities in cases:
        failures = evaluate(text, authorities)
        named = [f for f in failures if f.startswith(guard)]
        if not named:
            print(f"SELF-TEST FAIL {guard}: did not fire (failures: {failures})")
            ok = False
        else:
            print(f"SELF-TEST ok {guard}: {named[0][:150]}")
    print("SELF-TEST", "PASS" if ok else "FAIL")
    return 0 if ok else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test()

    authorities = {
        "conformance": conformance_keys(CONFORMANCE),
        "differential": differential_keys(DIFFERENTIAL),
        "census": census_keys(CENSUS),
    }
    for name, keys in sorted(authorities.items()):
        print(f"LEAN-DIVERGENCES authority {name}: {len(keys)} key(s)")
    text = LEDGER.read_text() if LEDGER.exists() else None
    failures = evaluate(text, authorities)
    if text is not None:
        entries = parse_ledger(text)
        closed = sum(1 for e in entries if e["status"] == "closed")
        print(
            f"LEAN-DIVERGENCES ledger: {len(entries)} entr(ies), "
            f"{len(entries) - closed} open, {closed} closed"
        )
    if failures:
        for failure in failures:
            print(f"FAIL {failure}")
        return 1
    print("PASS scripts/check-lean-divergences.py")
    return 0


if __name__ == "__main__":
    sys.exit(main())
