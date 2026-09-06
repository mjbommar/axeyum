#!/usr/bin/env python3
"""Measure the PRODUCER channel: theorems whose proof term a producer built.

WHY THIS EXISTS
===============

The running production number this project quotes is "hand proofs retired":
a hand-written prelude proof deleted and replaced by producer output. It read
**67** on 2026-09-03 and still reads 67, unchanged, in five documents. Zero
retirement commits have touched the kernel crate since 2026-09-04, while
roughly two hundred new `proved` facts landed.

The rate did not slow. The work moved channel. Producers now EMIT theorems
that were never hand-written, so there is no hand proof to retire, and a
metric defined as "hand proofs deleted" is structurally blind to every
theorem that never had a hand proof in the first place. Quoting it as a rate
is the volume-for-progress mistake `docs/math-department/12-the-chair.md`
exists to catch.

The rule this script encodes, stated as generally as it is true:

    A production metric must be able to see EVERY channel that produces,
    or it will read flat while the system accelerates.

WHAT IT MEASURES, AND WHAT IT CANNOT
====================================

The measurement is in three layers, each with its own coverage line, because
they have different strengths and a reader must be able to tell them apart.

  L1 SITE CENSUS - fully reproducible, no name resolution.
     Every call to a producer entry point from outside the producer modules
     and outside test code, classified:

       EMIT   `<producer>::…::declare*`   the producer builds the proof term
                                          AND adds the declaration. A theorem
                                          that exists only because a producer
                                          emitted it. THIS is the channel the
                                          retirement metric cannot see.
       ASSIST `::prove*`, `::theorem`,    the producer builds a proof term
              `::run`, `::emit_*`         that a hand-authored declaration
                                          then adds. Producer-assisted, not
                                          producer-emitted.
       CONFIG `default_rules`, `rule_*`,  rule-set plumbing and rendering.
              `with_extra`, `render`, …   No proof term is built.

     Fail-closed: an entry point that is in no bucket is an ERROR, not an
     "other" bucket. That is what stops a new producer route from being
     silently absorbed into a headline number.

  L2 NAME RESOLUTION - EMIT sites name their theorem through a prelude
     names-struct FIELD (`p.add_right_comm`), not a string. Field -> leaf is
     EXTRACTED from the `field: kernel.name_str(ns, "leaf")` bindings in the
     kernel sources, never guessed from the field spelling: measured, 1,367
     of 2,725 bindings have a leaf that differs from its field, so guessing
     would be wrong about half the time.

  L3 LEDGER JOIN - a `proved` fact counts as producer-emitted when its
     `formal.kernel_theorem` ends in a leaf that an EMIT site names AND that
     leaf is unambiguous across the ledger's namespaces. A leaf naming
     theorems in two namespaces is reported as AMBIGUOUS and EXCLUDED from
     the numerator, so the headline number is a lower bound by construction.

WHAT THIS SCRIPT STRUCTURALLY CANNOT SEE
========================================

Printed at every run, because a number whose blind spots are not printed
beside it becomes a number quoted without them.

  * ASSIST is a count of SITES, not of theorems. A producer call inside a
    helper that is invoked N times is one site and N proof terms.
  * `ring::declare_ring_all` and `decide::declare_decidable_equality` emit
    SEVERAL theorems from ONE site. L1 counts the site.
  * The import-route producers in `crates/axeyum-lean-import/src/producers/`
    (bounded application, bounded induction, conclusion-directed application,
    the modeq family) are a different channel with a different trust base and
    are NOT counted here.
  * The CAS and the SMT routes produce settled facts and appear in neither
    layer. `proof_route` in the fact schema separates them; this script is
    about `kernel-lean` only.
  * The ledger records `provenance.established_by` as the PRELUDE BUILDER
    (`axeyum-lean-kernel build_nat_prelude`), never the producer. So L3 has
    to reach through the kernel SOURCES to answer a question the ledger
    should be able to answer on its own. See THE MISSING FIELD, below.

THE MISSING FIELD
=================

For this to be countable FROM THE LEDGER, without a source scan, exactly one
field has to be recorded, on exactly one path:

    fact.provenance.produced_by : string | null

  * `null` means hand-authored, asserted, not merely absent - the same
    absent/explicit-null distinction `formal.kernel_theorem` already draws.
  * The value names the producer entry point that built the proof term
    (`linarith::nat::declare`, `ring::int::prove_eq_at`, `tactic::run`, …).
  * It is written on the path that flips a fact to `proved` against a
    kernel-lean declaration, by the lane that names `formal.kernel_theorem` -
    the same moment, from the same knowledge, so it costs no new measurement.

Until that field exists, L3's number is derived from source text and carries
this script's resolution coverage as its error bar.

Usage
-----
    python3 scripts/measure-producer-channel.py            # report
    python3 scripts/measure-producer-channel.py --check    # gate

`--check` fails when an entry point is unclassified (a producer route this
script cannot see), when a layer collapses to zero (the report would pass
vacuously), or when the pinned floor in
`scripts/producer-channel-baseline.json` is broken.
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]


def _input(env: str, default: pathlib.Path) -> pathlib.Path:
    """Resolve one input, redirectable for the control suite ONLY.

    The default is the real in-tree path, so the gate does not depend on an
    ambient variable being set -- `scripts/tests/test-producer-channel-controls.sh`
    runs the unmutated script with `env -u` on all three and requires it green,
    which is what stops this from becoming "a gate on one shell".
    """
    value = os.environ.get(env)
    return pathlib.Path(value) if value else default


KERNEL_SRC = _input(
    "AXEYUM_PRODUCER_CHANNEL_KERNEL_SRC", ROOT / "crates/axeyum-lean-kernel/src"
)
FACTS = _input("AXEYUM_PRODUCER_CHANNEL_FACTS", ROOT / "artifacts/facts")
BASELINE = _input(
    "AXEYUM_PRODUCER_CHANNEL_BASELINE", ROOT / "scripts/producer-channel-baseline.json"
)

PRODUCERS = ("linarith", "ring", "simp", "psatz", "decide", "tactic")

# Classification of producer entry points. FAIL-CLOSED: a call to an entry
# point named in none of these three sets is an error. Keys are the final
# path segment of the call.
EMIT = {
    "declare",
    "declare_ring_all",
    "declare_decidable_equality",
    "declare_decide",
}
ASSIST = {
    "prove",
    "prove_s",
    "prove_eq",
    "prove_eq_at",
    "prove_eq_unverified",
    "theorem",
    "run",
    "emit_le_from_certificate",
    "certificate_for",
    "find_certificate",
    "find_refutation",
    "search_sos",
    "search_with_hypotheses",
    "glue_rel",
    "discriminate",
    "ceq",
    "ring_proof",
    "cone",
}
CONFIG = {
    "default_rules",
    "with_extra",
    "render",
    "measure",
    "measure_int",
    "measure_rat",
    "measure_list",
    "monomials_of_degree",
}
# `rule_*` is a rule constructor; matched by prefix rather than listed, since
# the rule set grows and a missing rule name is not a missing PRODUCER route.
CONFIG_PREFIXES = ("rule_",)

CALL = re.compile(
    r"(?:crate::)?\b(" + "|".join(PRODUCERS) + r")::((?:[a-z_0-9]+::)*)([a-z_0-9]+)\s*\("
)
# `field: <binder>(ns, "leaf")` — the authority for field -> leaf. The binder
# set is CLOSED: a names-struct initializer whose call is not one of these is
# reported as unresolved rather than guessed at, and a field with no binding at
# all lowers the printed L2 coverage instead of silently disappearing.
NAME_BINDERS = frozenset(
    {
        "kernel.name_str",
        "k.name_str",
        "self.name_str",
        "self.name_str_anon",
        "self.lookup_name_str",
        "child",
    }
)
BINDING = re.compile(
    r"^\s*([a-z_0-9]+)\s*:\s*([A-Za-z_0-9:.]+)\s*\(\s*[^()\"]*\"([^\"]+)\"\s*\)\s*,?\s*$",
    re.M,
)
# The names-struct field an EMIT site passes, e.g. `p.add_right_comm`.
EMIT_FIELD = re.compile(r"::declare[a-z_]*\(\s*[^,]+,\s*[^,]+,\s*[A-Za-z_0-9]+\.([a-z_0-9]+)")

SETTLED = "proved"


def strip_noise(text: str) -> str:
    """Blank out string literals and comments, preserving offsets.

    Without this the census reads producer paths out of `.expect("linarith::
    generic (setoid) must …")` panic messages and out of `//!` module docs, and
    reports them as call sites. Measured: two such false positives in
    `creal/linarith_bridge.rs`, both prose.
    """
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    break
                j += 1
            for k in range(i, min(j + 1, n)):
                if out[k] != "\n":
                    out[k] = " "
            i = j + 1
            continue
        if c == "/" and i + 1 < n and text[i + 1] == "/":
            j = text.find("\n", i)
            j = n if j == -1 else j
            for k in range(i, j):
                out[k] = " "
            i = j
            continue
        if c == "/" and i + 1 < n and text[i + 1] == "*":
            j = text.find("*/", i + 2)
            j = n if j == -1 else j + 2
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
            continue
        i += 1
    return "".join(out)


def is_test_path(rel: str) -> bool:
    parts = rel.replace(".rs", "").split("/")
    return any("test" in p for p in parts)


def in_producer_module(rel: str) -> bool:
    head = rel.split("/")[0]
    return head.removesuffix(".rs") in PRODUCERS


def classify(entry: str) -> str | None:
    if entry in EMIT:
        return "EMIT"
    if entry in ASSIST:
        return "ASSIST"
    if entry in CONFIG or entry.startswith(CONFIG_PREFIXES):
        return "CONFIG"
    return None


def scan_sites() -> tuple[dict, list, list]:
    """L1: producer call sites outside producer modules and test code."""
    buckets: dict[str, collections.Counter] = {
        "EMIT": collections.Counter(),
        "ASSIST": collections.Counter(),
        "CONFIG": collections.Counter(),
    }
    unclassified: list[str] = []
    emit_sites: list[dict] = []
    for path in sorted(KERNEL_SRC.rglob("*.rs")):
        rel = str(path.relative_to(KERNEL_SRC))
        if is_test_path(rel) or in_producer_module(rel):
            continue
        text = strip_noise(path.read_text())
        for m in CALL.finditer(text):
            producer, mid, entry = m.group(1), m.group(2).rstrip(":"), m.group(3)
            kind = classify(entry)
            call = f"{producer}::{mid or '-'}::{entry}"
            if kind is None:
                unclassified.append(f"{rel}: {call}")
                continue
            buckets[kind][call] += 1
            if kind == "EMIT":
                tail = text[m.start() : m.start() + 400]
                fm = EMIT_FIELD.search(tail)
                emit_sites.append(
                    {
                        "file": rel,
                        "call": call,
                        "field": fm.group(1) if fm else None,
                    }
                )
    return buckets, emit_sites, unclassified


def field_to_leaf() -> dict[str, set[str]]:
    """L2: EXTRACTED field -> leaf bindings. Never guessed from the field."""
    table: dict[str, set[str]] = collections.defaultdict(set)
    differing = 0
    total = 0
    for path in sorted(KERNEL_SRC.rglob("*.rs")):
        for m in BINDING.finditer(path.read_text()):
            if m.group(2) not in NAME_BINDERS:
                continue
            field, leaf = m.group(1), m.group(3)
            table[field].add(leaf)
            total += 1
            if field != leaf:
                differing += 1
    table["__stats__"] = {"total": total, "differing": differing}  # type: ignore[assignment]
    return table


def ledger_theorems() -> tuple[dict[str, list[str]], int, int]:
    """Proved facts keyed by the LEAF of formal.kernel_theorem."""
    by_leaf: dict[str, list[str]] = collections.defaultdict(list)
    proved = 0
    with_theorem = 0
    for path in sorted(FACTS.glob("F-*.json")):
        data = json.loads(path.read_text())
        if data.get("epistemic_status") != SETTLED:
            continue
        proved += 1
        name = data.get("formal", {}).get("kernel_theorem")
        if not name:
            continue
        with_theorem += 1
        by_leaf[name.split(".")[-1]].append(name)
    return by_leaf, proved, with_theorem


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true", help="gate: exit nonzero on a finding")
    args = ap.parse_args()

    buckets, emit_sites, unclassified = scan_sites()
    table = field_to_leaf()
    stats = table.pop("__stats__")
    by_leaf, proved, with_theorem = ledger_theorems()

    errors: list[str] = []

    print("# Producer channel measurement")
    print()
    print("METHOD: producer entry-point call sites in")
    try:
        where = KERNEL_SRC.relative_to(ROOT)
    except ValueError:  # redirected by the control suite
        where = KERNEL_SRC
    print(f"        {where}, excluding test paths and the")
    print("        producer modules themselves; classified EMIT / ASSIST / CONFIG,")
    print("        fail-closed on an unclassified entry point. Names are EXTRACTED")
    print("        from `field: kernel.name_str(ns, \"leaf\")`, never guessed.")
    print()

    # ---- L1 -------------------------------------------------------------
    n_emit = sum(buckets["EMIT"].values())
    n_assist = sum(buckets["ASSIST"].values())
    n_config = sum(buckets["CONFIG"].values())
    print("## L1 site census")
    print()
    print(f"  EMIT   {n_emit:5d}  producer builds the term AND declares it")
    print(f"  ASSIST {n_assist:5d}  producer builds a term a hand declaration adds")
    print(f"  CONFIG {n_config:5d}  rule-set plumbing, no proof term")
    print(f"  unclassified {len(unclassified):3d}  (any is an error)")
    print()
    for kind in ("EMIT", "ASSIST"):
        for call, count in sorted(buckets[kind].items(), key=lambda kv: (-kv[1], kv[0])):
            print(f"    {kind:6s} {count:4d}  {call}")
    print()
    for line in unclassified:
        print(f"    UNCLASSIFIED  {line}")
    if unclassified:  # GUARD:unclassified
        errors.append(  # GUARD:unclassified
            f"{len(unclassified)} producer entry point(s) in no bucket: a producer "  # GUARD:unclassified
            "route this metric cannot see"  # GUARD:unclassified
        )  # GUARD:unclassified

    # ---- L2 -------------------------------------------------------------
    resolved: dict[str, set[str]] = {}
    unresolved = 0
    for site in emit_sites:
        field = site["field"]
        if field is None or field not in table:
            unresolved += 1
            continue
        resolved.setdefault(field, set()).update(table[field])
    print("## L2 name resolution")
    print()
    print(f"  field -> leaf bindings extracted: {stats['total']}")
    print(f"  of those, leaf DIFFERS from field: {stats['differing']} "
          f"({100.0 * stats['differing'] / max(stats['total'], 1):.1f}%) "
          "- why the field spelling is never used as the name")
    print(f"  EMIT sites: {len(emit_sites)}; fields resolved: {len(resolved)}; "
          f"sites unresolved: {unresolved}")
    print(f"  COVERAGE: {100.0 * (len(emit_sites) - unresolved) / max(len(emit_sites), 1):.1f}% "
          "of EMIT sites carry a resolvable theorem name")
    print()

    # ---- L3 -------------------------------------------------------------
    hit: set[str] = set()
    ambiguous: set[str] = set()
    missing: set[str] = set()
    for field, leaves in resolved.items():
        for leaf in leaves:
            names = by_leaf.get(leaf, [])
            distinct = {n for n in names}
            if not distinct:
                missing.add(leaf)
            elif len({n.rsplit(".", 1)[0] for n in distinct}) > 1:
                ambiguous.add(leaf)
            else:
                hit.update(distinct)
    print("## L3 ledger join")
    print()
    print(f"  ledger: {proved} proved facts, {with_theorem} carrying "
          f"formal.kernel_theorem ({100.0 * with_theorem / max(proved, 1):.1f}%)")
    print(f"  proved facts whose kernel theorem a producer EMITTED: {len(hit)}")
    print(f"  leaves excluded as AMBIGUOUS across namespaces: {len(ambiguous)}")
    print(f"  EMIT leaves with no proved fact in the ledger: {len(missing)}")
    print()
    print("  This is a LOWER BOUND: ambiguous leaves are dropped, ASSIST sites are")
    print("  not counted at all, and a producer reached through a bridge module is")
    print("  attributed to the bridge, not to the producer.")
    print()

    # ---- blind spots, printed every run ---------------------------------
    print("## What this measurement cannot see")
    print()
    for line in (
        "ASSIST counts SITES, not theorems: a producer call in a helper invoked",
        "  N times is one site and N proof terms.",
        "declare_ring_all / declare_decidable_equality emit several theorems from",
        "  one site; L1 counts the site.",
        "The import-route producers in crates/axeyum-lean-import/src/producers/ are",
        "  a different channel with a different trust base and are not counted.",
        "The CAS and SMT routes appear in no layer; proof_route separates them.",
        "provenance.established_by names the PRELUDE BUILDER, never the producer,",
        "  so L3 must reach through source text. See THE MISSING FIELD in --help:",
        "  fact.provenance.produced_by would make this countable from the ledger.",
    ):
        print(f"  - {line}" if not line.startswith("  ") else f"  {line}")
    print()

    # ---- vacuity and floor ---------------------------------------------
    if n_emit == 0:  # GUARD:vacuous-emit
        errors.append("zero EMIT sites: this report would pass vacuously")  # GUARD:vacuous-emit
    if proved == 0:  # GUARD:vacuous-ledger
        errors.append("zero proved facts: the ledger join would pass vacuously")  # GUARD:vacuous-ledger
    if with_theorem == 0:  # GUARD:blind-join
        errors.append("no proved fact carries formal.kernel_theorem: L3 is blind")  # GUARD:blind-join

    floor = json.loads(BASELINE.read_text()) if BASELINE.exists() else None
    if floor is not None:
        print("## Floor")
        print()
        for key, observed in (
            ("emit_sites", n_emit),
            ("assist_sites", n_assist),
            ("producer_emitted_proved_facts", len(hit)),
        ):
            want = floor.get(key)
            if want is None:  # GUARD:floor-missing
                errors.append(f"baseline has no floor for `{key}`")  # GUARD:floor-missing
                continue  # GUARD:floor-missing
            ok = want is None or observed >= want
            shown = "  n/a" if want is None else f"{want:5d}"
            print(f"  {key:32s} floor {shown}  observed {observed:5d}  "
                  f"{'ok' if ok else 'BELOW FLOOR'}")
            if not ok:  # GUARD:floor-breach
                errors.append(  # GUARD:floor-breach
                    f"`{key}` fell from {want} to {observed}: the producer channel "  # GUARD:floor-breach
                    "shrank, or the census stopped seeing part of it"  # GUARD:floor-breach
                )  # GUARD:floor-breach
        print()

    if errors:
        print("## Findings")
        print()
        for e in errors:
            print(f"  ERROR: {e}")
        print()
        if args.check:
            return 1
        return 0
    print("No findings.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
