#!/usr/bin/env python3
"""Refill the flywheel's input queue with propositions we can actually state.

`check-dispatchable-frontier.py` went RED on 2026-08-29 with G4
`empty-dispatchable-set`: every open `ml430` mirror was held-out, a mutation
control, or blocked by a construction-level divergence. The population had run
out.

The previous lane established that supply is not the problem -- 8,932 unused
pinned propositions -- and that `screened-ok` against the divergence registry is
**necessary but not sufficient**: it says nothing about whether a proposition can
be EXPRESSED here, which is why hundreds of `Std.PRange`, `Finset` and
`LinearOrder` rows sail through it.

This script adds the missing positive screen and uses it to preregister a
refill.

THE POSITIVE SCREEN
-------------------
A pinned statement's `type_repr` is a structural `Lean.Expr` dump, so the exact
set of Lean constants it mentions is extractable mechanically. A proposition is
STATABLE HERE iff every one of those constants is admissible, where

    admissible = env      declaration names read from `kernel.environment()`
               | bridge   {constants of SETTLED ml430 mirrors} \\ env

The bridge is DERIVED, never asserted. An entry exists only because the ledger
already closed a mirror stated with that constant, which is what makes the
claim "this surface constant needs no kernel counterpart" a measurement rather
than an opinion. It covers exactly three things:

  * typeclass/notation elaboration -- `HAdd.hAdd`, `OfNat.ofNat`, `LE.le`;
  * Mathlib abbreviations that unfold into kernel vocabulary -- `Nat.Coprime`
    (`gcd a b = 1`), `Nat.ModEq`, `Nat.Prime`, `Even`, `Odd`, `ite`;
  * order abbreviations that unfold the same way -- `Monotone`, `StrictMono`,
    `StrictMonoOn`, `Set.Ici`, `Symmetric`, `Function.swap`. `Nat.fib_mono` is
    `proved` with the kernel type `a <= b -> fib a <= fib b`; `Monotone` never
    needed to exist here.

The false-positive control is the one that matters and it runs against real
data: EVERY settled `ml430` mirror must pass. Measured 156/156.

WHY THIS DOES NOT GROW `nursery-v1.json`
----------------------------------------
`create-autogenesis-mathlib-fact-catalog.py` refuses to emit a catalog whose
generated Lean surface module differs from `SURFACE_ATTESTATION_SHA256` -- "the
generated surface module changed without a new real-Lean attestation". That
guard is correct and this script does not defeat it: attesting new statements
needs `import Mathlib` against a built Mathlib, and the checkout at
`/data0/axeyum/lean-import-toolchain/mathlib4` (pinned commit, verified) has no
`.lake/build`.

So the refill lands as an ADDITIVE extension, `nursery-v2-extension.json`, with
its own -- WEAKER, and labelled -- validation grade:

  v1  real-Lean round trip: every statement re-elaborated as an axiom after
      `import Mathlib` and accepted (214 propositions).
  v2  byte-identical QUOTATION of the pinned statement-only extractor output at
      Mathlib c5ea0035 / v4.30.0, sha256 4285e551…. Nothing is transcribed, so
      there is no transcription to attest; but a pretty-printed type is not
      guaranteed to re-parse, and these rows must never be reported as if they
      carried v1's attestation.

`nursery-v1.json` is not touched: no entry moves partition, no count changes,
and `create-autogenesis-mathlib-nursery-split.py --check` stays green.

Usage:
    python3 scripts/gen-autogenesis-nursery-refill.py --snapshot-from <file>
    python3 scripts/gen-autogenesis-nursery-refill.py
    python3 scripts/gen-autogenesis-nursery-refill.py --check

`--snapshot-from` takes the stdout of

    cargo run --release -p axeyum-lean-kernel --example shape_search -- \\
      --include-constructed --limit 999999 --kind axiom --kind definition \\
      --kind theorem --kind inductive --kind constructor --kind recursor

Exit status: 0 ok, 1 a check failed, 2 an input could not be read.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys
from collections import Counter
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"
AUTOGEN = ROOT / "artifacts/autogenesis"
CATALOG = AUTOGEN / "mathlib-nat-int-fact-catalog-v1.json"
REGISTRY = AUTOGEN / "mirror-divergence-registry.json"
ENV_SNAPSHOT = AUTOGEN / "kernel-environment-snapshot-v1.json"
VOCABULARY = AUTOGEN / "mathlib-statable-vocabulary-v1.json"
EXTENSION = AUTOGEN / "nursery-v2-extension.json"

INVENTORY = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson"
)
INVENTORY_SHA256 = "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc"
INVENTORY_RECORDS = 9729
SOURCE_COMMIT = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
SOURCE_TAG = "v4.30.0"

SETTLED = {"proved", "refuted", "computed"}
CONST_RE = re.compile(r"Lean\.Expr\.const\s+`+([^\s\)\[]+)")

# Compiler-generated and hygienic names are not propositions anybody would
# dispatch a lane at. `_def`/`_eq_def` unfold notation and are defeq by
# construction; `Int.Linear.*` is `omega`'s internal certificate vocabulary.
#
# `\._` is the load-bearing one and it was NOT in the first draft: the generated
# names carry a LEADING underscore on the internal component
# (`Nat.decidable_dvd._proof_1`, `Int.ModEq.refl._simp_1`), so a `\.proof_\d+`
# pattern misses every one of them. `Nat.decidable_dvd._proof_1` reached the
# selection and was caught by reading the emitted rows, not by the pattern.
# Lean never gives a user-written declaration a name component starting with
# `_`, so the component-level rule is both correct and complete.
HYGIENE = re.compile(
    r"_@|_hyg|✝|\._|\.eq_def$|_def$|\.eq_\d+$|\.match_\d+"
    r"|\.congr_|\.sizeOf_|\.inj$|\.injEq$|\.noConfusion|^Int\.Linear\.|^Nat\.Linear\."
)

# The two surviving held-out families are `natural-logarithm` (21 open) and
# `natural-square-root` (16). The split key is `<family>:<statement-shape>`
# BECAUSE a route for one member is evidence about its siblings -- so a refill
# row over the same constructions would spend blind-evaluation value without
# anyone touching the partition. Excluded by construction, not by care.
HELD_OUT_CONSTRUCTIONS = {"Nat.log", "Nat.clog", "Nat.log2", "Nat.sqrt"}

# ---------------------------------------------------------------------------
# The preregistered split for the refill.
#
# `split_freeze: before-target-outcomes` is the hard part of a refill and it is
# a discipline question, not a tooling one. The rule below is stated here, in
# code, so that it is checkable rather than claimed:
#
#   New families are ordered by the LEXICOGRAPHIC path of their primary Mathlib
#   defining module -- a property of the external source, decided by Mathlib's
#   own directory layout and not by anything we know about our own capability.
#   Walking that order, partitions are assigned by the repeating cycle
#   held-out, development, train.
#
#   The cycle STARTS at held-out because the measured deficiency is held-out
#   breadth: of twelve v1 families exactly two are still open and blind, so the
#   surviving evaluation population tests two capabilities.
#
# `PARTITION_CYCLE` and `FAMILY_MODULES` are the whole input; `assign_partitions`
# derives the assignment, and `--check` re-derives it. Editing the ASSIGNMENT by
# hand is therefore not possible -- only editing the rule, which is legible.
PARTITION_CYCLE = ("held-out", "development", "train")

FAMILY_MODULES: dict[str, tuple[str, ...]] = {
    "integer-division": ("Init.Data.Int.DivMod.Lemmas", "Init.Data.Int.DivMod.Bootstrap"),
    "integer-order": ("Init.Data.Int.Order",),
    "integer-parity": ("Mathlib.Algebra.Group.Int.Even", "Mathlib.Algebra.Ring.Int.Parity"),
    "natural-division": ("Init.Data.Nat.Div.Basic", "Init.Data.Nat.Div.Lemmas"),
    "natural-divisibility": ("Init.Data.Nat.Dvd",),
    "natural-lcm": ("Init.Data.Nat.Lcm",),
    "natural-parity": ("Mathlib.Algebra.Group.Nat.Even", "Mathlib.Algebra.Ring.Parity"),
    "natural-totient": ("Mathlib.Data.Nat.Totient",),
}

FAMILY_ROUTES: dict[str, tuple[str, ...]] = {
    "integer-division": ("kernel-library-application", "modular-arithmetic-reconstruction"),
    "integer-order": ("kernel-induction", "kernel-library-application"),
    "integer-parity": ("kernel-library-application", "modular-arithmetic-reconstruction"),
    "natural-division": ("kernel-induction", "kernel-library-application"),
    "natural-divisibility": ("divisibility-library-application", "kernel-induction"),
    "natural-lcm": ("divisibility-library-application", "kernel-induction"),
    "natural-parity": ("kernel-induction", "modular-arithmetic-reconstruction"),
    "natural-totient": ("divisibility-library-application", "kernel-induction"),
}

PER_FAMILY = 10
V1_EVALUATION_ENTRIES = 214

# ADR-0615. The `100..300` range this used to enforce is `nursery-v1.json`'s OWN
# `policy.evaluation_fact_count`, and `check-autogenesis-nursery.py` checks it
# against v1's 214 entries alone -- `NURSERY` there is `nursery-v1.json` and
# nothing else. R3 used to apply that per-manifest bound to the SUM of two
# manifests (`V1_EVALUATION_ENTRIES + len(entries) > 300`), which is a stricter
# reading than any rule states and which made the second draw arithmetically
# impossible at 294 with a 40-row minimum.
#
# So the envelope is applied per COHORT, as it is written. v1 keeps its own
# range, asserted below rather than assumed. The quoted cohort gets a ceiling
# equal to the ATTESTED one, so an unattested population can never outweigh the
# population that carries the real-Lean round trip -- the same "scaffolding,
# never headline" rule ADR-0601 states for imports. When this binds, the answer
# is to re-attest (`scripts/provision-lean-import-toolchain.sh`, ~5 min on this
# host), not to raise it again.
V1_POLICY_RANGE = (100, 300)
EXTENSION_CEILING = V1_EVALUATION_ENTRIES


class RefillError(RuntimeError):
    """The refill cannot be reproduced or would breach a preregistered rule."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def slug(value: str) -> str:
    rendered = re.sub(r"[^a-z0-9]+", "-", value.lower()).strip("-")
    return rendered or "statement"


def statement_shape(statement: str) -> str:
    """The v1 catalog's classifier, verbatim -- the split key depends on it."""
    if "∃" in statement:
        return "existential-witness"
    if statement.startswith("¬"):
        return "negated-proposition"
    if any(marker in statement for marker in (
            "Monotone", "StrictMono", "Antitone", "Symmetric", "Function.swap")):
        return "higher-order-property"
    if re.search(r"\{?f\s*:\s*Bool\s*→", statement):
        return "higher-order-property"
    if "↔" in statement:
        return "biconditional"
    if "→" in statement:
        return "conditional-proposition"
    if "=" in statement:
        return "unconditional-equality"
    return "unconditional-relation"


def frozen_partitions() -> dict[str, str]:
    """The partitions an EARLIER draw already preregistered.

    ADR-0615. Without this the generator is not incremental at all: it derives
    every family's partition from one cycle over the whole of `FAMILY_MODULES`,
    so adding four new families to make a second draw shifts the cycle index of
    every family sorting after them. Measured on the eight draw-1 families,
    adding four moves SEVEN of them -- including `natural-division` (train, 8 of
    its 10 mirrors proved) into `held-out`, which manufactures a blind
    population out of rows whose answers are already published. R6 cannot see
    it: R6 compares the emitted manifest against `assign_partitions()`, and
    after the change both agree on the new, wrong assignment.

    The manifest is trusted only against its own digest, so a hand-edited
    `family_partitions` cannot become the frozen truth by being on disk.
    """
    if not EXTENSION.is_file():
        return {}
    manifest = load_json(EXTENSION)
    recorded = manifest.get("extension_sha256")
    body = {k: v for k, v in manifest.items() if k != "extension_sha256"}
    if digest(body) != recorded:
        raise RefillError(
            f"{EXTENSION.name} does not match its own extension_sha256, so its "
            f"recorded partitions cannot be trusted as the freeze")
    partitions = manifest.get("family_partitions")
    if not isinstance(partitions, dict) or not partitions:
        raise RefillError(
            f"{EXTENSION.name} carries no family_partitions to freeze")
    for entry in manifest.get("entries", []):
        if partitions.get(entry["family"]) != entry["partition"]:
            raise RefillError(
                f"{EXTENSION.name} entry {entry['fact_id']} carries partition "
                f"{entry['partition']!r}, disagreeing with its own "
                f"family_partitions")
    return dict(partitions)


def assign_partitions() -> dict[str, str]:
    """Frozen families keep their partition; the cycle runs over the NEW ones.

    The cycle restarts at `held-out` for each draw's new family set, which is
    what makes R5's "at least two new held-out families" reachable at four
    families. Continuing one global cycle across draws would not.
    """
    frozen = frozen_partitions()
    assignment = {f: p for f, p in frozen.items() if f in FAMILY_MODULES}
    fresh = sorted((f for f in FAMILY_MODULES if f not in assignment),
                   key=lambda f: FAMILY_MODULES[f][0])
    for index, family in enumerate(fresh):
        assignment[family] = PARTITION_CYCLE[index % len(PARTITION_CYCLE)]
    return assignment


# ---------------------------------------------------------------------------


def load_json(path: pathlib.Path) -> Any:
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        print(f"ERROR: {path}: {exc}", file=sys.stderr)
        raise SystemExit(2) from exc


def read_inventory() -> dict[str, dict[str, Any]]:
    if not INVENTORY.is_file():
        print(f"ERROR: the pinned statement inventory is not readable at "
              f"{INVENTORY}. This generator needs it; the CHECKER "
              f"(check-dispatchable-frontier.py --statable) does not.",
              file=sys.stderr)
        raise SystemExit(2)
    raw = INVENTORY.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != INVENTORY_SHA256:
        print(f"ERROR: {INVENTORY} is sha256 {actual}, expected "
              f"{INVENTORY_SHA256}. Note that the sibling `-v1.ndjson` also "
              f"carries {INVENTORY_RECORDS} records and is NOT the pinned "
              f"artifact.", file=sys.stderr)
        raise SystemExit(2)
    rows = {}
    for line in raw.decode().splitlines():
        record = json.loads(line)
        rows[record["name"]] = record
    if len(rows) != INVENTORY_RECORDS:
        print(f"ERROR: {len(rows)} distinct names, expected "
              f"{INVENTORY_RECORDS}", file=sys.stderr)
        raise SystemExit(2)
    return rows


def parse_env_dump(text: str) -> dict[str, Any]:
    """Turn `shape_search` stdout into the committed environment snapshot."""
    names, coverage, control = [], None, None
    for line in text.splitlines():
        if line.startswith("MATCH "):
            names.append(line.split()[1])
        elif line.startswith("coverage: "):
            coverage = line[len("coverage: "):]
        elif line.startswith("control: "):
            control = line[len("control: "):]
    if not names or coverage is None or control is None:
        raise RefillError(
            "the dump has no MATCH/coverage/control lines -- this is "
            "`shape_search` stdout, not a name list")
    unique = sorted(set(names))
    if len(unique) != len(names):
        raise RefillError("the dump repeats a declaration name")
    snapshot = {
        "schema_version": 1,
        "kind": "axeyum-kernel-environment-snapshot",
        "read_from": "Kernel::environment() via examples/shape_search",
        "command": (
            "cargo run --release -p axeyum-lean-kernel --example shape_search "
            "-- --include-constructed --limit 999999 --kind axiom --kind "
            "definition --kind theorem --kind inductive --kind constructor "
            "--kind recursor"),
        "coverage": coverage,
        "control": control,
        "declaration_count": len(unique),
        "notes": (
            "Declaration NAMES only, every populated kind. This is the "
            "authority for 'can this be stated here'; a theorem inventory is "
            "not -- it lists no Definitions, so `Nat.add` returns zero rows "
            "from it and certainly exists. The snapshot is a point-in-time "
            "read: it can only go stale in the fail-closed direction "
            "(a declaration that landed after it reads as absent)."),
        "declarations": unique,
    }
    return snapshot


def build_vocabulary(env: set[str], inventory: dict[str, dict[str, Any]],
                     catalog: dict[str, Any],
                     facts: dict[str, dict[str, Any]]) -> dict[str, Any]:
    external = [row for row in catalog["facts"] if row["kind"] == "external-source"]
    rows = []
    open_count = 0
    for row in sorted(external, key=lambda r: r["source_name"]):
        name = row["source_name"]
        record = inventory.get(name)
        if record is None:
            raise RefillError(f"catalogued {name} is absent from the pinned inventory")
        if facts[row["fact_id"]]["epistemic_status"] not in SETTLED:
            open_count += 1
            continue
        rows.append({
            "source_name": name,
            "constants": sorted(set(CONST_RE.findall(record["type_repr"]))),
        })
    bridge: set[str] = set()
    for row in rows:
        bridge |= set(row["constants"]) - env
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-statable-vocabulary",
        "derivation": (
            "bridge = {Lean constants in the pinned type_repr of every SETTLED "
            "ml430 mirror} \\ kernel-environment-snapshot-v1.declarations. "
            "Derived, never asserted: an entry exists only because a mirror "
            "stated with that constant has already been closed here."),
        "keyed_by": (
            "Mathlib source_name, NOT fact_id. Naming a fact id here would put "
            "held-out ids in a non-population artifact -- "
            "check-autogenesis-holdout-isolation.py caught exactly that on the "
            "first draft of this file, 35 references. The checker resolves "
            "source_name to a fact through the catalog, which IS a population "
            "file and may name them."),
        "source": {"mathlib_commit": SOURCE_COMMIT, "mathlib_tag": SOURCE_TAG,
                   "statement_inventory_sha256": INVENTORY_SHA256},
        "environment_snapshot": "artifacts/autogenesis/kernel-environment-snapshot-v1.json",
        "coverage": {
            "catalogued_propositions": len(rows) + open_count,
            "settled_propositions": len(rows),
            "open_propositions": open_count,
            "distinct_constants": len({c for r in rows for c in r["constants"]}),
            "bridge_constants": len(bridge),
        },
        "bridge": sorted(bridge),
        "settled": rows,
    }


def admissible(env: set[str], vocabulary: dict[str, Any]) -> set[str]:
    return env | set(vocabulary["bridge"])


def blockers_for(statement: str, registry: list[dict[str, Any]]) -> list[str]:
    return sorted(e["mathlib_constant"] for e in registry
                  if any(form in statement for form in e["surface_forms"]))


def select(inventory: dict[str, dict[str, Any]], env: set[str],
           vocabulary: dict[str, Any], registry: list[dict[str, Any]],
           catalogued: set[str]) -> tuple[list[dict[str, Any]], Counter]:
    adm = admissible(env, vocabulary)
    module_family = {m: f for f, ms in FAMILY_MODULES.items() for m in ms}
    reasons: Counter = Counter()
    per_family: dict[str, list[dict[str, Any]]] = {f: [] for f in FAMILY_MODULES}
    for name in sorted(inventory):
        record = inventory[name]
        family = module_family.get(record["module"])
        if family is None:
            continue
        if name in catalogued:
            reasons["already-catalogued"] += 1
            continue
        if HYGIENE.search(name):
            reasons["hygienic-or-generated"] += 1
            continue
        constants = set(CONST_RE.findall(record["type_repr"]))
        missing = sorted(constants - adm)
        if missing:
            reasons["not-statable-here"] += 1
            continue
        if constants & HELD_OUT_CONSTRUCTIONS:
            reasons["held-out-construction"] += 1
            continue
        blocked = blockers_for(record["type"], registry)
        if blocked:
            reasons["divergence-registry"] += 1
            continue
        per_family[family].append({
            "source_name": name,
            "module": record["module"],
            "statement": record["type"],
            "constants": sorted(constants),
        })
    partitions = assign_partitions()
    entries: list[dict[str, Any]] = []
    for family in sorted(per_family):
        pool = per_family[family]
        if len(pool) < PER_FAMILY:
            raise RefillError(
                f"family {family!r} yields {len(pool)} screened candidates, "
                f"fewer than the {PER_FAMILY} the refill takes")
        for cand in pool[:PER_FAMILY]:
            name = cand["source_name"]
            candidate_id = hashlib.sha256(
                (name + "\0" + cand["statement"]).encode()).hexdigest()
            shape = statement_shape(cand["statement"])
            entries.append({
                "answer_access": "withheld-during-episode",
                "candidate_id": candidate_id,
                "constants": cand["constants"],
                "fact_id": f"F:ml430-{slug(name)}-{candidate_id[:8]}",
                "family": family,
                "fragment": "Int" if name.startswith("Int.") else "Nat",
                "module": cand["module"],
                "mutation_of": None,
                "partition": partitions[family],
                "proof_shape": f"{family}:{shape}",
                "provenance_class": "external-transcribed",
                "route_hypotheses": list(FAMILY_ROUTES[family]),
                "source_group": cand["module"],
                "source_name": name,
                "source_statement_sha256": hashlib.sha256(
                    cand["statement"].encode()).hexdigest(),
                "statement": cand["statement"],
                "statement_shape": shape,
            })
        reasons[f"selected:{family}"] = PER_FAMILY
    return entries, reasons


def guard(entries: list[dict[str, Any]], v1_nursery: dict[str, Any],
          env: set[str]) -> None:
    """Every rule the refill claims to respect, asserted rather than described."""
    partitions = assign_partitions()
    frozen = frozen_partitions()
    # R4 and R5 ask what THIS draw adds. Once a second draw exists, every
    # earlier family is still in `entries` (the manifest is regenerated whole),
    # so counting over all of them would make both rules pass on draw-1's rows
    # while the new draw contributed nothing.
    new_entries = [e for e in entries if e["family"] not in frozen]

    # R1 -- the leakage rules the v1 policy states, applied to the new rows.
    for key in ("family", "proof_shape", "source_group"):
        by_value: dict[str, set[str]] = {}
        for entry in entries:
            by_value.setdefault(entry[key], set()).add(entry["partition"])
        crossing = {v: sorted(p) for v, p in by_value.items() if len(p) > 1}
        if crossing:
            raise RefillError(f"R1 {key} crosses evaluation partitions: {crossing}")

    # R2 -- no new family may reuse a v1 family name. A shared name would put
    # two independently-partitioned populations under one split key.
    v1_families = {e["family"] for e in v1_nursery["entries"]}
    clash = sorted(set(FAMILY_MODULES) & v1_families)
    if clash:
        raise RefillError(f"R2 new families collide with v1 families: {clash}")

    # R3 -- the ceiling, applied PER COHORT (ADR-0615). v1's own
    # `policy.evaluation_fact_count` governs v1, and is asserted here rather
    # than assumed; the quoted cohort may not outgrow the attested one.
    v1_evaluation = [e for e in v1_nursery["entries"]
                     if e["partition"] in ("train", "development", "held-out")]
    if len(v1_evaluation) != V1_EVALUATION_ENTRIES:
        raise RefillError(
            f"R3 nursery-v1 holds {len(v1_evaluation)} evaluation entries, not "
            f"the frozen {V1_EVALUATION_ENTRIES}; the attested cohort moved")
    low, high = V1_POLICY_RANGE
    if not low <= len(v1_evaluation) <= high:
        raise RefillError(
            f"R3 nursery-v1's {len(v1_evaluation)} evaluation entries fall "
            f"outside its own {low}..{high} policy range")
    if len(entries) > EXTENSION_CEILING:
        raise RefillError(
            f"R3 the quoted cohort would be {len(entries)} rows, over the "
            f"{EXTENSION_CEILING}-row ceiling (the size of the ATTESTED "
            f"cohort). Re-attest rather than raise it: "
            f"scripts/provision-lean-import-toolchain.sh")

    # R4 and R5 judge a DRAW. An invocation that adds no family is a
    # reproduction -- `--check`, or an idempotent re-run -- and there is no
    # refill for them to be about. They are not skippable for a real draw: any
    # family added to FAMILY_MODULES lands in `new_entries` and both apply.
    if new_entries:
        # R4 -- the refill must actually refill: at least one row THIS DRAW
        # ADDS must be dispatchable, or the exercise moved a counter without
        # adding work.
        dispatchable = [e for e in new_entries if e["partition"] != "held-out"]
        if not dispatchable:
            raise RefillError("R4 every refill row is held-out; nothing is dispatchable")

        # R5 -- and it must restore blind breadth, which is the other half of
        # the measured deficiency. The surviving v1 held-out set is two
        # families.
        new_held_out = {e["family"] for e in new_entries
                        if e["partition"] == "held-out"}
        if len(new_held_out) < 2:
            raise RefillError(
                f"R5 the refill adds {len(new_held_out)} held-out families; the "
                f"blind population is already down to two capabilities")

    # R6 -- the assignment must be the one the rule produces. Belt and braces:
    # `select` reads the same function, so this fires only if someone
    # hand-edited a partition into the emitted manifest.
    for entry in entries:
        if entry["partition"] != partitions[entry["family"]]:
            raise RefillError(
                f"R6 {entry['fact_id']} carries partition "
                f"{entry['partition']!r}, but the preregistered rule assigns "
                f"{partitions[entry['family']]!r} to {entry['family']!r}")

    # R7 -- routes must be sorted and unique, as the v1 generator demands.
    for family, routes in FAMILY_ROUTES.items():
        if list(routes) != sorted(set(routes)):
            raise RefillError(f"R7 route hypotheses for {family} are not sorted/unique")

    # R8 -- a family an earlier draw preregistered keeps its partition, and
    # keeps existing. R6 above cannot see either failure: it re-derives the
    # assignment from the same function the emitter used, so a cycle that
    # shifted agrees with itself.
    for entry in entries:
        was = frozen.get(entry["family"])
        if was is not None and entry["partition"] != was:
            raise RefillError(
                f"R8 {entry['family']!r} was preregistered as {was!r} and this "
                f"draw assigns {entry['partition']!r}; a preregistered "
                f"partition may only move through the ADR-0542 amendment "
                f"ledger, never by regeneration")
    dropped = sorted(set(frozen) - set(FAMILY_MODULES))
    if dropped:
        raise RefillError(
            f"R8 preregistered families are absent from FAMILY_MODULES and "
            f"would be deleted from the manifest: {dropped}")

    # R9 -- a candidate whose Mathlib name ALREADY has a declaration here may
    # not be preregistered blind. This is the natural-binomial contamination
    # (ADR-0542, 2026-08-25: ordinary development in `choose.rs` had already
    # proved 5 of 20 held-out rows) detected BEFORE preregistration rather than
    # three days after. Scoped to what this draw adds -- an earlier draw's rows
    # are frozen, and repairing one is an amendment, not a regeneration.
    contaminated = sorted(
        (e["family"], e["source_name"]) for e in new_entries
        if e["partition"] == "held-out" and e["source_name"] in env)
    if contaminated:
        raise RefillError(
            f"R9 {len(contaminated)} held-out candidate(s) already have a "
            f"declaration of the same Mathlib name in the kernel environment, "
            f"so they are not blind: {contaminated[:5]}")


def build_extension(entries: list[dict[str, Any]],
                    reasons: Counter) -> dict[str, Any]:
    partitions = assign_partitions()
    counts = Counter(e["partition"] for e in entries)
    extension = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-nursery-extension",
        "state": "preregistered-before-target-outcomes",
        "extends": "artifacts/autogenesis/nursery-v1.json",
        "why": (
            "check-dispatchable-frontier.py G4 empty-dispatchable-set fired on "
            "2026-08-29: 58 open ml430 mirrors, 0 dispatchable. This extension "
            "adds population that can be worked. It is ADDITIVE -- no v1 entry "
            "moves partition, no v1 count changes, and "
            "create-autogenesis-mathlib-nursery-split.py --check stays green."),
        "source": {
            "mathlib_commit": SOURCE_COMMIT,
            "mathlib_tag": SOURCE_TAG,
            "lean_version": "4.30.0",
            "statement_inventory": str(INVENTORY),
            "statement_inventory_sha256": INVENTORY_SHA256,
        },
        "surface_validation": {
            "grade": "quotation",
            "method": (
                "formal.statement is a BYTE-IDENTICAL quotation of the pinned "
                "statement-only extractor's `type` field. Nothing is "
                "transcribed, so there is no transcription to attest."),
            "weaker_than_v1_because": (
                "nursery-v1's 214 statements were re-elaborated as axioms after "
                "`import Mathlib` and accepted "
                "(accepted-214-proof-free-axiom-types). These were not: a "
                "pretty-printed type is not guaranteed to re-parse. Reporting "
                "these rows as carrying v1's attestation would be false."),
            "blocked_on": (
                "create-autogenesis-mathlib-fact-catalog.py refuses a catalog "
                "whose generated surface module differs from "
                "SURFACE_ATTESTATION_SHA256, and re-attesting needs a built "
                "Mathlib. /data0/axeyum/lean-import-toolchain/mathlib4 is at "
                "the pinned commit with no .lake/build, so the attestation "
                "could not be produced in this lane."),
            "per_row_binding": "source_statement_sha256",
        },
        "screens": {
            "divergence_registry": "artifacts/autogenesis/mirror-divergence-registry.json",
            "statable_here": "artifacts/autogenesis/mathlib-statable-vocabulary-v1.json",
            "held_out_constructions": sorted(HELD_OUT_CONSTRUCTIONS),
            "note": (
                "Every candidate passed BOTH screens plus the held-out "
                "construction exclusion before entering this manifest. A "
                "generator that emits unclosable rows inflates the open count "
                "without adding work, which is how the v1 population came to "
                "be 72% closed with an empty dispatchable set."),
        },
        "partition_assignment_rule": (
            "New families are ordered by the lexicographic path of their "
            "primary Mathlib defining module -- a property of the external "
            "source, not of our capability -- and partitions are assigned by "
            "the repeating cycle "
            + ", ".join(PARTITION_CYCLE)
            + ". The cycle starts at held-out because the measured deficiency "
            "is held-out breadth: of twelve v1 families exactly two are still "
            "open and blind. No target outcome was consulted; the rule is "
            "re-derived by --check, so the assignment cannot be hand-edited. "
            "ADR-0615: a family an earlier draw preregistered is FROZEN and the "
            "cycle runs over the new families only. Without that freeze, adding "
            "four families shifted the cycle index of seven of the first "
            "eight -- moving natural-division, 8 of whose 10 mirrors are "
            "proved, into held-out."),
        "family_partitions": partitions,
        "family_modules": {f: list(m) for f, m in sorted(FAMILY_MODULES.items())},
        "route_hypotheses": {f: list(r) for f, r in sorted(FAMILY_ROUTES.items())},
        "coverage": {
            "entries": len(entries),
            "families": len(FAMILY_MODULES),
            "per_family": PER_FAMILY,
            "partition_counts": dict(sorted(counts.items())),
            "v1_evaluation_entries": V1_EVALUATION_ENTRIES,
            "combined_evaluation_entries": V1_EVALUATION_ENTRIES + len(entries),
            "attested_cohort_entries": V1_EVALUATION_ENTRIES,
            "quoted_cohort_ceiling": EXTENSION_CEILING,
            "ceiling_authority": (
                "ADR-0615. nursery-v1's policy.evaluation_fact_count 100..300 "
                "governs nursery-v1, which check-autogenesis-nursery.py checks "
                "against its 214 entries alone. This QUOTED cohort carries its "
                "own ceiling, equal to the ATTESTED cohort, so an unattested "
                "population can never outweigh an attested one. When it binds, "
                "re-attest (scripts/provision-lean-import-toolchain.sh) rather "
                "than raise it."),
            "screen_rejections": dict(sorted(
                (k, v) for k, v in reasons.items() if not k.startswith("selected:"))),
        },
        "limitations": [
            "Lean surface propositions are not Axeyum kernel-core terms.",
            "These statements carry the quotation grade, not v1's real-Lean "
            "round-trip attestation; the two must not be reported together as "
            "one attested population.",
            "depends_on is empty: no dependency-component analysis was run for "
            "these rows, so source_group is the Mathlib defining module rather "
            "than a declared weak component.",
            "Mathlib declarations remain external prior art and every Axeyum "
            "fact here remains open.",
        ],
        "entries": entries,
    }
    extension["extension_sha256"] = digest(extension)
    return extension


def fact_for(entry: dict[str, Any]) -> dict[str, Any]:
    name = entry["source_name"]
    return {
        "schema_version": 1,
        "id": entry["fact_id"],
        "title": f"Mathlib v4.30 source proposition {name}",
        "statement": (
            f"The proposition declared as `{name}` in the pinned Mathlib "
            f"v4.30 source."),
        "formal": {
            "language": "lean4-surface",
            "statement": entry["statement"],
            "fragment": entry["fragment"],
        },
        "epistemic_status": "open",
        "external_status": "proved",
        "depends_on": [],
        "evidence": [],
        "provenance": {
            "date": "2026-08-29",
            "established_by": "not established in this ledger",
            "source": (
                f"statement-only extraction of `{name}` from Mathlib "
                f"{SOURCE_TAG}; no proof value was exposed"),
            "prior_art": [
                {
                    "who": "the Mathlib contributors",
                    "what": f"the theorem declaration `{name}`",
                    "where": f"mathlib4 commit {SOURCE_COMMIT} ({SOURCE_TAG})",
                    "year": 2026,
                    "attribution": (
                        "the proposition was read from the pinned "
                        "statement-only inventory; the proof term and tactic "
                        "trace were not consulted"),
                }
            ],
        },
        "notes": (
            "Open in Axeyum. The external theorem declaration is prior art, "
            "not a locally constructed proof. formal.statement is a "
            "BYTE-IDENTICAL quotation of the pinned extractor's pretty-printed "
            "type -- the QUOTATION grade, weaker than the 214 nursery-v1 rows, "
            "which were re-elaborated as axioms after `import Mathlib` and "
            "accepted. Preregistered in "
            "artifacts/autogenesis/nursery-v2-extension.json, which carries "
            "the partition; that manifest, not this file, is the split "
            "authority. Screened against the mirror-divergence registry and "
            "the statable-here vocabulary before preregistration."),
    }


def fact_path(fact_id: str) -> pathlib.Path:
    return FACTS / (fact_id.replace("F:", "F-") + ".json")


def render_fact(fact: dict[str, Any]) -> str:
    return json.dumps(fact, indent=2, ensure_ascii=False) + "\n"


def render(value: Any) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n"


# What preregistration binds about a fact, and therefore all this generator may
# assert about one that already exists. Everything else -- `epistemic_status`,
# `evidence`, `depends_on` -- belongs to the ledger and to whichever lane closed
# the mirror; `validate-facts.py` is its checker, not this script.
PREREGISTERED_FIELDS = ("id", "title", "statement")


def shown(path: pathlib.Path) -> str:
    """Repository-relative when it can be, absolute when it cannot -- the
    controls point `FACTS` at a scratch directory outside the tree."""
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def preregistered_view(fact: dict[str, Any]) -> dict[str, Any]:
    view = {k: fact.get(k) for k in PREREGISTERED_FIELDS}
    formal = fact.get("formal") or {}
    view["formal.statement"] = formal.get("statement")
    view["formal.fragment"] = formal.get("fragment")
    view["formal.language"] = formal.get("language")
    return view


def reconcile_facts(entries: list[dict[str, Any]], check: bool) -> list[str]:
    """Emit a fact ONLY where none exists; never rewrite one that does.

    ADR-0615. This generator regenerates the whole manifest from
    `FAMILY_MODULES`, and it used to regenerate every fact file with it. By the
    time a second draw was attempted, lanes had closed 39 of draw 1's 50
    dispatchable mirrors, so `--check` reported `39 generated file(s) are
    stale` and its own advice -- "regenerate without --check" -- would have
    overwritten 39 `proved` facts with fresh `open` stubs, discarding the
    evidence rows and status flips of five lanes.

    A preregistered fact is immutable in the fields preregistration BINDS and
    mutable in everything else. So the reconciliation asserts the former and
    leaves the latter alone, in both modes.
    """
    problems: list[str] = []
    for entry in entries:
        path = fact_path(entry["fact_id"])
        fresh = fact_for(entry)
        if not path.exists():
            if check:
                problems.append(
                    f"{shown(path)} is missing; regenerate without --check")
            else:
                path.write_text(render_fact(fresh))
            continue
        existing = json.loads(path.read_text())
        want = preregistered_view(fresh)
        got = preregistered_view(existing)
        if want != got:
            drift = sorted(k for k in want if want[k] != got[k])
            problems.append(
                f"{shown(path)} has drifted from its preregistration "
                f"in {drift}; a preregistered statement may not be rewritten")
    return problems


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true",
                    help="re-derive everything and fail if the tree differs")
    ap.add_argument("--snapshot-from", type=pathlib.Path,
                    help="rewrite the environment snapshot from shape_search stdout")
    args = ap.parse_args()

    try:
        if args.snapshot_from is not None:
            snapshot = parse_env_dump(args.snapshot_from.read_text())
            ENV_SNAPSHOT.write_text(render(snapshot))
            print(f"KERNEL_ENVIRONMENT_SNAPSHOT|declarations="
                  f"{snapshot['declaration_count']}|{snapshot['coverage']}")
            return 0

        snapshot = load_json(ENV_SNAPSHOT)
        env = set(snapshot["declarations"])
        if len(env) != snapshot["declaration_count"]:
            raise RefillError("environment snapshot count disagrees with its list")
        inventory = read_inventory()
        catalog = load_json(CATALOG)
        registry = load_json(REGISTRY)["constructions"]
        facts = {}
        for path in sorted(FACTS.glob("*.json")):
            fact = json.loads(path.read_text())
            facts[fact["id"]] = fact

        vocabulary = build_vocabulary(env, inventory, catalog, facts)

        # The false-positive control, run against the real population on every
        # invocation rather than against a fixture: a screen that rejects a
        # mirror we already CLOSED is wrong about the vocabulary.
        adm = admissible(env, vocabulary)
        rejected = [r["source_name"] for r in vocabulary["settled"]
                    if set(r["constants"]) - adm]
        if rejected:
            raise RefillError(
                f"the statable-here screen rejects {len(rejected)} SETTLED "
                f"mirror(s), so its vocabulary is incomplete: {rejected[:5]}")

        catalogued = {row["source_name"] for row in catalog["facts"]
                      if row["kind"] == "external-source"}
        entries, reasons = select(inventory, env, vocabulary, registry, catalogued)
        v1_nursery = load_json(AUTOGEN / "nursery-v1.json")
        guard(entries, v1_nursery, env)
        extension = build_extension(entries, reasons)

        outputs = {VOCABULARY: render(vocabulary), EXTENSION: render(extension)}

        if args.check:
            stale = [p for p, text in outputs.items()
                     if not p.exists() or p.read_text() != text]
            if stale:
                raise RefillError(
                    f"{len(stale)} generated file(s) are stale, first "
                    f"{stale[0].relative_to(ROOT)}; regenerate without --check")
        else:
            for path, text in outputs.items():
                path.write_text(text)

        # Facts are reconciled, never rewritten -- see reconcile_facts.
        problems = reconcile_facts(entries, args.check)
        if problems:
            # Under --check this is a reproduction failure and must be fatal.
            # During a draw it is a LEDGER defect in rows this invocation is not
            # touching, and blocking every future draw on one lane's edit to one
            # settled fact would be the wrong trade -- so it is reported on
            # stderr, loudly and by name, and the draw proceeds. Nothing is
            # written to those files either way.
            if args.check:
                raise RefillError(
                    f"{len(problems)} fact file(s) disagree with the "
                    f"preregistration; first: {problems[0]}")
            for problem in problems:
                print(f"PREREGISTRATION_DRIFT|{problem}", file=sys.stderr)
            print(f"PREREGISTRATION_DRIFT|{len(problems)} fact(s) drifted; "
                  f"none were rewritten", file=sys.stderr)

        counts = extension["coverage"]["partition_counts"]
        print("AUTOGENESIS_NURSERY_REFILL_OK|"
              f"entries={len(entries)}|"
              f"settled_mirrors_admitted={len(vocabulary['settled'])}|"
              f"bridge={len(vocabulary['bridge'])}|"
              f"env={len(env)}|"
              + "|".join(f"{k}={v}" for k, v in sorted(counts.items()))
              + f"|combined={V1_EVALUATION_ENTRIES + len(entries)}")
    except RefillError as error:
        print(f"autogenesis-nursery-refill: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
