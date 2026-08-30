#!/usr/bin/env python3
"""Is there anything left for the flywheel to select?

`fact-frontier.py` prints the queue. It does not print a number that goes to
ZERO when the queue empties, and it exits 0 either way -- so a queue that has
run out reads exactly like a queue being worked down. Measured 2026-08-29: the
`ml430` mirror population was 214/155 proved, and of the 59 open rows 37 were
blind-evaluation held-out, 12 were mutation negative controls, and of the 12
that remained ELEVEN were blocked by a construction-level divergence no proof
effort resolves. One row was actually dispatchable. Every headline count in the
frontier output (research 3, blocked 17, backlog 47) read as substantial work.

This script computes the one number those counts do not contain -- the
DISPATCHABLE set -- and makes the exit status depend on it.

    open ml430 rows
      - held-out          (blind evaluation population, ADR-0542; off-limits)
      - mutation controls (deliberately perturbed, often false; never closable)
      - structurally blocked by `artifacts/autogenesis/mirror-divergence-registry.json`
      = DISPATCHABLE

It also runs two SCREENS over candidate propositions before they are
preregistered, because a generator that emits population nobody can close
inflates the open count without adding work -- which is exactly how the
population came to be 72% closed with an empty dispatchable set.

  `--screen`    the NEGATIVE screen: the divergence registry. Blocks a mirror
                over a construction whose axeyum counterpart diverges.
  `--statable`  the POSITIVE screen, added 2026-08-29. `screened-ok` is
                NECESSARY AND NOT SUFFICIENT: the registry says nothing about
                whether a proposition can be EXPRESSED here, which is why
                hundreds of `Std.PRange`, `Finset` and `LinearOrder` rows sail
                through it. A candidate is STATABLE HERE iff every Lean
                constant in its type is admissible, where

                    admissible = env      names read from kernel.environment()
                               | bridge   {constants of SETTLED ml430 mirrors}
                                          minus env

                The bridge is DERIVED, never asserted: an entry exists only
                because the ledger already closed a mirror stated with that
                constant. It covers typeclass/notation elaboration
                (`HAdd.hAdd`, `OfNat.ofNat`), Mathlib abbreviations that unfold
                into kernel vocabulary (`Nat.Coprime`, `Nat.ModEq`, `Even`), and
                order abbreviations that unfold the same way (`Monotone`,
                `Set.Ici`) -- `Nat.fib_mono` is `proved` with the kernel type
                `a <= b -> fib a <= fib b`, so `Monotone` never needed to exist
                here. Measured 2026-08-29: 2,773 of 8,932 unused pinned
                propositions pass, so the screen rejects 69% and is not vacuous;
                and all 156 settled mirrors pass, so it is not a false-positive
                machine. `--statable` ALSO applies the registry, so one
                invocation is the whole pre-preregistration gate.

The registry is not taken on trust. Three of its guards exist to stop it being
used to shrink the open count by fiat:

  G1  a registry entry that matches no `ml430` proposition at all is stale.
  G2  a `codomain` claim must be RE-DERIVED from the pinned statements
      themselves -- some pinned statement mentioning the construction must
      place it against a `true`/`false` literal. A `codomain` row nobody can
      witness from the pinned source is an assertion, not a measurement.
  G3  the registry may never block a mirror we have already PROVED. That is the
      false-positive control, and it runs against every closed row on every
      invocation rather than against a fixture.

The statable-here vocabulary is not taken on trust either:

  S1  the environment snapshot must be internally consistent, must contain
      declarations any real kernel environment has, and must NOT contain a name
      no kernel could declare. An empty snapshot and an everything snapshot
      both read as a working screen otherwise.
  S2  a bridge constant must be WITNESSED by a settled mirror that mentions it,
      and must be absent from the environment -- a bridge for something the
      kernel declares hides a rename instead of recording an elaboration.
  S3  the screen may never reject a mirror we have already CLOSED. The
      false-positive control, run against the real population.
  S4  the vocabulary's per-row `settled` flag must agree with the fact ledger.
      Without this, flipping one flag smuggles any constant into the bridge and
      S2 becomes satisfiable by assertion.
  S5  `--statable` rejects an unstatable candidate before preregistration.
  S6  `--statable` rejects a candidate whose statement carries an elided-proof
      or inaccessible-name glyph (`⋯` U+22EF, `✝` U+271D, `…` U+2026) or the
      literal token `sorry`. Added 2026-08-29 after
      `scripts/attest-nursery-surface.py` found `F:ml430-nat-le-induction-`
      `2f088ac3` preregistered with a `⋯` in its statement -- Lean's
      pretty-printer glyph for an elided proof term, which re-parsed is a hole
      nothing can fill. The per-row `source_statement_sha256` cannot catch
      this: it faithfully binds a LOSSY string. No existing screen looked at
      the statement text for anything but the constants it names, so this row
      sailed through `--statable` and `--screen` both. S6 is scoped to
      `--statable` only (not to `check-dispatchable-frontier.py`'s own
      re-derivation of `select()`'s candidate pools in the generator) so that
      adding it cannot retroactively reshuffle an already-frozen family's
      preregistered candidates -- see gen-autogenesis-nursery-refill.py's
      `frozen_partitions()` for why that would be unsafe.

Partitions are read from the v1 nursery AND from `nursery-v2-extension.json`
(the 2026-08-29 refill). A held-out row that only the extension knows about
would otherwise be counted as dispatchable, which is the precise mistake the
extension exists to avoid.

Usage:
    python3 scripts/check-dispatchable-frontier.py
    python3 scripts/check-dispatchable-frontier.py --screen candidates.json
    python3 scripts/check-dispatchable-frontier.py --statable candidates.json
    python3 scripts/check-dispatchable-frontier.py --json

Exit status:
    0  a dispatchable row exists and the registry is internally sound
    1  a guard fired (see the FAIL lines)
    2  an input could not be read
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
DEFAULT_FACTS = ROOT / "artifacts" / "facts"
DEFAULT_NURSERY = ROOT / "artifacts" / "autogenesis" / "nursery-v1.json"
DEFAULT_REGISTRY = ROOT / "artifacts" / "autogenesis" / "mirror-divergence-registry.json"
DEFAULT_EXTENSION = ROOT / "artifacts" / "autogenesis" / "nursery-v2-extension.json"
DEFAULT_ENV = ROOT / "artifacts" / "autogenesis" / "kernel-environment-snapshot-v1.json"
DEFAULT_VOCAB = ROOT / "artifacts" / "autogenesis" / "mathlib-statable-vocabulary-v1.json"
DEFAULT_CATALOG = (ROOT / "artifacts" / "autogenesis"
                   / "mathlib-nat-int-fact-catalog-v1.json")

# S1's vacuity probes. `Eq` is Lean's own equality and every prelude this kernel
# builds needs it; `Nat` is the carrier the whole ml430 population is stated
# over. A snapshot missing either is not a kernel environment. The absent probe
# is a name no declaration can carry (a space is not a valid Lean name
# component), so a snapshot that "contains everything" -- the other way a screen
# goes vacuous, and the one that ADMITS rather than rejects -- fails too.
ENV_PROBES_PRESENT = ("Eq", "Nat")
ENV_PROBE_ABSENT = "axeyum probe no declaration can carry"

# S6. Lean's pretty-printer prints an elided proof term as `⋯` and an
# inaccessible/hygienic name as `✝`; `…` is the same elision spelled with the
# single-character horizontal ellipsis some renderers use instead of `⋯`. A
# statement carrying any of these is not the proposition it looks like -- see
# docs/contributor-guide/lean-surface-attestation.md's "finding". `sorry` is
# matched as a whole word so a real identifier merely containing the letters
# (there is none in this inventory, and the word-boundary is the false-positive
# guard if one ever appears) is not flagged.
GLYPH_RE = re.compile(r"[⋯✝…]|\bsorry\b")

# The ONE row ADR-0615 already recorded as not a well-formed proposition
# (docs/contributor-guide/lean-surface-attestation.md, "The finding, 2026-08-29").
# ADR-0615 forbids rewriting a preregistered `formal.statement` and forbids
# deleting a held-out row, so this fact_id will carry its `⋯` forever. S6 must
# not fail the standing gate on a defect that is already known, already
# recorded, and structurally un-fixable -- but it must fail on any OTHER
# candidate, present or future, that carries the same glyph. This set is the
# whole exemption: adding a fact_id here is a decision, not a side effect of
# running the screen, and nothing else may grow it silently.
KNOWN_GLYPHED_FACT_IDS = frozenset({"F:ml430-nat-le-induction-2f088ac3"})

MIRROR_PREFIX = "F:ml430-"
SETTLED = {"proved", "refuted", "computed"}
CODOMAIN = "codomain"
CLASSES = {CODOMAIN, "definitional", "algorithmic", "recursion-principle"}

# G7's floor. Below this many dispatchable rows the queue is about to empty and
# the run FAILS.
#
# This was `NARROW = 3` and a WARNING at exit 0 until 2026-08-30, on the
# reasoning that "a failure at this point would fire on a healthy-but-narrow
# queue". That reasoning is wrong in the direction this repository cares about.
# A gate that fires only at ZERO has told you after the fact: the queue is
# already empty, every lane is already blocked, and the refill -- which is a
# hand-authored source edit to `gen-autogenesis-nursery-refill.py`'s
# `FAMILY_MODULES`, not a script anyone can just re-run -- has not started.
# Measured 2026-08-30: the warning had been printing at 3 while the queue was
# hand-refilled four separate times, and all three remaining rows needed the
# same missing keystone, so the effective depth was ONE. Nobody was watching a
# line that exits 0.
#
# Ten is chosen against the measured drain rate, not picked for roundness: draw
# 4 put 110 non-held-out rows into the population and 107 of them were settled
# within a day, so the flywheel consumes non-held-out population far faster than
# a human authors draws. Ten is roughly the notice a draw needs.
FLOOR = 10


def die(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(2)


def load_facts(facts_dir: pathlib.Path) -> dict[str, dict[str, Any]]:
    if not facts_dir.is_dir():
        die(f"no fact directory at {facts_dir}")
    out: dict[str, dict[str, Any]] = {}
    for path in sorted(facts_dir.glob("*.json")):
        try:
            fact = json.loads(path.read_text())
        except json.JSONDecodeError as exc:
            die(f"{path}: {exc}")
        ident = fact.get("id")
        if not isinstance(ident, str):
            die(f"{path}: fact has no string id")
        out[ident] = fact
    if not out:
        die(f"{facts_dir} contains no facts")
    return out


def load_partitions(*manifests: pathlib.Path) -> tuple[set[str], set[str]]:
    """(held-out fact ids, mutation fact ids) from the preregistered splits.

    Every manifest is REQUIRED. Skipping an unreadable one would silently
    reclassify its held-out rows as dispatchable -- a gate that hands a lane a
    blind-evaluation proposition, which is worse than no gate.
    """
    held, mutation = set(), set()
    for path in manifests:
        if not path.is_file():
            die(f"no nursery manifest at {path}")
        manifest = json.loads(path.read_text())
        entries = manifest.get("entries")
        if not isinstance(entries, list):
            die(f"{path}: no `entries` list")
        for entry in entries:
            ident = entry.get("fact_id")
            if not isinstance(ident, str):
                continue
            if entry.get("partition") == "held-out":
                held.add(ident)
            if entry.get("mutation_of"):
                mutation.add(ident)
    return held, mutation


def load_vocabulary(env_path: pathlib.Path,
                    vocab_path: pathlib.Path) -> tuple[dict[str, Any], dict[str, Any]]:
    for path in (env_path, vocab_path):
        if not path.is_file():
            die(f"no statable-here input at {path}")
    snapshot = json.loads(env_path.read_text())
    vocabulary = json.loads(vocab_path.read_text())
    for doc, key, label in ((snapshot, "declarations", env_path),
                            (vocabulary, "bridge", vocab_path),
                            (vocabulary, "settled", vocab_path)):
        if not isinstance(doc.get(key), list):
            die(f"{label}: `{key}` must be a list")
    return snapshot, vocabulary


def load_catalog(path: pathlib.Path) -> dict[str, str]:
    """source_name -> fact_id for the catalogued external-source rows.

    The vocabulary artifact is keyed by Mathlib source name and NEVER by fact
    id: naming an id there would put held-out ids in a non-population file, and
    `check-autogenesis-holdout-isolation.py` caught precisely that on the first
    draft (35 references). The catalog IS a population file and may name them,
    so the join happens here.
    """
    if not path.is_file():
        die(f"no fact catalog at {path}")
    doc = json.loads(path.read_text())
    rows = doc.get("facts")
    if not isinstance(rows, list):
        die(f"{path}: no `facts` list")
    return {r["source_name"]: r["fact_id"] for r in rows
            if isinstance(r, dict) and r.get("kind") == "external-source"}


def guard_vocabulary(snapshot: dict[str, Any], vocabulary: dict[str, Any],
                     facts: dict[str, dict[str, Any]],
                     catalog: dict[str, str]) -> list[str]:
    """S1-S4. Returns FAIL lines."""
    fails: list[str] = []
    declarations = snapshot["declarations"]
    env = set(declarations)

    # S1 -- the snapshot is the authority for the whole positive screen, and
    # both ways it can go vacuous look identical from the exit status.
    if len(env) != len(declarations):
        fails.append("S1 stale-environment-snapshot: the declaration list "
                     "repeats a name")
    claimed = snapshot.get("declaration_count")
    if claimed != len(env):
        fails.append(f"S1 stale-environment-snapshot: declaration_count "
                     f"{claimed!r} disagrees with {len(env)} distinct names")
    absent_probes = [p for p in ENV_PROBES_PRESENT if p not in env]
    if absent_probes:
        fails.append(
            f"S1 stale-environment-snapshot: {absent_probes} missing. No "
            f"kernel environment lacks these, so this snapshot is empty, "
            f"truncated, or not a kernel environment at all.")
    if ENV_PROBE_ABSENT in env:
        fails.append(
            "S1 stale-environment-snapshot: the snapshot contains a name no "
            "declaration can carry, so it does not distinguish present from "
            "absent and the screen would admit everything.")

    bridge = set(vocabulary["bridge"])
    rows = vocabulary["settled"]
    witnessed: set[str] = set()
    listed: set[str] = set()
    for row in rows:
        if not isinstance(row, dict) or not isinstance(row.get("constants"), list):
            fails.append("S4 vocabulary-status-drift: a settled row has no "
                         "`constants` list")
            continue
        # S4 -- membership of this list is what promotes a row's constants into
        # the bridge, so it must be re-derived from the ledger, not believed.
        name = row.get("source_name")
        ident = catalog.get(name) if isinstance(name, str) else None
        if ident is None:
            fails.append(f"S4 vocabulary-status-drift: {name!r} is not a "
                         f"catalogued external-source proposition")
            continue
        listed.add(name)
        fact = facts.get(ident)
        if fact is None or fact.get("epistemic_status") not in SETTLED:
            status = None if fact is None else fact.get("epistemic_status")
            fails.append(
                f"S4 vocabulary-status-drift: {name} is listed as settled but "
                f"the ledger says {status!r}. Listing a row here promotes its "
                f"constants into the bridge, so the list is re-derived, never "
                f"believed.")
            continue
        witnessed |= set(row["constants"])
    # ...and the other direction, so a row cannot be DROPPED to make a
    # false-positive control (S3) pass over a narrower population.
    actually_settled = {name for name, ident in catalog.items()
                        if facts.get(ident, {}).get("epistemic_status") in SETTLED}
    absent = sorted(actually_settled - listed)
    if absent:
        fails.append(
            f"S4 vocabulary-status-drift: {len(absent)} settled mirror(s) are "
            f"missing from the vocabulary ({', '.join(absent[:3])}), so the "
            f"false-positive control would run against a narrower population "
            f"than the ledger has.")

    # S2 -- a bridge entry nothing witnesses is an assertion; a bridge entry the
    # kernel already declares is a rename hiding as an elaboration.
    unwitnessed = sorted(bridge - witnessed)
    if unwitnessed:
        fails.append(
            f"S2 unwitnessed-bridge-constant: {len(unwitnessed)} bridge "
            f"constant(s) appear in no settled mirror: {unwitnessed[:5]}. The "
            f"bridge is derived from closures, never asserted.")
    shadowing = sorted(bridge & env)
    if shadowing:
        fails.append(
            f"S2 unwitnessed-bridge-constant: {shadowing[:5]} are IN the kernel "
            f"environment, so they need no bridge; a bridge entry here hides a "
            f"rename.")

    # S3 -- the false-positive control, against the real closed population.
    admissible = env | bridge
    rejected = [row["source_name"] for row in rows
                if isinstance(row, dict)
                and isinstance(row.get("constants"), list)
                and set(row["constants"]) - admissible]
    if rejected:
        fails.append(
            f"S3 screen-rejects-a-settled-mirror: the statable-here screen "
            f"rejects {len(rejected)} mirror(s) we have already closed "
            f"({', '.join(rejected[:3])}), so its vocabulary is incomplete.")
    return fails


def load_registry(path: pathlib.Path) -> list[dict[str, Any]]:
    if not path.is_file():
        die(f"no divergence registry at {path}")
    doc = json.loads(path.read_text())
    entries = doc.get("constructions")
    if not isinstance(entries, list) or not entries:
        die(f"{path}: `constructions` must be a non-empty list")
    for entry in entries:
        name = entry.get("mathlib_constant")
        if not isinstance(name, str) or not name:
            die(f"{path}: an entry has no `mathlib_constant`")
        forms = entry.get("surface_forms")
        if not isinstance(forms, list) or not forms or not all(
                isinstance(f, str) and f for f in forms):
            die(f"{path}: {name} has no `surface_forms`")
        if entry.get("class") not in CLASSES:
            die(f"{path}: {name} has class {entry.get('class')!r}, "
                f"expected one of {sorted(CLASSES)}")
    return entries


def statement_of(fact: dict[str, Any]) -> str:
    formal = fact.get("formal")
    if not isinstance(formal, dict):
        return ""
    text = formal.get("statement")
    return text if isinstance(text, str) else ""


def blockers_for(statement: str, registry: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [e for e in registry
            if any(form in statement for form in e["surface_forms"])]


def classify(facts: dict[str, dict[str, Any]], held: set[str],
             mutation: set[str], registry: list[dict[str, Any]]) -> dict[str, Any]:
    buckets: dict[str, list[Any]] = {
        "held-out": [], "mutation": [], "blocked": [], "dispatchable": []}
    for ident, fact in sorted(facts.items()):
        if not ident.startswith(MIRROR_PREFIX):
            continue
        if fact.get("epistemic_status") in SETTLED:
            continue
        # A `-mutation-` id is the ledger's own naming convention and is not
        # reached by `mutation_of` when the row predates the nursery entry;
        # both are consulted so a control cannot be counted as dispatchable.
        if ident in mutation or "-mutation-" in ident:
            buckets["mutation"].append(ident)
            continue
        if ident in held:
            buckets["held-out"].append(ident)
            continue
        hits = blockers_for(statement_of(fact), registry)
        if hits:
            buckets["blocked"].append(
                (ident, [(h["mathlib_constant"], h["class"]) for h in hits]))
        else:
            buckets["dispatchable"].append(ident)
    return buckets


def guard_registry(facts: dict[str, dict[str, Any]],
                   registry: list[dict[str, Any]]) -> list[str]:
    """G1, G2, G3 and the evidence-path guard. Returns FAIL lines."""
    fails: list[str] = []
    mirrors = {i: f for i, f in facts.items() if i.startswith(MIRROR_PREFIX)}
    for entry in registry:
        name = entry["mathlib_constant"]
        forms = entry["surface_forms"]
        matched = [i for i, f in mirrors.items()
                   if any(form in statement_of(f) for form in forms)]

        # G1 -- a blocker nothing is blocked by is stale, and a stale blocker is
        # how the open count gets shrunk without any proposition changing.
        if not matched:
            fails.append(
                f"G1 stale-registry-entry: {name} matches no ml430 proposition "
                f"(surface forms {forms}). Remove it or fix the forms.")

        # G3 -- the false-positive control. If the registry blocks something we
        # have already closed, the registry is wrong about the construction.
        proved = sorted(i for i in matched
                        if mirrors[i].get("epistemic_status") in SETTLED)
        if proved:
            fails.append(
                f"G3 blocks-a-settled-mirror: {name} would block {len(proved)} "
                f"already-settled mirror(s): {', '.join(proved[:5])}. "
                f"A construction we have closed a mirror over does not diverge.")

        # G2 -- a codomain claim must be re-derivable from the pinned source.
        if entry["class"] == CODOMAIN:
            pattern = entry.get("codomain_witness_regex")
            if not isinstance(pattern, str) or not pattern:
                fails.append(
                    f"G2 unwitnessed-codomain-claim: {name} is class "
                    f"`codomain` but carries no `codomain_witness_regex`, so "
                    f"the claim cannot be re-derived from the pinned source.")
            else:
                rx = re.compile(pattern)
                witness = [i for i in matched if rx.search(statement_of(mirrors[i]))]
                if not witness:
                    fails.append(
                        f"G2 unwitnessed-codomain-claim: {name} claims codomain "
                        f"{entry.get('mathlib_codomain')!r}, but no pinned "
                        f"statement mentioning it matches "
                        f"/{pattern}/. Nothing re-derives the claim.")
        else:
            # Definitional / algorithmic / recursion-principle divergences are
            # invisible in the pinned STATEMENT -- they live in the definition.
            # This gate cannot re-derive them, so it demands that the reading be
            # recorded somewhere a referee can open.
            source = entry.get("mathlib_source")
            if not isinstance(source, dict) or not source.get("path"):
                fails.append(
                    f"G5 unbacked-divergence-claim: {name} is class "
                    f"{entry['class']!r}, which this gate cannot re-derive, and "
                    f"names no `mathlib_source.path`.")
            recorded = entry.get("recorded_in")
            if not isinstance(recorded, str) or not (ROOT / recorded).is_file():
                fails.append(
                    f"G5 unbacked-divergence-claim: {name} is class "
                    f"{entry['class']!r} and its `recorded_in` "
                    f"({recorded!r}) is not a file in this tree.")
    return fails


def read_candidates(path: pathlib.Path) -> list[dict[str, Any]]:
    if not path.is_file():
        die(f"no candidate file at {path}")
    doc = json.loads(path.read_text())
    if isinstance(doc, list):
        candidates = doc
    else:
        # `entries` lets the preregistered extension manifest be re-screened by
        # the gate on every run, rather than only at the moment it was written.
        candidates = doc.get("candidates")
        if candidates is None:
            candidates = doc.get("entries")
    if not isinstance(candidates, list):
        die(f"{path}: expected a list, {{'candidates': [...]}} "
            f"or {{'entries': [...]}}")
    return candidates


def statable_screen(path: pathlib.Path, registry: list[dict[str, Any]],
                    env: set[str], bridge: set[str]) -> int:
    """S5 (+ G6) -- both screens over candidates before preregistration."""
    candidates = read_candidates(path)
    admissible = env | bridge
    blocked = unstatable = glyphed = 0
    for cand in candidates:
        if not isinstance(cand, dict):
            die(f"{path}: a candidate is not an object")
        name = cand.get("name") or cand.get("source_name", "<unnamed>")
        fact_id = cand.get("fact_id")
        statement = cand.get("statement")
        constants = cand.get("constants")
        if not isinstance(statement, str):
            die(f"{path}: candidate {name} has no string `statement`")
        # Fail-closed: a candidate that does not carry its constant set cannot
        # be screened, and "no constants recorded" must not read as "clean".
        if not isinstance(constants, list) or not all(
                isinstance(c, str) for c in constants):
            die(f"{path}: candidate {name} has no `constants` list, so the "
                f"statable-here screen cannot decide it")
        hits = blockers_for(statement, registry)
        missing = sorted(set(constants) - admissible)
        glyphs = sorted(set(GLYPH_RE.findall(statement)))
        if hits:
            blocked += 1
            classes = ", ".join(f"{h['mathlib_constant']} ({h['class']})"
                                for h in hits)
            print(f"  BLOCKED     {name}  -- {classes}")
        elif missing:
            unstatable += 1
            print(f"  UNSTATABLE  {name}  -- {', '.join(missing[:4])}")
        elif glyphs and fact_id in KNOWN_GLYPHED_FACT_IDS:
            print(f"  GLYPH       {name}  -- {', '.join(glyphs)}  "
                  f"(recorded, ADR-0615: {fact_id})")
        elif glyphs:
            glyphed += 1
            print(f"  GLYPH       {name}  -- {', '.join(glyphs)}")
        else:
            print(f"  statable-ok {name}")
    print(f"\n{len(candidates)} candidate(s), {blocked} blocked by the "
          f"divergence registry, {unstatable} not statable here "
          f"(env {len(env)} + bridge {len(bridge)}), {glyphed} carrying an "
          f"elided-proof glyph.")
    status = 0
    if blocked:
        print("\nG6 blocked-candidate: preregistering these adds population "
              "that can never be closed.", file=sys.stderr)
        status = 1
    if unstatable:
        print("\nS5 unstatable-candidate: these mention constructions this "
              "kernel cannot name and cannot bridge to, so no proof effort "
              "reaches them. `screened-ok` against the divergence registry is "
              "necessary and NOT sufficient.", file=sys.stderr)
        status = 1
    if glyphed:
        print("\nS6 glyphed-candidate: the statement contains a Lean "
              "pretty-printer elision or hygiene glyph, so what is "
              "preregistered is not guaranteed to be a well-formed "
              "proposition -- see docs/contributor-guide/"
              "lean-surface-attestation.md.", file=sys.stderr)
        status = 1
    return status


def screen(path: pathlib.Path, registry: list[dict[str, Any]]) -> int:
    """G6 -- reject candidate propositions before preregistration."""
    candidates = read_candidates(path)
    blocked = 0
    for cand in candidates:
        if not isinstance(cand, dict):
            die(f"{path}: a candidate is not an object")
        name = cand.get("name", "<unnamed>")
        statement = cand.get("statement")
        if not isinstance(statement, str):
            die(f"{path}: candidate {name} has no string `statement`")
        hits = blockers_for(statement, registry)
        if hits:
            blocked += 1
            classes = ", ".join(f"{h['mathlib_constant']} ({h['class']})"
                                for h in hits)
            print(f"  BLOCKED     {name}  -- {classes}")
        else:
            print(f"  screened-ok {name}")
    print(f"\n{len(candidates)} candidate(s), {blocked} blocked.")
    if blocked:
        print("\nG6 blocked-candidate: preregistering these adds population "
              "that can never be closed, inflating the open count without "
              "adding work. Drop them, or state a local analogue instead.")
        return 1
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--facts-dir", type=pathlib.Path, default=DEFAULT_FACTS)
    ap.add_argument("--nursery", type=pathlib.Path, default=DEFAULT_NURSERY)
    ap.add_argument("--registry", type=pathlib.Path, default=DEFAULT_REGISTRY)
    ap.add_argument("--extension", type=pathlib.Path, default=DEFAULT_EXTENSION,
                    help="the additive nursery extension carrying its own split")
    ap.add_argument("--env-snapshot", type=pathlib.Path, default=DEFAULT_ENV)
    ap.add_argument("--vocabulary", type=pathlib.Path, default=DEFAULT_VOCAB)
    ap.add_argument("--catalog", type=pathlib.Path, default=DEFAULT_CATALOG)
    ap.add_argument("--screen", type=pathlib.Path,
                    help="screen candidates against the divergence registry")
    ap.add_argument("--statable", type=pathlib.Path,
                    help="screen candidates against BOTH the divergence "
                         "registry and the statable-here vocabulary")
    ap.add_argument("--floor", type=int, default=FLOOR,
                    help=f"G7's dispatchable floor (default {FLOOR}). May only "
                         f"RAISE the floor: a flag that could lower it would be "
                         f"a knob for silencing the gate, which is the failure "
                         f"mode this whole script exists to prevent.")
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    args = ap.parse_args()

    # The one-way ratchet on --floor. Checked before any work so a caller that
    # tried to relax the gate learns it here rather than from a green run.
    floor = args.floor
    if floor < FLOOR:
        # The wording deliberately avoids the token sequence the controls use
        # to detect that a named guard FIRED (`G7 <word>`): this is a rejected
        # INPUT, not a guard hit, and a message that reads as a hit makes the
        # "exactly one guard fired" assertion unusable for this case. The
        # controls caught exactly that on the first draft.
        die(f"--floor {floor} is below the built-in floor {FLOOR}. This flag "
            f"may only raise the floor. Lowering it silences the "
            f"queue-below-floor guard without adding a single dispatchable "
            f"row; if the floor is genuinely wrong, change FLOOR and say why "
            f"in the commit.")

    registry = load_registry(args.registry)
    if args.screen is not None:
        print(f"SCREEN {args.screen} against "
              f"{len(registry)} diverging construction(s)")
        return screen(args.screen, registry)
    if args.statable is not None:
        snapshot, vocabulary = load_vocabulary(args.env_snapshot, args.vocabulary)
        env = set(snapshot["declarations"])
        bridge = set(vocabulary["bridge"])
        print(f"SCREEN {args.statable} against "
              f"{len(registry)} diverging construction(s) and "
              f"{len(env)} kernel declaration(s) + {len(bridge)} bridge "
              f"constant(s)")
        # S1 runs HERE too. The rest of the vocabulary guards need the fact
        # ledger, which screening does not load; but a snapshot that lists
        # everything would make this mode admit everything, and that is the
        # failure direction nobody notices.
        snapshot_fails = [f for f in guard_vocabulary(snapshot, vocabulary, {}, {})
                          if f.startswith("S1 ")]
        for line in snapshot_fails:
            print(f"FAIL: {line}", file=sys.stderr)
        status = statable_screen(args.statable, registry, env, bridge)
        return 1 if snapshot_fails else status

    facts = load_facts(args.facts_dir)
    held, mutation = load_partitions(args.nursery, args.extension)
    snapshot, vocabulary = load_vocabulary(args.env_snapshot, args.vocabulary)
    catalog = load_catalog(args.catalog)
    buckets = classify(facts, held, mutation, registry)
    fails = guard_registry(facts, registry)
    fails += guard_vocabulary(snapshot, vocabulary, facts, catalog)

    dispatchable = buckets["dispatchable"]
    total_open = sum(len(v) for v in buckets.values())

    # The queue verdict is decided BEFORE any output is emitted, so that
    # `guard_failures` in --json mode carries it. It did not until 2026-08-30:
    # G4 was appended to `fails` AFTER the json.dumps, so a caller parsing the
    # JSON to decide whether the queue was healthy read `guard_failures: []`
    # while the process exited 1 with an EMPTY dispatchable set. The one
    # consumer shape this mode exists for was the one shape it lied to.
    queue_fail = None
    if not dispatchable:
        queue_fail = (
            "G4 empty-dispatchable-set: every open ml430 mirror is held-out, a "
            "mutation control, or structurally blocked. The flywheel's input "
            "queue is EMPTY -- the concept DAG and the fact ledger have nothing "
            "left to say to prove next. Refill the population (screening "
            "candidates with --screen first); do not dispatch at held-out rows "
            "and do not relax this check.")
    elif len(dispatchable) < floor:
        queue_fail = (
            f"G7 queue-below-floor: {len(dispatchable)} dispatchable mirror(s), "
            f"floor {floor}. The queue is not empty yet, which is the entire "
            f"point of failing here: a refill is a hand-authored edit to "
            f"gen-autogenesis-nursery-refill.py's FAMILY_MODULES and "
            f"FAMILY_ROUTES, so it needs lead time that a gate firing at zero "
            f"does not give. Run `python3 scripts/propose-nursery-refill.py` "
            f"for the families that are ready to draw from, then author the "
            f"draw. Do not lower the floor -- --floor may only raise it.")
    if queue_fail is not None:
        fails.append(queue_fail.split(":", 1)[0])

    if args.json:
        print(json.dumps({
            "open_mirrors": total_open,
            "held_out": sorted(buckets["held-out"]),
            "mutation": sorted(buckets["mutation"]),
            "blocked": [{"fact": i, "blockers": [
                {"construction": c, "class": k} for c, k in b]}
                for i, b in buckets["blocked"]],
            "dispatchable": sorted(dispatchable),
            "dispatchable_floor": floor,
            "queue_below_floor": len(dispatchable) < floor,
            "guard_failures": fails,
        }, indent=2, sort_keys=True))
    else:
        print(f"open ml430 mirrors: {total_open}")
        print(f"  held-out (blind evaluation, do not dispatch): "
              f"{len(buckets['held-out'])}")
        print(f"  mutation negative controls (never closable):  "
              f"{len(buckets['mutation'])}")
        print(f"  structurally blocked by a divergence:         "
              f"{len(buckets['blocked'])}")
        for ident, hits in buckets["blocked"]:
            classes = ", ".join(f"{c} ({k})" for c, k in hits)
            print(f"      {ident}  -- {classes}")
        print(f"  DISPATCHABLE:                                 "
              f"{len(dispatchable)}")
        for ident in dispatchable:
            print(f"      {ident}")

    for line in fails:
        print(f"FAIL: {line}", file=sys.stderr)

    # `--json` must emit JSON and nothing else on stdout: a caller that pipes
    # it into a parser is the whole point of the mode, and a trailing WARNING
    # line broke exactly that on the first draft.
    chatter = sys.stderr if args.json else sys.stdout

    if queue_fail is not None:
        print(f"\nFAIL: {queue_fail}", file=sys.stderr)

    if fails:
        return 1
    print("\nOK -- the dispatchable set is non-empty and the divergence "
          "registry is witnessed against the pinned statements.", file=chatter)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
