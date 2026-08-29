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

It also runs the registry as a SCREEN over candidate propositions before they
are preregistered (`--screen`), because a generator that emits more mirrors over
a diverging construction adds unclosable population and inflates the open count
without adding work.

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

Usage:
    python3 scripts/check-dispatchable-frontier.py
    python3 scripts/check-dispatchable-frontier.py --screen candidates.json
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

MIRROR_PREFIX = "F:ml430-"
SETTLED = {"proved", "refuted", "computed"}
CODOMAIN = "codomain"
CLASSES = {CODOMAIN, "definitional", "algorithmic", "recursion-principle"}

# When the dispatchable set gets this small the queue is about to empty. Not a
# failure -- a failure at this point would fire on a healthy-but-narrow queue --
# but it must be said out loud, because the whole point of this script is that
# nobody noticed the number falling.
NARROW = 3


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


def load_partitions(nursery: pathlib.Path) -> tuple[set[str], set[str]]:
    """(held-out fact ids, mutation fact ids) from the preregistered split."""
    if not nursery.is_file():
        die(f"no nursery manifest at {nursery}")
    manifest = json.loads(nursery.read_text())
    entries = manifest.get("entries")
    if not isinstance(entries, list):
        die(f"{nursery}: no `entries` list")
    held, mutation = set(), set()
    for entry in entries:
        ident = entry.get("fact_id")
        if not isinstance(ident, str):
            continue
        if entry.get("partition") == "held-out":
            held.add(ident)
        if entry.get("mutation_of"):
            mutation.add(ident)
    return held, mutation


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


def screen(path: pathlib.Path, registry: list[dict[str, Any]]) -> int:
    """G6 -- reject candidate propositions before preregistration."""
    if not path.is_file():
        die(f"no candidate file at {path}")
    doc = json.loads(path.read_text())
    candidates = doc.get("candidates") if isinstance(doc, dict) else doc
    if not isinstance(candidates, list):
        die(f"{path}: expected a list of candidates or {{'candidates': [...]}}")
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
    ap.add_argument("--screen", type=pathlib.Path,
                    help="screen candidate propositions before preregistration")
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    args = ap.parse_args()

    registry = load_registry(args.registry)
    if args.screen is not None:
        print(f"SCREEN {args.screen} against "
              f"{len(registry)} diverging construction(s)")
        return screen(args.screen, registry)

    facts = load_facts(args.facts_dir)
    held, mutation = load_partitions(args.nursery)
    buckets = classify(facts, held, mutation, registry)
    fails = guard_registry(facts, registry)

    dispatchable = buckets["dispatchable"]
    total_open = sum(len(v) for v in buckets.values())

    if args.json:
        print(json.dumps({
            "open_mirrors": total_open,
            "held_out": sorted(buckets["held-out"]),
            "mutation": sorted(buckets["mutation"]),
            "blocked": [{"fact": i, "blockers": [
                {"construction": c, "class": k} for c, k in b]}
                for i, b in buckets["blocked"]],
            "dispatchable": sorted(dispatchable),
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

    # G4 -- the alarm this script exists for. There is no floor to lower: the
    # only way through is to add population that can actually be worked.
    # `--json` must emit JSON and nothing else on stdout: a caller that pipes
    # it into a parser is the whole point of the mode, and a trailing WARNING
    # line broke exactly that on the first draft.
    chatter = sys.stderr if args.json else sys.stdout

    if not dispatchable:
        print(
            "\nFAIL: G4 empty-dispatchable-set: every open ml430 mirror is "
            "held-out, a mutation control, or structurally blocked. The "
            "flywheel's input queue is EMPTY -- the concept DAG and the fact "
            "ledger have nothing left to say to prove next. Refill the "
            "population (screening candidates with --screen first); do not "
            "dispatch at held-out rows and do not relax this check.",
            file=sys.stderr)
        fails.append("G4 empty-dispatchable-set")
    elif len(dispatchable) <= NARROW:
        print(f"\nWARNING: only {len(dispatchable)} dispatchable mirror(s) "
              f"remain. The queue is about to empty; refill it before it does.",
              file=chatter)

    if fails:
        return 1
    print("\nOK -- the dispatchable set is non-empty and the divergence "
          "registry is witnessed against the pinned statements.", file=chatter)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
