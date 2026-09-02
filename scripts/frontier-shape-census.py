#!/usr/bin/env python3
"""What the dependency-ready open frontier is SHAPED like, measured.

WHY THIS EXISTS. `scripts/fact-frontier.py --json` reports 217 dependency-ready
open facts, of which 209 are `proof-route-only` with no producer contract that
could match them (`diagnostics.unmatched_by_route_class`). Both existing
producer contracts are spent (ADR-1510). The next producer has to be designed
against those 209 -- and nobody had measured what they look like, so every
proposal for one was a guess about a population whose shape was unknown.

This tool measures that population and NOTHING else. It writes no producer, no
contract and no decline; it is a census, and the artifact it emits is an input
to designing a producer, never a producer itself.

WHAT A "SHAPE SIGNATURE" IS. Per fact, parsed from `formal.statement`:

    carriers                 ℕ / ℤ / ℝ / ... , from binder ascriptions
    conclusion head          Eq / le / lt / dvd / Iff / ModEq / And / Or / ...
    hypothesis heads         the same vocabulary, one per top-level arrow
    hypothesis count         len(hypothesis heads)
    bound variable count     universally quantified variables over a carrier
    conclusion constants     and whether each is DECLARED in this kernel
    provenance               an `ml430` Mathlib mirror, or native to this ledger
    mutation control         a deliberately-perturbed proposition (NOT a target)
    divergence-blocked       the mirror names a construction that is not our
                             construction, so it is a different proposition

Buckets are formed at two granularities -- FINE (the whole signature) and
COARSE (carrier x conclusion head x hypothesis-count band 0/1/2+) -- and ranked
by size. A producer is worth building for a bucket, not for a fact.

SIZE IS NOT TARGETABLE SIZE, and on this frontier the gap is the whole story.
A bucket's `size` counts its members; `targetable_size` subtracts the two
classes no producer can close however well it works -- mutation controls (false
by construction) and divergence-blocked mirrors (`Nat.testBit` returns a `Nat`
here and a `Bool` in Mathlib; no proof bridges that). The largest coarse bucket
in this census holds NINE facts and ZERO targetable ones. Ranked on raw size it
is exactly where a producer would have been pointed.

THE PARSER IS NOT A THIRD ONE. `scripts/brief-step0.py` already parses this
ledger's two `formal.statement` dialects (Lean surface, and the kernel's own
rendered type) and `scripts/fact-frontier.py` already resolves candidate
identifiers against the kernel environment. Both are imported and called. A
third parser would drift from them silently, and the drift would look like a
finding.

HELD-OUT FACTS ARE EXCLUDED FROM EVERY BUCKET, AND FROM EVERY MEMBER LIST.
`artifacts/autogenesis/nursery-v1.json` and `nursery-v2-extension.json`
preregister blind evaluation population; naming one of those ids in an artifact
a producer reads is itself a spend, because the split key is
`<family>:<statement-shape>` and a route for one member is evidence about its
siblings. Only AGGREGATE counts of the excluded set are reported.

    python3 scripts/frontier-shape-census.py            # write + print
    python3 scripts/frontier-shape-census.py --print    # print only
    python3 scripts/frontier-shape-census.py --check    # committed == fresh?

Exit status:
    0  the census was computed (and, without --check, written)
    1  --check: the committed artifact disagrees with a fresh computation
    2  UNANSWERABLE -- the frontier could not be built, so this run has no
       opinion in either direction. Deliberately distinct from 1: a checker
       that reports "disagrees" when it could not compute an answer is the
       checker-that-cannot-fail defect wearing the opposite mask.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import importlib.util
import json
import pathlib
import subprocess
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parent.parent
FACTS = ROOT / "artifacts" / "facts"
ARTIFACT = ROOT / "artifacts" / "autogenesis" / "frontier-shape-census-v1.json"

# The two nursery manifests, and BOTH are required. `check-autogenesis-holdout-
# isolation.py` reads both for exactly this reason and refuses a manifest that
# contributes zero held-out rows, because a gate reading only v1 would report
# PASS while leaving the extension's population unprotected. Its loader is the
# authority here and is imported rather than copied.
HOLDOUT_ISOLATION = ROOT / "scripts" / "check-autogenesis-holdout-isolation.py"
FACT_FRONTIER = ROOT / "scripts" / "fact-frontier.py"
BRIEF_STEP0 = ROOT / "scripts" / "brief-step0.py"
# The mirror-divergence registry: constructions where OUR definition and
# Mathlib's are different functions, so the mirror is a different proposition
# and no amount of proof effort closes it. A producer cannot close one of these
# any more than it can close a mutation control, so a census that ranked buckets
# without them would overstate every bucket it touched -- and the largest one
# here is entirely made of them.
DISPATCHABLE_FRONTIER = ROOT / "scripts" / "check-dispatchable-frontier.py"

# Conclusion-head classes. The key is what a PRODUCER would dispatch on, so the
# vocabulary is deliberately small: two heads that need the same proof move
# belong in one class. `le`/`lt` stay apart because a strict and a non-strict
# bound need different lemmas at the last step.
HEAD_CLASSES = {
    "Eq": "Eq", "eq": "Eq",
    "Ne": "Ne",
    "le": "le", "Nat.le": "le", "AxNat.le": "le", "Int.le": "le",
    "lt": "lt", "Nat.lt": "lt", "AxNat.lt": "lt", "Int.lt": "lt",
    "dvd": "dvd", "Nat.dvd": "dvd", "AxNat.dvd": "dvd", "Int.dvd": "dvd",
    "Iff": "Iff",
    "ModEq": "ModEq", "Nat.ModEq": "ModEq", "Int.ModEq": "ModEq",
    "And": "And", "Or": "Or", "Not": "Not",
    "Exists": "Exists",
    "True": "True", "False": "False",
}

# `formal.statement` dialects present in this ledger. Named so a bucket that is
# an artefact of the DIALECT rather than of the mathematics is visible as one.
DIALECT_SURFACE = "lean-surface"
DIALECT_RENDERED = "kernel-rendered"
DIALECT_SMTLIB = "smtlib"
DIALECT_PROSE = "prose"

BAND_LABELS = {0: "0", 1: "1"}


class CensusError(RuntimeError):
    """The census could not be computed. Always exit 2, never exit 1."""


def load_module(path: pathlib.Path, alias: str):
    spec = importlib.util.spec_from_file_location(alias, path)
    if spec is None or spec.loader is None:
        raise CensusError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


# ---------------------------------------------------------------------------
# inputs


def load_frontier(path: pathlib.Path | None = None) -> dict[str, Any]:
    """`fact-frontier.py --json`, run rather than re-implemented.

    Selection is that file's job and stays there: this reads
    `selection.ready_fact_ids` and each entry's `route_class`, and never
    recomputes either. A `--frontier` path is accepted so a caller that already
    has one (and the controls, which drive a fixture) does not pay for a second
    ~15 s run.
    """
    if path is not None:
        try:
            return json.loads(path.read_text())
        except (OSError, json.JSONDecodeError) as error:
            raise CensusError(f"frontier file unusable: {error}") from error
    try:
        done = subprocess.run(  # noqa: S603
            [sys.executable, str(FACT_FRONTIER), "--json"],
            cwd=ROOT, capture_output=True, text=True, timeout=600, check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise CensusError(f"fact-frontier.py did not run: {error}") from error
    if done.returncode != 0:
        raise CensusError(
            f"fact-frontier.py --json exited {done.returncode}: "
            f"{done.stderr.strip()[:400]}")
    try:
        return json.loads(done.stdout)
    except json.JSONDecodeError as error:
        raise CensusError(f"fact-frontier.py --json emitted no JSON: {error}") from error


def load_facts() -> dict[str, dict]:
    facts: dict[str, dict] = {}
    for path in sorted(FACTS.glob("*.json")):
        try:
            record = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError) as error:
            raise CensusError(f"fact {path.name} unreadable: {error}") from error
        facts[record["id"]] = record
    if not facts:
        raise CensusError("the fact ledger is empty; this census would be vacuous")
    return facts


def held_out_ids(frontier_module) -> tuple[frozenset[str], dict[str, Any]]:
    """Every preregistered held-out fact id, from BOTH nursery manifests.

    Two loaders are read and UNIONED, deliberately:

    * `check-autogenesis-holdout-isolation.py:held_out_facts()` -- the gate
      that protects this population. It requires both manifests and refuses a
      manifest contributing zero rows, so it cannot pass vacuously.
    * `fact-frontier.py:held_out_fact_ids()` -- the annotation the queue itself
      uses, which the brief for this lane named as the authority to reuse.

    They DISAGREE in this tree, and the disagreement is reported rather than
    smoothed over: the frontier's loader reads `nursery-v1.json` only, so it
    does not know the 2026-08-29 refill's held-out rows in
    `nursery-v2-extension.json`. Excluding the union is the safe direction --
    over-excluding costs a bucket member, under-excluding spends a blind
    population -- and the gap is surfaced in `population.held_out_source_gap`
    because it means `just next` currently under-warns on those rows.
    """
    isolation = load_module(HOLDOUT_ISOLATION, "holdout_isolation_for_census")
    try:
        gate_ids = frozenset(isolation.held_out_facts())
    except Exception as error:  # the gate raises its own IsolationError
        raise CensusError(f"held-out population unreadable: {error}") from error
    frontier_ids = frozenset(frontier_module.held_out_fact_ids())
    if not gate_ids:
        raise CensusError("the held-out population is empty; exclusion would be vacuous")
    return gate_ids | frontier_ids, {
        "isolation_gate_count": len(gate_ids),
        "fact_frontier_count": len(frontier_ids),
        "known_only_to_isolation_gate": len(gate_ids - frontier_ids),
        "known_only_to_fact_frontier": len(frontier_ids - gate_ids),
    }


def kernel_names(step0_module) -> tuple[frozenset[str] | None, dict[str, Any]]:
    """Declaration names from `brief-step0.py`'s environment snapshot.

    `None` when no snapshot is cached. That distinction is load-bearing: a
    missing snapshot must make `conclusion_constants_declared` UNKNOWN, never
    `false`. A stale binary reports a false ABSENT, and a false ABSENT here
    would say a producer cannot state a fact it can state perfectly well.
    """
    snapshot, freshness = step0_module.load_snapshot(ROOT)
    # SNAPSHOT-INTRINSIC FIELDS ONLY. The artifact must be a function of the
    # ledger and the snapshot, and of nothing else about the tree it was
    # produced in: `check-generated-artifact-ownership.py`'s OWNER arm re-runs
    # this producer in a sandbox holding only `artifacts/` and `scripts/`, and
    # requires the bytes back. Recording `freshness["state"]` or the worktree's
    # own kernel tree sha -- both of which read `crates/` and `.git`, absent
    # there -- would make that arm red for a reason that has nothing to do with
    # ownership. The freshness state is still computed; it is PRINTED, where a
    # reader wants it, rather than stored.
    state = {
        "snapshot_kernel_tree": None,
        "declaration_count": None,
        "provisional": None,
        "freshness": freshness["state"],
    }
    if snapshot is None:
        return None, state
    state["snapshot_kernel_tree"] = snapshot.get("head")
    state["declaration_count"] = snapshot.get("declaration_count")
    state["provisional"] = bool(snapshot.get("binary_stale"))
    names = frozenset(row["name"] for row in snapshot.get("declarations", []))
    return (names or None), state


def divergence_registry() -> tuple[list[dict[str, Any]] | None, Any]:
    """`(registry, blockers_for)`, or `(None, None)` when it cannot be read.

    `load_registry` calls `die()` (a `SystemExit`) on absence, which would take
    the whole census with it. Degrading to `None` is right, and the artifact
    records WHICH -- a `divergence_blocked` column that quietly meant nothing
    would be the checker-that-cannot-fail defect in a data file.
    """
    try:
        module = load_module(DISPATCHABLE_FRONTIER, "dispatchable_frontier_for_census")
        registry = module.load_registry(module.DEFAULT_REGISTRY)
    except (CensusError, SystemExit, OSError, ValueError):
        return None, None
    if not registry:
        return None, None
    return registry, module.blockers_for


# ---------------------------------------------------------------------------
# the signature


def dialect_of(statement: str, step0_module) -> str:
    text = step0_module.strip_decl_prefix(statement)
    stripped = text.lstrip()
    if stripped.startswith(";"):
        return DIALECT_PROSE
    if step0_module.is_rendered(text):
        return DIALECT_RENDERED
    if stripped.startswith("(") and ("(forall (" in text or "(assert " in text
                                     or "(declare-" in text):
        return DIALECT_SMTLIB
    return DIALECT_SURFACE


def classify_head(head: str | None, chunk: str = "") -> str:
    """A head constant, mapped into the small dispatch vocabulary.

    Three refinements are applied to what the shared parser returns, each for a
    spelling it does not cover and each verified against a real ledger row:

    * `b ≡ a [MOD n]` -- `≡` is in `brief-step0.py`'s NOTATION table but not in
      its `head_of` symbol scan, so a modular-congruence conclusion comes back
      as the name of a bound variable. `ModEq` is one of the classes a producer
      would dispatch on, so losing it would hide the class entirely.
    * `(n ^ m).Deficient` / `n.Coprime m` -- dot notation whose RECEIVER is a
      bound variable. `head_of` returns the receiver (`n`, or `n.Coprime`
      whole); the predicate is the capitalised leaf.
    * anything still resolving to a lone lower-case token is a binder name, not
      a constant, and is reported `unparsed` rather than made into a bucket of
      its own. A bucket keyed on a variable name is an artefact of the parser,
      and it would look exactly like a finding.
    """
    import re

    if "≡" in chunk and ("[MOD" in chunk or "[ZMOD" in chunk or "[SMOD" in chunk):
        return "ModEq"
    if head is None:
        return "unparsed"
    if head in HEAD_CLASSES:
        return HEAD_CLASSES[head]
    leaf = head.split(".")[-1]
    if leaf in HEAD_CLASSES:
        return HEAD_CLASSES[leaf]
    if leaf[:1].isupper():
        return f"other:{leaf}"
    suffix = re.search(r"\.([A-Z][A-Za-z0-9_']*)\s*$", chunk.strip())
    if suffix:
        return f"other:{suffix.group(1)}"
    if head[:1].isupper():
        return f"other:{head}"
    return "unparsed"


def bound_variable_count(statement: str, step0_module) -> int:
    """Universally quantified variables ascribed a carrier type.

    Counts binder GROUPS' names, not binder groups -- `∀ (m n : ℕ)` binds two.
    A binder whose ascribed type is not a carrier this project knows (a
    function, a `Prop`, a hypothesis name) is not a quantified variable for
    this purpose and is not counted; it shows up as a hypothesis head instead.
    """
    import re

    total = 0
    for _opener, names, sort in re.findall(
            r"([({\[⦃])\s*([^:)}\]⦄]+?)\s*:\s*([^)}\]⦄]+)[)}\]⦄]", statement):
        sort_text = sort.strip()
        carrier = None
        for token in step0_module.IDENT.findall(sort_text) + re.findall(r"[ℕℤℚℝℂ]", sort_text):
            if token in step0_module.CARRIERS:
                carrier = step0_module.CARRIERS[token]
                break
        if carrier is None or carrier in ("Prop",):
            continue
        total += len(names.split())
    return total


def carriers_of(statement: str, step0_module) -> list[str]:
    _bag, carriers = step0_module.statement_bag(statement)
    return sorted(carriers - {"Prop"})


def normalize_rendered_binders(text: str) -> str:
    """Rename LEADING rendered binders to the `xN` spelling the parser expects.

    `brief-step0.py:rendered_heads` peels binders matching `(xN : T) ->`,
    because the kernel's own inventory rows render every binder that way. Two
    facts in this ledger were pasted from a hand-written rendered type and use
    real names -- `((n : AxNat) -> ((h4 : AxNat.le …) -> …))` -- so no binder
    matched, and `head_of_rendered` returned the FIRST identifier it saw, the
    binder name `n`. That is a bucket named after a variable.

    This renames only the binder occurrences at the front of the type, one at a
    time, and never touches the body (an inner `fun (p : AxNat) =>` keeps its
    name). It feeds the shared parser rather than replacing it.
    """
    import re

    # ONLY the binder names change; the string is otherwise returned verbatim,
    # so the parser does its own peeling exactly as it does for an inventory
    # row. The cursor advances strictly and the depth is bounded, so this
    # cannot loop -- the first draft rebuilt the string as it went and did.
    # `\s*` FIRST: after peeling one binder the cursor sits on the space before
    # `((h4 : …)`, and a pattern starting `\(*` cannot match there. Measured on
    # `F:goldbach-strong`, which stopped after its first binder and reported a
    # conclusion head of `h4` -- a hypothesis's binder NAME.
    pattern = re.compile(r"\s*\(*\s*\(([A-Za-z_][A-Za-z0-9_']*)\s*:\s*")
    out = text
    position = 0
    for index in range(64):
        match = pattern.match(out, position)
        if match is None:
            return out
        name = match.group(1)
        if name.startswith("x") and name[1:].isdigit():
            replacement = name
        else:
            replacement = f"x{index}"
            out = out[: match.start(1)] + replacement + out[match.end(1):]
        cursor = match.end() + (len(replacement) - len(name))
        depth = 0
        while cursor < len(out):
            char = out[cursor]
            if char in "({[":
                depth += 1
            elif char in ")}]":
                if depth == 0:
                    break
                depth -= 1
            cursor += 1
        if cursor >= len(out):
            return out
        cursor += 1
        while cursor < len(out) and out[cursor].isspace():
            cursor += 1
        if not out.startswith("->", cursor):
            return out
        position = cursor + 2
    return out


def arrow_chunks(statement: str, step0_module) -> list[str]:
    """Top-level `→`-separated chunks of a surface statement, in order.

    The split is the same one `brief-step0.py:surface_heads` performs, so chunk
    `i` is the text its head `i` was read from. Recomputed here rather than
    returned by that function only because it does not return them.
    """
    import re

    text = step0_module.strip_decl_prefix(statement)
    if step0_module.is_rendered(text):
        return []
    body = re.sub(r"^\s*(∀|∃)[^,]*,", "", text).strip()
    depth = 0
    current = ""
    index = 0
    chunks: list[str] = []
    while index < len(body):
        char = body[index]
        if char in "({[":
            depth += 1
        elif char in ")}]":
            depth -= 1
        if depth == 0 and body.startswith("→", index):
            chunks.append(current)
            current = ""
            index += 1
            continue
        current += char
        index += 1
    chunks.append(current)
    return [chunk.strip() for chunk in chunks]


def conclusion_text(statement: str, step0_module) -> str:
    """The final arrow-chunk of a surface statement, or the whole rendered type."""
    chunks = arrow_chunks(statement, step0_module)
    if not chunks:
        return step0_module.strip_decl_prefix(statement)
    return chunks[-1]


def declared_state(statement: str, names: frozenset[str] | None,
                   frontier_module, proven: set[str]) -> tuple[bool | None, list[str]]:
    """`(every conclusion constant declared?, the ones that are not)`.

    `None` when no environment snapshot was available -- unknown, never false.
    Resolution is `fact-frontier.py`'s own `missing_declarations`, including
    its corroboration rule: a name used in an already-SETTLED fact's statement
    is not reported missing, because several capabilities here (`Nat.Prime`,
    `Nat.Coprime`) are built INLINE and have no declaration of their own.
    """
    if names is None:
        return None, []
    index = frontier_module.KernelIndex(
        names=names,
        namespaces=frozenset(name.split(".", 1)[0] for name in names if "." in name),
        row_count=len(names),
    )
    missing = frontier_module.missing_declarations(statement, index, proven)
    return (not missing), missing


def signature_of(fact: dict, entry: dict[str, Any], names: frozenset[str] | None,
                 step0_module, frontier_module, proven: set[str],
                 registry: list[dict[str, Any]] | None = None,
                 blockers_for=None) -> dict[str, Any]:
    statement = fact["formal"]["statement"]
    dialect = dialect_of(statement, step0_module)
    if dialect in (DIALECT_PROSE, DIALECT_SMTLIB):
        # Neither parser speaks these, and guessing at a head would invent a
        # bucket. Recorded as unparsed, with the dialect named, so the count is
        # visible rather than absorbed into an "other" bucket.
        concl, hyps = None, []
        bound = 0
        carriers: list[str] = []
        declared, missing = None, []
        chunks: list[str] = []
    elif dialect == DIALECT_RENDERED:
        text = normalize_rendered_binders(step0_module.strip_decl_prefix(statement))
        concl, hyps = step0_module.rendered_heads(text)
        bound = bound_variable_count(statement, step0_module)
        carriers = carriers_of(statement, step0_module)
        declared, missing = declared_state(text, names, frontier_module, proven)
        chunks = []
    else:
        # Chunk-aligned, so each head is classified against the text it was
        # read from. `surface_heads` drops a chunk whose head is None, which
        # would slide every later chunk one position left -- a misclassification
        # that leaves no trace. `head_of` is still the shared function.
        chunks = arrow_chunks(statement, step0_module)
        heads = [step0_module.head_of(chunk) for chunk in chunks]
        concl, hyps = heads[-1], heads[:-1]
        bound = bound_variable_count(statement, step0_module)
        carriers = carriers_of(statement, step0_module)
        declared, missing = declared_state(chunks[-1], names, frontier_module, proven)
    hypothesis_chunks = chunks[:-1] if chunks else [""] * len(hyps)
    conclusion_chunk = chunks[-1] if chunks else ""
    hypothesis_heads = [
        classify_head(head, chunk)
        for head, chunk in zip(hyps, hypothesis_chunks)
    ]
    return {
        "carriers": carriers,
        "conclusion_head": classify_head(concl, conclusion_chunk),
        "hypothesis_heads": hypothesis_heads,
        "hypothesis_count": len(hypothesis_heads),
        "bound_variable_count": bound,
        "conclusion_constants_declared": declared,
        "missing_conclusion_constants": missing,
        "dialect": dialect,
        "provenance": "ml430-mirror" if fact["id"].startswith("F:ml430-") else "native",
        "mutation_control": frontier_module.mutation_kind(fact) is not None,
        # `None` = the registry could not be read, so this column is unknown
        # rather than clear. `population.divergence_registry_loaded` says which.
        "divergence_blocked": (
            None if blockers_for is None
            else sorted({hit["mathlib_constant"] for hit in
                         blockers_for(statement, registry)}) or False),
        "fragment": entry["fragment"],
    }


def band(count: int) -> str:
    return BAND_LABELS.get(count, "2+")


def coarse_key(signature: dict[str, Any]) -> dict[str, Any]:
    return {
        "carriers": signature["carriers"],
        "conclusion_head": signature["conclusion_head"],
        "hypothesis_band": band(signature["hypothesis_count"]),
    }


def fine_key(signature: dict[str, Any]) -> dict[str, Any]:
    key = dict(signature)
    # The member list already carries per-fact detail; a fine bucket keyed on
    # the missing-constant NAMES, or on WHICH construction diverges, would be
    # one bucket per fact by construction.
    key.pop("missing_conclusion_constants", None)
    blocked = key.get("divergence_blocked")
    key["divergence_blocked"] = None if blocked is None else bool(blocked)
    return key


def rank_buckets(rows: list[dict[str, Any]], key_of) -> list[dict[str, Any]]:
    """Buckets, largest first, ties broken lexicographically on the key.

    `targetable_size` is size minus the members a producer CANNOT close however
    well it works, and there are two such classes, not one:

      mutation controls        deliberately perturbed propositions kept as
                               negative controls. Often FALSE; proving one is a
                               soundness alarm, not a result.
      divergence-blocked       the mirror names a construction that is not our
                               construction, so the statement is a different
                               proposition. `Nat.testBit` returns a `Nat` here
                               and a `Bool` in Mathlib; no proof effort bridges
                               that.

    Ranking on raw size alone is how the largest bucket in this census -- nine
    facts, every targetable one of them divergence-blocked -- would have been
    read as the obvious place to point a producer. All three numbers are
    reported; none replaces the others.
    """
    grouped: dict[str, list[dict[str, Any]]] = collections.defaultdict(list)
    keys: dict[str, dict[str, Any]] = {}
    for row in rows:
        key = key_of(row["signature"])
        token = canonical_json(key)
        keys[token] = key
        grouped[token].append(row)
    buckets = []
    for token, members in grouped.items():
        mutations = [m for m in members if m["signature"]["mutation_control"]]
        blocked = [m for m in members
                   if not m["signature"]["mutation_control"]
                   and m["signature"].get("divergence_blocked")]
        targetable = [m for m in members
                      if not m["signature"]["mutation_control"]
                      and not m["signature"].get("divergence_blocked")]
        buckets.append({
            "signature": keys[token],
            "size": len(members),
            "targetable_size": len(targetable),
            "mutation_control_count": len(mutations),
            "divergence_blocked_count": len(blocked),
            "fact_ids": sorted(m["fact_id"] for m in members),
        })
    buckets.sort(key=lambda b: (-b["size"], -b["targetable_size"],
                                canonical_json(b["signature"])))
    for index, bucket in enumerate(buckets, start=1):
        bucket["rank"] = index
    return buckets


# ---------------------------------------------------------------------------
# the census


def build_census(frontier: dict[str, Any], meta: dict[str, Any] | None = None
                 ) -> dict[str, Any]:
    """The census document. `meta`, when given, receives the tree-local facts
    that are deliberately NOT part of the artifact -- today only the snapshot's
    freshness, which the human report prints and the artifact must not carry."""
    facts = load_facts()
    frontier_module = load_module(FACT_FRONTIER, "fact_frontier_for_census")
    step0_module = load_module(BRIEF_STEP0, "brief_step0_for_census")
    held, holdout_gap = held_out_ids(frontier_module)
    names, snapshot_state = kernel_names(step0_module)
    if meta is not None:
        meta["freshness"] = snapshot_state["freshness"]
    proven = frontier_module.proven_identifier_names(facts)
    registry, blockers_for = divergence_registry()

    ready = list(frontier["selection"]["ready_fact_ids"])
    entries = {entry["fact_id"]: entry for entry in frontier["entries"]}

    censused: list[dict[str, Any]] = []
    excluded_held_out = 0
    for fact_id in sorted(ready):
        if fact_id in held:
            excluded_held_out += 1
            continue
        entry = entries.get(fact_id)
        fact = facts.get(fact_id)
        if entry is None or fact is None:
            raise CensusError(f"ready fact {fact_id} is not in the ledger or the frontier")
        censused.append({
            "fact_id": fact_id,
            "route_class": entry["route_class"],
            "contract_matched": bool(entry["matched_producer_contract_ids"]),
            "signature": signature_of(fact, entry, names, step0_module,
                                      frontier_module, proven,
                                      registry, blockers_for),
        })

    # The PRIMARY population: exactly the facts the next producer would have to
    # match -- dependency-ready, proof-route-only, no contract matching them
    # today, and not blind evaluation population. The rest is recorded beside
    # it, labeled, rather than dropped: "the other 8" is a number a reader of
    # this artifact should not have to reconstruct.
    primary = [row for row in censused
               if row["route_class"] == "proof-route-only" and not row["contract_matched"]]
    other = [row for row in censused if row not in primary]

    diagnostics = frontier.get("diagnostics", {})
    return {
        "schema_version": 1,
        "kind": "axeyum-frontier-shape-census",
        "authority": "artifacts/facts via scripts/fact-frontier.py --json",
        "produced_by": "scripts/frontier-shape-census.py",
        "ledger": frontier["ledger"],
        "frontier": {
            "frontier_sha256": frontier.get("frontier_sha256"),
            "diagnostics": diagnostics,
        },
        # `freshness` is a property of the TREE this ran in, not of the census,
        # so it is dropped here and printed instead -- see `kernel_names`.
        "environment_snapshot": {key: value for key, value in snapshot_state.items()
                                 if key != "freshness"},
        "population": {
            "ready_count": len(ready),
            "held_out_excluded": excluded_held_out,
            "held_out_authority": [
                "artifacts/autogenesis/nursery-v1.json",
                "artifacts/autogenesis/nursery-v2-extension.json",
            ],
            "held_out_source_gap": holdout_gap,
            "censused_count": len(censused),
            "primary_count": len(primary),
            "other_count": len(other),
            "divergence_registry_loaded": registry is not None,
            "primary_mutation_control_count": sum(
                1 for row in primary if row["signature"]["mutation_control"]),
            "primary_divergence_blocked_count": sum(
                1 for row in primary
                if not row["signature"]["mutation_control"]
                and row["signature"].get("divergence_blocked")),
            "primary_targetable_count": sum(
                1 for row in primary
                if not row["signature"]["mutation_control"]
                and not row["signature"].get("divergence_blocked")),
            "by_route_class": dict(sorted(collections.Counter(
                row["route_class"] for row in censused).items())),
            "by_dialect": dict(sorted(collections.Counter(
                row["signature"]["dialect"] for row in censused).items())),
        },
        "buckets": {
            "coarse": rank_buckets(primary, coarse_key),
            "fine": rank_buckets(primary, fine_key),
        },
        "other": sorted(other, key=lambda row: row["fact_id"]),
    }


# ---------------------------------------------------------------------------
# reporting


def format_signature(signature: dict[str, Any]) -> str:
    if "hypothesis_band" in signature:
        carriers = "+".join(signature["carriers"]) or "-"
        return (f"{carriers:<10} {signature['conclusion_head']:<12} "
                f"hyp:{signature['hypothesis_band']}")
    carriers = "+".join(signature["carriers"]) or "-"
    hyps = ",".join(signature["hypothesis_heads"]) or "-"
    declared = {True: "decl", False: "MISSING", None: "unknown"}[
        signature["conclusion_constants_declared"]]
    return (f"{carriers:<8} {signature['conclusion_head']:<10} "
            f"hyps[{hyps}] vars:{signature['bound_variable_count']} "
            f"{signature['provenance']} {declared}"
            + (" MUTATION-CONTROL" if signature["mutation_control"] else "")
            + (" DIVERGENCE-BLOCKED" if signature.get("divergence_blocked") else ""))


def report(census: dict[str, Any], limit: int = 12,
           meta: dict[str, Any] | None = None) -> str:
    pop = census["population"]
    lines = [
        "FRONTIER SHAPE CENSUS",
        f"  ledger              {census['ledger']['fact_count']} facts, "
        f"sha {census['ledger']['ledger_sha256'][:12]}",
        f"  dependency-ready    {pop['ready_count']}",
        f"  held-out excluded   {pop['held_out_excluded']}  "
        f"(aggregate only; no held-out id appears in this artifact)",
        f"  censused            {pop['censused_count']}",
        f"  primary population  {pop['primary_count']}  "
        f"(proof-route-only, no matching contract)",
        f"      of which mutation controls (FALSE by construction)  "
        f"{pop['primary_mutation_control_count']}",
        f"      of which divergence-blocked (not our proposition) "
        f"{pop['primary_divergence_blocked_count']}",
        f"      genuinely targetable                              "
        f"{pop['primary_targetable_count']}"
        + ("" if pop["divergence_registry_loaded"]
           else "   [divergence registry NOT loaded -- this number is an "
                "UPPER BOUND]"),
        f"  environment         {(meta or {}).get('freshness', 'not-recorded')}, "
        f"{census['environment_snapshot']['declaration_count']} declarations"
        + ("  PROVISIONAL (stale projection binary)"
           if census["environment_snapshot"]["provisional"] else ""),
        "",
        "COARSE BUCKETS (carrier x conclusion head x hypothesis band)",
    ]
    for bucket in census["buckets"]["coarse"][:limit]:
        lines.append(f"  {bucket['rank']:>3}. size {bucket['size']:>3} "
                     f"(targetable {bucket['targetable_size']:>3}, "
                     f"mut {bucket['mutation_control_count']:>2}, "
                     f"div {bucket['divergence_blocked_count']:>2})  "
                     f"{format_signature(bucket['signature'])}")
    lines.append("")
    lines.append("FINE BUCKETS (whole signature)")
    for bucket in census["buckets"]["fine"][:limit]:
        lines.append(f"  {bucket['rank']:>3}. size {bucket['size']:>3} "
                     f"(targetable {bucket['targetable_size']:>3}, "
                     f"mut {bucket['mutation_control_count']:>2}, "
                     f"div {bucket['divergence_blocked_count']:>2})  "
                     f"{format_signature(bucket['signature'])}")
    lines.append("")
    coarse = census["buckets"]["coarse"]
    biggest = max((b["targetable_size"] for b in coarse), default=0)
    if biggest < 10:
        lines.append(
            f"FINDING: the largest coarse bucket holds {biggest} targetable "
            f"fact(s), under 10. The frontier is NOT producer-shaped: there is "
            f"no population here large enough to repay a target-agnostic "
            f"producer. See docs/research/11-design-review/"
            f"2026-09-02-what-the-frontier-is-shaped-like.md.")
    else:
        lines.append(f"FINDING: the largest coarse bucket holds {biggest} "
                     f"targetable facts.")
    return "\n".join(lines)


def comparable(census: dict[str, Any], snapshot_matches: bool) -> dict[str, Any]:
    """The census with machine-local inputs normalized away when they differ.

    The environment snapshot lives in `~/.cache` and is per-host, so on a
    machine whose snapshot was built from a different kernel tree the
    `conclusion_constants_declared` fields legitimately differ from the
    committed ones. Comparing them anyway would make `--check` red for a reason
    that has nothing to do with the frontier -- a gate wrong about its own
    subject, which this repository has shipped three times in one day. So that
    one field is dropped from BOTH sides when, and only when, the snapshot
    identity differs; everything else -- every bucket, every member list, every
    count, the ledger digest -- is still compared exactly.
    """
    if snapshot_matches:
        return census
    reduced = json.loads(canonical_json(census))
    reduced["environment_snapshot"] = "normalized: snapshot identity differs"

    def strip(node: Any) -> None:
        if isinstance(node, dict):
            if "conclusion_constants_declared" in node:
                node["conclusion_constants_declared"] = "normalized"
                node["missing_conclusion_constants"] = "normalized"
            for value in node.values():
                strip(value)
        elif isinstance(node, list):
            for value in node:
                strip(value)

    strip(reduced)
    return reduced


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true",
                        help="compare the committed artifact against a fresh census")
    parser.add_argument("--print", dest="print_only", action="store_true",
                        help="print the table without writing the artifact")
    parser.add_argument("--frontier", type=pathlib.Path, default=None,
                        help="read a captured `fact-frontier.py --json` instead "
                             "of running one")
    parser.add_argument("--artifact", type=pathlib.Path, default=ARTIFACT)
    parser.add_argument("--limit", type=int, default=12)
    args = parser.parse_args(argv)

    meta: dict[str, Any] = {}
    try:
        frontier = load_frontier(args.frontier)
        census = build_census(frontier, meta)
    except CensusError as error:
        print(f"SHAPE_CENSUS|UNANSWERABLE|{error}", file=sys.stderr)
        return 2

    if args.check:
        if not args.artifact.is_file():
            print(f"SHAPE_CENSUS|FAIL|no committed artifact at "
                  f"{args.artifact.relative_to(ROOT)}; run "
                  f"scripts/frontier-shape-census.py", file=sys.stderr)
            return 1
        try:
            committed = json.loads(args.artifact.read_text())
        except json.JSONDecodeError as error:
            print(f"SHAPE_CENSUS|FAIL|committed artifact is not JSON: {error}",
                  file=sys.stderr)
            return 1
        matches = (isinstance(committed.get("environment_snapshot"), dict)
                   and committed["environment_snapshot"].get("snapshot_kernel_tree")
                   == census["environment_snapshot"]["snapshot_kernel_tree"])
        left = comparable(committed, matches)
        right = comparable(census, matches)
        if canonical_json(left) != canonical_json(right):
            print("SHAPE_CENSUS|FAIL|the committed census disagrees with a fresh "
                  "computation", file=sys.stderr)
            for field in ("population", "buckets", "ledger"):
                if canonical_json(left.get(field)) != canonical_json(right.get(field)):
                    print(f"    differs: {field}", file=sys.stderr)
            print("    remedy: run scripts/frontier-shape-census.py and commit "
                  "the artifact", file=sys.stderr)
            return 1
        note = "" if matches else "|environment=normalized"
        print(f"SHAPE_CENSUS|current|primary="
              f"{census['population']['primary_count']}|targetable="
              f"{census['population']['primary_targetable_count']}{note}|PASS")
        return 0

    print(report(census, args.limit, meta))
    if not args.print_only:
        args.artifact.parent.mkdir(parents=True, exist_ok=True)
        args.artifact.write_text(json.dumps(census, indent=2, sort_keys=True) + "\n")
        print(f"\nwrote {args.artifact.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
