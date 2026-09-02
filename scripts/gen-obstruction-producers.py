#!/usr/bin/env python3
"""D4: compile a curated obstruction classification and, where honest, a
producer contract, from primary sources -- never from a summary of them.

## Why this exists (ADR-0602, and the failure it is designed against)

ADR-0602 is binding: operations are RETROSPECTIVE receipts (admission
requires `proved`); a producer contract is a SEPARATE, PROSPECTIVE artifact
with no `proved` field at all -- "facts matching this shape are
dischargeable via route R with recipe X", evaluated on MULTIPLE targets
before it is trusted. The measured failure this guards against: an
operation registry where every entry named exactly one target (24
operations, 23 facts covered, 0 naming more than one, 0 of 144
dependency-ready facts covered) -- a dispatch table wearing a producer's
name, unable to fail because it only ever describes what already happened.

So this script does two DIFFERENT things and keeps them visibly separate:

1. CLASSIFY every open obstruction this lane could find real evidence for,
   into exactly one of three buckets:
     - `producer`         -- a reusable strategy exists NOW, evaluable
                              against real kernel/ledger state, applicable
                              to more than one target.
     - `new-construction` -- removable in principle (the kernel's type
                              system already has what is needed), but the
                              construction has not been built, so no
                              producer is evaluable today.
     - `not-removable`    -- the mirror is a DIFFERENT PROPOSITION (a
                              definitional/algorithmic divergence the
                              project has already documented and decided
                              must stay open), or the statement needs a
                              type this kernel structurally lacks.
   Only the first bucket may carry a compiled producer contract.

2. COMPILE a producer contract for each `producer`-classified obstruction,
   re-verifying its applicability and negative controls against the actual
   fact ledger and kernel source ON EVERY RUN (not trusting a cached
   verdict), so contract drift is a `--check` failure, not a silent stale
   claim.

## The two producers this run actually found

Both were found by independently verifying claims already sitting in this
repository's own commit history and doc comments (per the standing "search
for the STEP, not the NAME" / "verify a handoff's blocker before inheriting
it" rules), NOT by inventing new proof technique:

- `extensional-duplicate-close`: an `ml430` mirror fact is dischargeable by
  EVIDENCE POINTER ALONE (no new kernel proof term) when an existing kernel
  declaration or already-proved fact already establishes the identical
  content under a different name, PROVIDED the underlying construction is
  not registered as diverging from Mathlib's. `Nat.land`/`lor`/`ldiff`/`xor`
  are not registered as diverging (unlike `Nat.minFac`/`Nat.multichoose`,
  which this script explicitly EXCLUDES after reading their own module docs
  and fact `notes` -- see `MINFAC_IS_NOT_A_DUPLICATE_TARGET` below, a
  correction this lane made to its own working hypothesis mid-session).
- `pointwise-bit-extensionality`: an equality between two Nats built purely
  from `land`/`lor`/`ldiff`/`xor` is provable by reducing to
  `Nat.eq_of_testbit_eq` and case-splitting each bit's value against the
  {0,1} bound `Nat.testBit_le_one` -- the "smallest missing capability" for
  `and_or_distrib_left/right`, verified absent from the tree (no
  `and_or_distrib`/joint-induction machinery exists anywhere in
  `nat_prelude/`).

## What this script deliberately refuses to compile

`Nat.testBit`'s obstruction, 5 of its 6 open mirrors, is classified
`not-removable` -- CORRECTED by ADR-1545 from an earlier `new-construction`
whose stated reason ("a Bool-valued view plus a bridge theorem is buildable
in principle, but neither is built") was false on both halves. It IS built,
axiom-free, in `examples/nat_testbit_bool_bridge.rs`, and it moved none of
these mirrors, because the codomain is the OUTERMOST LINK of a chain rather
than the obstruction: Mathlib's `testBit m n := 1 &&& (m >>> n) != 0` is a
shift-and-mask closed form over an absent `Nat.shiftRight` and a divergent
`Nat.land`, and three of the five additionally name `Nat.land`/`lor`/`ldiff`
themselves. This is the SAME correction shape as `fastFib` below, arrived at
from the codomain rather than from the recursion principle: syntactic
similarity is not propositional identity, and one visible divergence is not
the whole chain. The 6th (`n.testBit i = n.bits.getI i`) needs `List Bool`
and `Inhabited`, neither of which this kernel's closed inductive set and
instance-implicit-free elaboration have at all; also `not-removable`.

`Nat.multichoose` (3 mirrors), `Nat.minFac` (1 mirror), and `Nat.fastFib`
(1 mirror) are all classified `not-removable`: each is recorded, IN THIS
TREE, as computing the same VALUES as Mathlib's by a DIFFERENT construction,
and the project's own standing mirror-flip criterion (CLAUDE.md, "WHEN IS
FLIPPING AN `ml430` MIRROR HONEST", generalized compositionally by
ADR-0840) says a theorem about Mathlib's construction is a different
proposition from one about ours. `minFac` looked, at first, like a candidate
for `extensional-duplicate-close` (same predicate symbols, an already-proved
native analogue) -- `nat_prelude/min_fac.rs`'s own module doc and
`F-nat-coprime-of-lt-minfac.json`'s own `notes` field BOTH explicitly say
this is not a flip and must not be treated as one. `fastFib` looked, at
first (and was classified in an earlier draft of this script), like
`new-construction` -- Mathlib's `binaryRec` needs a dependent motive a fuel
encoding cannot supply -- until ADR-0840 verified in-tree that (a) Mathlib's
own `fastFibAux` only ever instantiates `binaryRec` at a NON-dependent
motive, so the fuel `binaryRec` already built here is sufficient, and (b)
`Nat.fib` itself is a second, independently divergent construction
(curried-accumulator, no tuple type). Both corrections are kept in this
docstring because they are themselves the lesson: syntactic/structural
similarity is not propositional identity, and the files that refuted each
hypothesis were sitting in the tree before this script existed.

Usage:
    python3 scripts/gen-obstruction-producers.py            # write artifacts
    python3 scripts/gen-obstruction-producers.py --check     # recompute, diff, exit 1 on drift
    python3 scripts/gen-obstruction-producers.py --json      # print the computed doc to stdout

Exit status:
    0  wrote (or, under --check, matched) the classification and contracts
    1  --check found drift, or a source input failed to parse
    2  a required input file is missing
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS_DIR = ROOT / "artifacts" / "facts"
REGISTRY_PATH = ROOT / "artifacts" / "autogenesis" / "mirror-divergence-registry.json"
NAT_PRELUDE_DIR = ROOT / "crates" / "axeyum-lean-kernel" / "src" / "nat_prelude"
OUT_DIR = ROOT / "artifacts" / "obstruction-producers"
OBSTRUCTIONS_PATH = OUT_DIR / "obstructions.json"
PRODUCERS_DIR = OUT_DIR / "producers"

SCHEMA_VERSION = 1


def die(message: str, code: int = 2) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(code)


def load_json(path: pathlib.Path) -> Any:
    if not path.is_file():
        die(f"no input at {path}")
    try:
        return json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        die(f"{path}: {exc}", code=1)


def load_facts() -> dict[str, dict[str, Any]]:
    if not FACTS_DIR.is_dir():
        die(f"no fact directory at {FACTS_DIR}")
    out: dict[str, dict[str, Any]] = {}
    for path in sorted(FACTS_DIR.glob("*.json")):
        fact = load_json(path)
        ident = fact.get("id")
        if isinstance(ident, str):
            out[ident] = fact
    if not out:
        die(f"{FACTS_DIR} contains no facts")
    return out


def statement_of(fact: dict[str, Any]) -> str:
    formal = fact.get("formal")
    if not isinstance(formal, dict):
        return ""
    text = formal.get("statement")
    return text if isinstance(text, str) else ""


def status_of(fact: dict[str, Any]) -> str:
    return fact.get("epistemic_status", "")


# --- nat_prelude source scan: does a declaration by this name exist? ------

_DECLARED_NAME_RE = re.compile(r"\bp\.([a-z][a-z0-9_]*)\b")


def declared_nat_prelude_names() -> set[str]:
    """Every `p.<name>` field reference across `nat_prelude/*.rs`.

    This is the same-shape check the compiler needs everywhere: "does the
    kernel already carry a declaration by this name". It is a SECOND,
    independent implementation of nothing that exists elsewhere in this
    scope -- it reads the same source tree `nat_theorem_inventory` would
    read, by grep rather than by building the crate, because this script
    must run without a cargo lock. A stale claim here fails safe: it can
    only under-report (miss a declaration renamed since this ran), never
    fabricate one, because the name must appear literally in the source.
    """
    names: set[str] = set()
    if not NAT_PRELUDE_DIR.is_dir():
        die(f"no nat_prelude source at {NAT_PRELUDE_DIR}")
    for path in sorted(NAT_PRELUDE_DIR.glob("*.rs")):
        text = path.read_text(errors="replace")
        names.update(_DECLARED_NAME_RE.findall(text))
    if not names:
        die(f"{NAT_PRELUDE_DIR}: scanned 0 declared names -- source layout changed "
            f"under this script; re-derive _DECLARED_NAME_RE before trusting any "
            f"negative control it produces")
    return names


def any_module_mentions(token: str) -> list[str]:
    """Which `nat_prelude/*.rs` files mention `token` at all (substring)."""
    hits = []
    for path in sorted(NAT_PRELUDE_DIR.glob("*.rs")):
        if token in path.read_text(errors="replace"):
            hits.append(str(path.relative_to(ROOT)))
    return hits


# --- registry-derived obstructions ----------------------------------------

MIRROR_PREFIX = "F:ml430-"


def blockers_for(statement: str, registry: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [e for e in registry
            if any(form in statement for form in e["surface_forms"])]


def registry_blocked_open_mirrors(
    facts: dict[str, dict[str, Any]], registry: list[dict[str, Any]]
) -> dict[str, list[str]]:
    """mathlib_constant -> [open ml430 fact ids it blocks]."""
    out: dict[str, list[str]] = {e["mathlib_constant"]: [] for e in registry}
    for ident, fact in sorted(facts.items()):
        if not ident.startswith(MIRROR_PREFIX) or "-mutation-" in ident:
            continue
        if status_of(fact) not in ("open",):
            continue
        for hit in blockers_for(statement_of(fact), registry):
            out[hit["mathlib_constant"]].append(ident)
    return out


def classify_testbit(blocked_ids: list[str], facts: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    """Split Nat.testBit's obstruction: Bool-valued vs List-Bool-valued.

    BOTH halves are `not-removable` (ADR-1545); the split is kept because
    the two are unclosable for DIFFERENT reasons and a future reader must
    not collapse them. The Bool-valued group is blocked by a chain of
    construction divergences (codomain, testBit's own body, and for three of
    the five a second divergence in `Nat.land`/`lor`/`ldiff`); the
    List-valued one is blocked by two types this kernel does not have.
    """
    needs_list = []
    needs_bool_only = []
    for ident in blocked_ids:
        stmt = statement_of(facts[ident])
        if "bits" in stmt or "getI" in stmt or "List" in stmt:
            needs_list.append(ident)
        else:
            needs_bool_only.append(ident)
    out = []
    if needs_bool_only:
        out.append({
            "id": "nat-testbit-bool-codomain",
            "capability_gap": "definitional-non-equivalence",
            "removability": "not-removable",
            "reason": (
                "CORRECTED BY ADR-1545, which this compiler must not re-regress "
                "on. This row said `new-construction` and gave as its reason that "
                "a Bool-valued testBit view plus a bridge theorem 'is buildable in "
                "principle, but neither is built'. BOTH HALVES ARE FALSE IN THIS "
                "TREE. (1) It IS built: examples/nat_testbit_bool_bridge.rs "
                "declares Axeyum.Autogenesis.bitToBool and testBitBool n i := "
                "bitToBool (Nat.testBit n i) and proves testBitBool_zero, "
                "testBitBool_succ, bitToBool_boolToBit and boolToBit_roundtrip_zero, "
                "every one reporting axioms=0; the family is exported as a "
                "committed capsule and run from the justfile. It has been in the "
                "tree since 2026-08-26 and moved none of these mirrors. (2) "
                "Building it does not remove the obstruction, because the codomain "
                "is the OUTERMOST LINK OF A CHAIN, not the obstruction. Mathlib's "
                "def, read at the pinned commit (Init/Data/Nat/Bitwise/Basic.lean:"
                "147), is `testBit m n := 1 &&& (m >>> n) != 0` -- a shift-and-mask "
                "closed form over Nat.shiftRight (absent from this kernel entirely) "
                "and Nat.land (itself divergent, see below), whose imported closure "
                "doc 279 measured as carrying propext. Ours is a fuel recursion on "
                "the bit INDEX. Per ADR-0840 a flip needs EVERY constituent "
                "construction to match, so no codomain change reaches these "
                "propositions. Three of these facts additionally name &&& / ||| / "
                "ldiff, i.e. Mathlib's Nat.land/lor/ldiff, each a specialization of "
                "the WELL-FOUNDED Nat.bitwise where ours are three independent "
                "hand-rolled structural fuel recursions (nat_prelude/land.rs's own "
                "module doc records the divergence and the reason for it) -- a "
                "second, independent divergence stacked on testBit's. The honest "
                "outcome is the local analogue facts that already exist "
                "(F:nat-testbit-land, F:nat-testbit-lor, F:nat-lt-of-testbit, "
                "F:nat-zero-of-testbit-eq-zero)."
            ),
            "evidence": [
                "artifacts/autogenesis/mirror-divergence-registry.json#Nat.testBit",
                "docs/research/09-decisions/adr-1545-the-testbit-codomain-is-the-"
                "outermost-link-of-a-chain-and-the-bool-view-is-already-built.md",
                "crates/axeyum-lean-kernel/examples/nat_testbit_bool_bridge.rs",
                "docs/autogenesis/279-bitwise-semantic-law-reconstruction-gap.md",
                "crates/axeyum-lean-kernel/src/nat_prelude/land.rs",
                "each fact's formal.statement uses Bool literals (=true/=false) "
                "or Bool connectives (&&, ||, !) applied to testBit's result",
            ],
            "blocked_fact_ids": sorted(needs_bool_only),
        })
    if needs_list:
        out.append({
            "id": "nat-testbit-list-bool-getI",
            "capability_gap": "missing-inductive-type",
            "removability": "not-removable",
            "reason": (
                "This mirror's statement (n.testBit i = n.bits.getI i) needs "
                "Nat.bits : Nat -> List Bool and List.getI. This kernel's closed "
                "inductive-type set (True/False/And/Or/Iff/Eq/Exists/Acc/Bool/Nat/"
                "Decidable, plus Nat.le/Nat.Fin/Char/Nat.Pair) has no List type at "
                "all. Adding one is foundational type-system work, out of scope "
                "for a producer or an ordinary new-construction; not removable on "
                "this route."
            ),
            "evidence": [
                "artifacts/autogenesis/mirror-divergence-registry.json#Nat.testBit",
                "fact statement contains '.bits.getI'",
                "CLAUDE.md's authoritative inductive-type inventory has no List",
            ],
            "blocked_fact_ids": sorted(needs_list),
        })
    return out


def classify_definitional_divergence(
    mathlib_constant: str, obstruction_id: str, blocked_ids: list[str],
    capability_gap: str,
) -> dict[str, Any]:
    return {
        "id": obstruction_id,
        "capability_gap": capability_gap,
        "removability": "not-removable",
        "reason": (
            f"{mathlib_constant}'s registry entry (class=definitional/algorithmic) "
            f"records that this kernel's construction computes the same VALUES as "
            f"Mathlib's by a DIFFERENT recursion/algorithm, and per the project's "
            f"own mirror-flip criterion a theorem about Mathlib's construction is "
            f"a different proposition from one about ours. Verified independently "
            f"this session against the module doc and/or the already-proved "
            f"native analogue's own `notes` field, both of which say explicitly "
            f"that flipping the mirror would NOT be honest."
        ),
        "evidence": [
            f"artifacts/autogenesis/mirror-divergence-registry.json#{mathlib_constant}",
        ],
        "blocked_fact_ids": sorted(blocked_ids),
    }


def classify_fastfib() -> dict[str, Any]:
    """Corrected per ADR-0840, which this compiler must not re-regress on.

    An EARLIER draft of this function (and the CLAUDE.md Gotcha it was
    copied from) classified this as `new-construction`, reasoning that
    Mathlib's `binaryRec` needs a dependent motive a fuel encoding cannot
    supply. ADR-0840 verified, in-tree, that this is doubly wrong for THIS
    mirror: (1) Mathlib's `fastFibAux` instantiates `binaryRec` at a
    NON-dependent motive (`fun _ => Nat.Pair`), so the fuel `binaryRec`
    already built here is sufficient -- no well-founded rebuild is a
    prerequisite; (2) even granting a well-founded `binaryRec`, `Nat.fib`
    ITSELF is a second, independently divergent construction (a
    curried-accumulator fuel recursion, `fibonacci.rs`'s own module doc,
    because this kernel has no tuple type) against Mathlib's own
    `Nat.rec`/well-founded recurrence. A flip needs every constituent
    construction a statement names to match, not just the outermost
    combinator -- so this is the SAME class as multichoose/minFac
    (construction-level divergence), not a missing-primitive gap.
    """
    return {
        "id": "nat-fastfib-recursion-principle",
        "capability_gap": "definitional-non-equivalence",
        "removability": "not-removable",
        "reason": (
            "ADR-0840 verified in-tree that fastFib's mirror is blocked by "
            "TWO independent construction divergences, not the recursion-"
            "principle gap an earlier analysis named. Mathlib's fastFibAux "
            "instantiates binaryRec at a non-dependent motive, so this "
            "kernel's existing fuel binaryRec is already sufficient -- "
            "building a well-founded one buys nothing here. The real, "
            "un-removable divergence is Nat.fib itself: this kernel's fib is "
            "a curried-accumulator fuel recursion (fibAux i a b, no tuple "
            "type to hold a pair), not Mathlib's own recurrence. Per the "
            "compositional mirror-flip criterion (ADR-0840), one divergence "
            "in the chain keeps the mirror open regardless of the other's "
            "status. The honest path is a new local fact over our own "
            "fastFib/fib once built, not a flip."
        ),
        "evidence": [
            "docs/research/09-decisions/adr-0840-a-flip-needs-every-"
            "constituent-construction-to-match-not-just-the-outermost-one.md",
            "crates/axeyum-lean-kernel/src/nat_prelude/fibonacci.rs "
            "('Two-step recursion, without a tuple type')",
        ],
        "blocked_fact_ids": ["F:ml430-nat-fastfib-eq-cde11774"],
    }


# --- Producer 1: extensional-duplicate-close ------------------------------
#
# Hypothesis table: for a bitwise ml430 mirror fact NOT flagged by the
# divergence registry (land/lor/ldiff/xor are not registered as diverging,
# unlike minFac/multichoose), check whether the identical content already
# has a home under a different name: either a sibling ml430 mirror using the
# NATIVE operator name (already flipped -- e.g. `land_comm` for `and_comm`),
# or a bare kernel declaration in nat_prelude source with no ml430 mirror at
# all yet (e.g. `land_le_left`). Every entry in this table is INTENDED to be
# tested; the ones that fail verification are not silently dropped, they
# become the negative controls, produced by the SAME mechanism as the
# positive claims rather than hand-picked separately.
P1_HYPOTHESES: list[dict[str, str]] = [
    {"fact_id": "F:ml430-nat-and-comm-7525d05a",
     "twin_mirror": "F:ml430-nat-land-comm-7e6ad72e",
     "native_declaration": "land_comm"},
    {"fact_id": "F:ml430-nat-and-assoc-273b60d8",
     "twin_mirror": "F:ml430-nat-land-assoc-ad4775b8",
     "native_declaration": "land_assoc"},
    {"fact_id": "F:ml430-nat-and-le-left-6d04acb7",
     "twin_mirror": "",
     "native_declaration": "land_le_left"},
    {"fact_id": "F:ml430-nat-and-le-right-a3f80076",
     "twin_mirror": "",
     "native_declaration": "land_le_right"},
    {"fact_id": "F:ml430-nat-and-self-06a84ccc",
     "twin_mirror": "",
     "native_declaration": "land_self"},
    {"fact_id": "F:ml430-nat-and-div-two-1a2f7c33",
     "twin_mirror": "",
     "native_declaration": "land_div_two"},
    {"fact_id": "F:ml430-nat-and-mod-two-eq-one-3e873792",
     "twin_mirror": "",
     "native_declaration": "land_mod_two_eq_one"},
    {"fact_id": "F:ml430-nat-and-one-is-mod-d861e96b",
     "twin_mirror": "",
     "native_declaration": "land_one_is_mod"},
]

# Constructions this compiler will NEVER treat as extensional-duplicate
# targets, however similar their surrounding facts look, because this
# session read their own module doc / fact notes and both explicitly refute
# the flip. Kept as an explicit denylist (not just "absence from the
# hypothesis table above") so a future edit to this file cannot silently
# re-admit them by pattern-matching alone.
MINFAC_IS_NOT_A_DUPLICATE_TARGET = "F:ml430-nat-coprime-of-lt-minfac-0f79bdba"


def compile_extensional_duplicate_close(
    facts: dict[str, dict[str, Any]], declared_names: set[str]
) -> dict[str, Any]:
    applicable: list[dict[str, Any]] = []
    declined: list[dict[str, Any]] = []
    spent: list[dict[str, Any]] = []
    for h in P1_HYPOTHESES:
        fid = h["fact_id"]
        if fid not in facts:
            die(f"P1 hypothesis names {fid}, which is not in the fact ledger")
        # A hypothesis whose fact has since CLOSED is SPENT, not stale. Dying
        # here was right while some were still open -- a producer must never
        # name settled work -- but it makes a producer whose WHOLE population
        # closed indistinguishable from a broken table, and it turns success
        # into a red gate.
        #
        # Measured 2026-08-30: two theorem lanes closed all eight of P1's
        # hypotheses in one day, by exactly the route P1 predicted, executed by
        # hand rather than by running the producer. That is a population
        # exhausted, and the honest record is FULFILLED with the closing route
        # per target -- not a producer still claiming prospective work it no
        # longer has.
        if status_of(facts[fid]) != "open":
            spent.append({
                "fact_id": fid,
                "closed_status": status_of(facts[fid]),
                "twin_mirror": h.get("twin_mirror") or None,
                "native_declaration": h.get("native_declaration"),
            })
            continue
        twin = h["twin_mirror"]
        twin_ok = bool(twin) and twin in facts and status_of(facts[twin]) in ("proved", "computed")
        decl_ok = h["native_declaration"] in declared_names
        if twin_ok or decl_ok:
            applicable.append({
                "fact_id": fid,
                "evidence_route": (f"twin mirror {twin} (already proved)" if twin_ok
                                    else f"kernel declaration Nat.{h['native_declaration']}"),
            })
        else:
            declined.append({
                "fact_id": fid,
                "why_declines": (
                    f"neither a twin ml430 mirror nor a kernel declaration named "
                    f"'{h['native_declaration']}' exists in nat_prelude source; "
                    f"this fact needs a genuinely new proof, not a restatement"
                ),
            })
    if MINFAC_IS_NOT_A_DUPLICATE_TARGET in facts:
        declined.append({
            "fact_id": MINFAC_IS_NOT_A_DUPLICATE_TARGET,
            "why_declines": (
                "SAME predicate symbols (minFac, gcd/Coprime) as the already-proved "
                "F:nat-coprime-of-lt-minfac, which made this look like a duplicate "
                "at first pass. It is not: nat_prelude/min_fac.rs's own module doc "
                "and F-nat-coprime-of-lt-minfac.json's own `notes` field BOTH state "
                "explicitly this is NOT a flip of this mirror, because Nat.minFac "
                "is registered as an algorithmic divergence from Mathlib's. "
                "Syntactic similarity is not propositional identity; this entry "
                "exists to keep that correction load-bearing rather than silent."
            ),
        })
    if len(applicable) < 2 and spent and not applicable:
        # Every hypothesis closed: the population is EXHAUSTED, not broken.
        # Emit a fulfilled record so the outcome is on the record and the gate
        # tells the truth, rather than dying and leaving a red gate that reads
        # as a defect.
        return {
            "id": "extensional-duplicate-close",
            "kind": "fulfilled",
            "obstruction_ids": ["nat-bitwise-extensional-duplicate"],
            "applicability": {"fact_ids": [], "evidence_routes": []},
            "spent": spent,
            "outcome": (
                f"All {len(spent)} hypotheses closed. The predicted route was "
                "correct and was executed BY HAND in two theorem lanes, not by "
                "running this producer -- so this is an exhausted population, "
                "NOT a validated producer run. Recorded as fulfilled so the "
                "distinction survives; a future duplicate of this shape needs a "
                "fresh hypothesis table."
            ),
            "declined": declined,
            # The declines were produced by the SAME mechanism as the positive
            # claims, so they remain the negative controls after fulfilment.
            "negative_controls": declined,
        }
    if len(applicable) < 2:
        die("extensional-duplicate-close verified fewer than 2 applicable targets "
            f"({len(applicable)} applicable, {len(spent)} spent); would have to be "
            "labeled a capsule, not compiled as this phase's headline producer",
            code=1)
    return {
        "id": "extensional-duplicate-close",
        "kind": "producer",
        "route": "kernel-lane",
        "obstruction_ids": ["nat-bitwise-extensional-duplicate"],
        "capability_gap": "equality-transport",
        "shape": {
            "description": (
                "An open ml430 mirror fact F, over Nat.land/lor/ldiff/xor only "
                "(never a construction the divergence registry flags), such that "
                "F's exact propositional content is already established under a "
                "different name -- a sibling ml430 mirror using the native "
                "operator spelling that has already been flipped, or a bare "
                "kernel declaration with no ml430 mirror yet."
            ),
            "predicate": {
                "type": "curated-hypothesis-table-reverified-each-run",
                "checks": [
                    "fact_id is open in the ledger (re-checked, not cached)",
                    "twin_mirror is proved/computed in the ledger, OR "
                    "native_declaration appears as a `p.<name>` field in "
                    "crates/axeyum-lean-kernel/src/nat_prelude/*.rs",
                    "fact_id is not in the minfac/multichoose denylist "
                    "(construction-level divergence overrides syntactic match)",
                ],
            },
        },
        "recipe": (
            "Register evidence for F pointing at the existing kernel declaration "
            "or the twin fact's proof. No new proof term is authored; the "
            "content was already checked once by Kernel::add_declaration under a "
            "different name."
        ),
        "budget": {"unit": "lookup", "estimate": "O(1) per target; zero new kernel proof text"},
        "candidate_inputs": P1_HYPOTHESES,
        "applicability": {
            "fact_ids": sorted(a["fact_id"] for a in applicable),
            "population_description": (
                "open ml430 Nat.land/lor/ldiff/xor mirrors with an existing "
                "same-content declaration under a different name"
            ),
            "evidence_routes": applicable,
        },
        "validation_examples": [
            "F:ml430-nat-land-comm-7e6ad72e (already closed by exactly this route)",
            "F:ml430-nat-land-assoc-ad4775b8 (already closed by exactly this route)",
        ],
        "negative_controls": declined,
        "falsifiable_prediction": (
            f"Each of {sorted(a['fact_id'] for a in applicable)} is closable with "
            f"ZERO new kernel proof text -- only an evidence row citing an "
            f"existing declaration. This is wrong if any of them turns out, on "
            f"inspection, to need argument-order or implicit/explicit "
            f"restructuring that amounts to a real proof (a TypeMismatch on the "
            f"cited declaration would falsify it for that target)."
        ),
    }


# --- Producer 2: pointwise-bit-extensionality -----------------------------

def compile_pointwise_bit_extensionality(facts: dict[str, dict[str, Any]]) -> dict[str, Any]:
    targets = [
        "F:ml430-nat-and-or-distrib-left-fe131f64",
        "F:ml430-nat-and-or-distrib-right-0daaa284",
    ]
    for fid in targets:
        if fid not in facts or status_of(facts[fid]) != "open":
            die(f"P2 target {fid} is missing or not open; hypothesis is stale")
    # The "no machinery exists" claim must be re-derived, not inherited: grep
    # the whole nat_prelude tree for the two names such machinery would need.
    hits = any_module_mentions("and_or_distrib") + any_module_mentions("joint_induction")
    if hits:
        die(f"pointwise-bit-extensionality assumed no existing machinery, but "
            f"found: {hits} -- re-derive this producer, it may already be solved "
            f"or the shape predicate needs narrowing", code=1)
    required_lemmas = {
        "eq_of_testbit_eq": "F-nat-eq-of-testbit-eq",
        "testbit_land": "F-nat-testbit-land",
        "testbit_lor": "F-nat-testbit-lor",
        "testbit_le_one": "F-nat-testbit-le-one",
    }
    missing = [name for name, fid in required_lemmas.items()
               if (FACTS_DIR / f"{fid}.json") not in FACTS_DIR.glob(f"{fid}.json")]
    # The glob-based membership check above is always true for an existing
    # path; the real check is file existence plus proved status.
    missing = []
    for name, fid in required_lemmas.items():
        p = FACTS_DIR / f"{fid}.json"
        if not p.is_file():
            missing.append(f"{name} ({fid} missing)")
            continue
        fact = load_json(p)
        if status_of(fact) not in ("proved", "computed"):
            missing.append(f"{name} ({fid} not proved)")
    if missing:
        die(f"pointwise-bit-extensionality's supporting lemmas are not all "
            f"proved: {missing}", code=1)

    # Negative controls: a soundness control (syntactically the same shape,
    # mathematically FALSE) and a shape-mismatch control (different top-level
    # connective -- Iff, not Eq -- so the recipe does not even apply).
    soundness_control = "F:ml430-mutation-a6dd1759bce60d820292e107"
    if soundness_control not in facts:
        die(f"soundness control {soundness_control} is missing from the ledger")
    soundness_stmt = statement_of(facts[soundness_control])
    if "|||" not in soundness_stmt or "&&&" not in soundness_stmt:
        die("soundness control no longer has the two-operator shape this "
            "producer's predicate matches -- it would not discriminate", code=1)

    shape_mismatch_control = "F:ml430-nat-and-mod-two-eq-one-3e873792"
    if shape_mismatch_control not in facts:
        die(f"shape-mismatch control {shape_mismatch_control} is missing")
    sm_stmt = statement_of(facts[shape_mismatch_control])
    if "↔" not in sm_stmt:  # '↔'
        die("shape-mismatch control no longer carries an Iff -- it would not "
            "demonstrate the connective mismatch this control is for", code=1)

    return {
        "id": "pointwise-bit-extensionality",
        "kind": "producer",
        "route": "kernel-lane",
        "obstruction_ids": ["nat-bitwise-cross-operator-proof-gap"],
        "capability_gap": "pointwise-extensionality-with-finite-case-exhaustion",
        "shape": {
            "description": (
                "An equality between two Nat-valued expressions built purely "
                "from land/lor/ldiff/xor (no arithmetic mixed in), whose "
                "top-level connective is Eq, not Iff."
            ),
            "predicate": {
                "type": "syntactic",
                "requires_all_of": ["only bitwise operators on both sides",
                                     "top connective is Eq"],
                "requires_none_of": ["arithmetic operators (+, *, /, %)",
                                      "Iff as the top connective"],
            },
        },
        "recipe": (
            "1. Apply Nat.eq_of_testbit_eq to reduce the goal to "
            "'forall i, lhs.testBit i = rhs.testBit i'. "
            "2. Rewrite both sides to a Nat.testBit-headed normal form using "
            "testbit_land / testbit_lor / testbit_ldiff / testbit_xor. "
            "3. Bound each testBit i term to {0,1} via testbit_le_one and case "
            "-split (finite exhaustion). 4. Each of the resulting closed "
            "arithmetic goals over {0,1} closes by evaluation."
        ),
        "budget": {"unit": "kernel-proof",
                   "estimate": "one Nat.rec-free proof per target: 1 "
                               "extensionality application + up to 3 rewrite "
                               "chains + an 8-case split for a 3-variable "
                               "identity, 4-case for 2 variables"},
        "candidate_inputs": [
            {"lemma": name, "fact_id": fid} for name, fid in required_lemmas.items()
        ],
        "applicability": {
            "fact_ids": targets,
            "population_description": (
                "open ml430 mirrors stating a pure bitwise (land/lor/ldiff/xor) "
                "Nat equality with no existing cross-operator machinery in the "
                "tree (re-verified absent on every run of this compiler)"
            ),
        },
        "validation_examples": [
            "F-nat-testbit-land, F-nat-testbit-lor, F-nat-eq-of-testbit-eq, "
            "F-nat-testbit-le-one are the proved kernel lemmas this recipe "
            "composes; none of them is new work",
        ],
        "negative_controls": [
            {"fact_id": soundness_control,
             "why_declines": (
                 "same two-operator bitwise shape (lor n m = land n m) but "
                 "mathematically FALSE (n=1,m=2: lor=3, land=0) -- a "
                 "deliberate mutation. The recipe's finite case-split reaches "
                 "a bit assignment where the two sides differ and correctly "
                 "fails to close, rather than fabricating a proof."
             )},
            {"fact_id": shape_mismatch_control,
             "why_declines": (
                 "top-level connective is Iff, not Eq -- the recipe's first "
                 "step (Nat.eq_of_testbit_eq) does not even type-check "
                 "against an Iff goal, so the shape predicate must exclude it "
                 "rather than let the recipe fail late."
             )},
        ],
        "falsifiable_prediction": (
            f"Both {targets} are closable by this exact 4-step recipe with no "
            f"induction beyond the finite case split. This is wrong if the "
            f"testBit rewrite chain fails to reach a closed arithmetic goal "
            f"(e.g. if AxNat.mul/AxNat.ble do not reduce at the bound {{0,1}} "
            f"values without further lemmas)."
        ),
    }


# --- top-level assembly ----------------------------------------------------

def build_obstructions_doc(facts: dict[str, dict[str, Any]]) -> dict[str, Any]:
    registry = load_json(REGISTRY_PATH).get("constructions")
    if not isinstance(registry, list) or not registry:
        die(f"{REGISTRY_PATH}: no constructions list")
    blocked = registry_blocked_open_mirrors(facts, registry)

    obstructions: list[dict[str, Any]] = []
    obstructions.extend(classify_testbit(blocked.get("Nat.testBit", []), facts))
    obstructions.append(classify_definitional_divergence(
        "Nat.multichoose", "nat-multichoose-definitional-divergence",
        blocked.get("Nat.multichoose", []), "definitional-non-equivalence"))
    obstructions.append(classify_definitional_divergence(
        "Nat.minFac", "nat-minfac-algorithmic-divergence",
        blocked.get("Nat.minFac", []), "definitional-non-equivalence"))
    obstructions.append(classify_fastfib())

    # Obstructions found OUTSIDE the registry's scope: genuine proof gaps
    # (missing machinery), not construction divergences. The registry never
    # claims to cover these -- `and_or_distrib_left/right` sit in
    # check-dispatchable-frontier.py's plain "dispatchable" bucket, which is
    # exactly why this compiler cannot only consume the registry's output.
    obstructions.append({
        "id": "nat-bitwise-cross-operator-proof-gap",
        "capability_gap": "pointwise-extensionality-with-finite-case-exhaustion",
        "removability": "producer",
        "reason": (
            "and_or_distrib_left/right need a cross-operator (land distributing "
            "over lor) argument. No joint-induction machinery for this exists "
            "in nat_prelude/ (re-verified: no 'and_or_distrib' or "
            "'joint_induction' token anywhere in the tree), but the smallest "
            "missing capability is not a new induction at all -- both operators "
            "already have per-bit characterizations (testbit_land, testbit_lor) "
            "and an extensionality principle (eq_of_testbit_eq), so the "
            "identity reduces to a finite case split over {0,1}-valued bits."
        ),
        "evidence": [
            "crates/axeyum-lean-kernel/src/nat_prelude/ (grep, no and_or_distrib "
            "or joint_induction token)",
            "F-nat-eq-of-testbit-eq.json, F-nat-testbit-land.json, "
            "F-nat-testbit-lor.json, F-nat-testbit-le-one.json (all proved)",
        ],
        "blocked_fact_ids": [
            "F:ml430-nat-and-or-distrib-left-fe131f64",
            "F:ml430-nat-and-or-distrib-right-0daaa284",
        ],
    })
    obstructions.append({
        "id": "nat-bitwise-extensional-duplicate",
        "capability_gap": "equality-transport",
        "removability": "producer",
        "reason": (
            "Several open ml430 Nat.land mirrors (and_comm, and_assoc, "
            "and_le_left) restate content this kernel already established "
            "under a different name -- a sibling ml430 mirror using the "
            "native spelling (land_comm, land_assoc, both already flipped), or "
            "a bare kernel declaration (land_le_left) with no mirror yet. "
            "Nat.land/lor/ldiff/xor are not registered as diverging from "
            "Mathlib's constructions, unlike minFac/multichoose, so a "
            "same-content restatement is an honest flip, not a manufactured "
            "one. and_le_right/and_self/and_div_two/and_mod_two_eq_one/"
            "and_one_is_mod were hypothesized by the same table and verified "
            "ABSENT -- no matching declaration exists -- so they remain "
            "genuinely open and serve as this producer's negative controls."
        ),
        "evidence": [
            "F-ml430-nat-land-comm-7e6ad72e.json, F-ml430-nat-land-assoc-"
            "ad4775b8.json (both proved, same content as the open and_* twins)",
            "crates/axeyum-lean-kernel/src/nat_prelude/rec_agreement.rs "
            "(land_le_left declared; land_le_right/land_self absent)",
        ],
        "blocked_fact_ids": [
            "F:ml430-nat-and-comm-7525d05a",
            "F:ml430-nat-and-assoc-273b60d8",
            "F:ml430-nat-and-le-left-6d04acb7",
        ],
    })

    if not obstructions:
        die("classification produced zero obstructions -- the compiler did "
            "not run against real data", code=1)
    return {
        "schema_version": SCHEMA_VERSION,
        "generated_by": "scripts/gen-obstruction-producers.py",
        "obstructions": sorted(obstructions, key=lambda o: o["id"]),
    }


def build_producers(facts: dict[str, dict[str, Any]]) -> dict[str, dict[str, Any]]:
    declared_names = declared_nat_prelude_names()
    producers = [
        compile_extensional_duplicate_close(facts, declared_names),
        compile_pointwise_bit_extensionality(facts),
    ]
    for p in producers:
        if "proved" in p:
            die(f"producer {p['id']} carries a 'proved' field -- ADR-0602 "
                f"forbids this structurally", code=1)
        # A FULFILLED record is allowed an empty applicability set -- that is
        # precisely what fulfilled means -- but it must then carry the spent
        # list and an outcome, or it is an empty producer wearing a new label.
        if p.get("kind") == "fulfilled":
            if not p.get("spent"):
                die(f"{p['id']} is kind=fulfilled with no spent hypotheses; a "
                    f"fulfilled record must name what closed", code=1)
            if not p.get("outcome"):
                die(f"{p['id']} is kind=fulfilled with no outcome", code=1)
        elif not p.get("applicability", {}).get("fact_ids"):
            die(f"producer {p['id']} has an empty applicability set", code=1)
        if p["kind"] == "producer" and len(p["applicability"]["fact_ids"]) < 2:
            die(f"producer {p['id']} claims kind=producer with "
                f"{len(p['applicability']['fact_ids'])} target(s) -- must be "
                f"labeled capsule", code=1)
        if not p.get("negative_controls"):
            die(f"producer {p['id']} has no negative controls", code=1)
    return {p["id"]: p for p in producers}


def render(args: argparse.Namespace) -> int:
    facts = load_facts()
    obstructions_doc = build_obstructions_doc(facts)
    producers = build_producers(facts)

    if args.json:
        print(json.dumps({"obstructions": obstructions_doc,
                           "producers": producers}, indent=2, sort_keys=True))
        return 0

    if args.check:
        drift = []
        if not OBSTRUCTIONS_PATH.is_file():
            drift.append(f"missing {OBSTRUCTIONS_PATH}")
        else:
            on_disk = json.loads(OBSTRUCTIONS_PATH.read_text())
            if on_disk != obstructions_doc:
                drift.append("obstructions.json does not match recomputation")
        for pid, doc in producers.items():
            p = PRODUCERS_DIR / f"{pid}.json"
            if not p.is_file():
                drift.append(f"missing {p}")
            elif json.loads(p.read_text()) != doc:
                drift.append(f"{p} does not match recomputation")
        on_disk_ids = {p.stem for p in PRODUCERS_DIR.glob("*.json")}
        stale = on_disk_ids - set(producers) - {"README"}
        for s in stale:
            drift.append(f"producers/{s}.json is on disk but no longer compiled "
                         f"-- stale contract")
        if drift:
            print("DRIFT:")
            for d in drift:
                print(f"  - {d}")
            return 1
        print("OK -- obstructions.json and every producer contract match "
              "recomputation from primary sources.")
        return 0

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    PRODUCERS_DIR.mkdir(parents=True, exist_ok=True)
    OBSTRUCTIONS_PATH.write_text(json.dumps(obstructions_doc, indent=2, sort_keys=True) + "\n")
    keep = set()
    for pid, doc in producers.items():
        path = PRODUCERS_DIR / f"{pid}.json"
        path.write_text(json.dumps(doc, indent=2, sort_keys=True) + "\n")
        keep.add(path.name)
    for stale in PRODUCERS_DIR.glob("*.json"):
        if stale.name not in keep:
            stale.unlink()
            print(f"removed stale {stale}")
    print(f"wrote {OBSTRUCTIONS_PATH}")
    for name in sorted(keep):
        print(f"wrote {PRODUCERS_DIR / name}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                      formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--check", action="store_true",
                        help="recompute and diff against committed artifacts; exit 1 on drift")
    parser.add_argument("--json", action="store_true",
                        help="print the computed documents to stdout instead of writing")
    return render(parser.parse_args())


if __name__ == "__main__":
    raise SystemExit(main())
