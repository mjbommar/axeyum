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
import importlib.util
import json
import pathlib
import re
import sys
import types
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
# The ADR-0542 amendment ledger. It is named `-v1` because nursery-v1 was the
# first population to need one; it is the ledger for BOTH cohorts, and
# `check-autogenesis-holdout-isolation.py` names it as the single repair site
# for a spent held-out family regardless of which manifest carries the row.
SPLIT_POLICY = AUTOGEN / "mathlib-nursery-split-policy-v1.json"

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

# The split key is `<family>:<statement-shape>` BECAUSE a route for one member
# is evidence about its siblings -- so a refill row over the same constructions
# would spend blind-evaluation value without anyone touching the partition.
# Excluded by construction, not by care.
#
# UPDATED 2026-08-30 (draw 5). When this was written the two surviving v1
# held-out families were `natural-logarithm` (21 open) and
# `natural-square-root` (16). `natural-logarithm` was amended OUT of held-out
# the same day under ADR-0542 (ordinary hand development in nat_prelude/log.rs
# and clog.rs spent it), so `Nat.log`/`Nat.clog`/`Nat.log2` no longer guard a
# blind family. **They are kept here deliberately.** Dropping them is a
# behaviour change that unlocks `Mathlib.Data.Nat.Log`'s 34 candidates for a
# development/train family, which is a decision for a draw that wants them and
# not a side effect of an unrelated draw; keeping them over-excludes, which is
# the safe direction. `Nat.sqrt` is still live -- `natural-square-root` is now
# the ONLY surviving v1 held-out family.
#
# Note the consequence for anyone reading `propose-nursery-refill.py`'s output:
# the PROPOSER does not apply this screen and the GENERATOR does, so
# `Mathlib.Data.Nat.Log` and `Mathlib.Data.Nat.Sqrt` appear in the proposer's
# "ready families" and yield ZERO candidates here. The ready set is 17 drawable
# of the 19 reported.
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
    # --- draw 2, 2026-08-29 (ADR-0615) ---------------------------------------
    # Selected from the 22 modules carrying >= 10 fully screened, unused
    # candidates, under one further constraint the existing rules do not state
    # and R2 cannot see: R2 forbids reusing a v1 family NAME, but a new family
    # over the same MATHEMATICS as an already-partitioned one leaks just as
    # much. So `Mathlib.Data.Nat.ModEq` (v1 natural-modular-equivalence),
    # `*.Gcd` (v1 natural-gcd / integer-gcd), `*.Prime.*` (v1 natural-primes),
    # `*.Factorial.*`, `*.Choose.*` and `*.Bitwise.*` are all excluded despite
    # having ample supply, because each would sit blind beside a family lanes
    # are working. The four below are the only remaining coherent modules whose
    # every adjacency lands in the SAME partition:
    #
    #   integer-natcast       held-out     no existing family covers casts
    #   natural-coprimality   development  adjacent to v1 natural-gcd, also development
    #   natural-modulus       train        adjacent to v2 natural-division, also train
    #   natural-induction-and-divisibility
    #                         held-out     its dvd rows are adjacent to v2
    #                                      natural-divisibility, also held-out
    #
    # The assignment is still the mechanical module-path cycle; what was chosen
    # by judgement is the SET, and only against already-published partitions --
    # no target outcome was consulted.
    "integer-natcast": ("Init.Data.Int.LemmasAux",),
    "natural-coprimality": ("Init.Data.Nat.Coprime",),
    "natural-induction-and-divisibility": ("Mathlib.Data.Nat.Init",),
    "natural-modulus": ("Init.Data.Nat.Mod",),
    # --- draw 3, 2026-08-29 (ADR-0615) ---------------------------------------
    # Re-measured: 18 modules now carry >= 10 fully screened, unused
    # candidates (down from draw 2's 22 -- four consumed by draw 2). The same
    # judgement rule applies ("every adjacency lands in the same partition"),
    # but this draw needed a SECOND screen the first two draws did not:
    # `*.Gcd`, `*.ModEq`, `*.Prime.*`, `*.Factorial.*`, `*.Choose.*`,
    # `*.Bitwise.*` are all adjacent to a v1 family that is development or
    # train (published, SEEN math), and putting a new family over the same
    # mathematics into held-out is the natural-division violation ADR-0615
    # documents -- so all six are excluded, exactly as draw 2 excluded them.
    #
    # That leaves three modules with NO existing-family adjacency at all:
    # `Init.Data.Nat.Basic`/`Init.Data.Nat.Lemmas` (plain Nat add/order
    # algebra), `Init.Data.Int.Lemmas` (the Int analogue). These are safe for
    # ANY partition on the adjacency test -- but R9 caught what adjacency
    # cannot: running the actual selection, natural-basic-arithmetic's first
    # 10 include `Nat.add_assoc`/`Nat.add_comm`, and integer-basic-arithmetic's
    # include `Int.add_assoc`/`Int.add_comm`/`Int.add_neg_cancel_right` --
    # ALREADY DECLARED in this kernel's own prelude, caught by R9's contaminated-
    # held-out check on the first attempt at this draw. "No nursery family
    # covers this math" and "this kernel has never proved it" are DIFFERENT
    # claims; basic algebra satisfies the first and fails the second, because
    # our own nat_prelude/int_prelude already cover it exhaustively. So these
    # two are fine for development/train (contamination there is a FEATURE --
    # fast closure -- not a defect) but cannot be the held-out slots.
    #
    # For held-out, two modules thread BOTH needles (checked, not assumed):
    # `Mathlib.Data.Int.Init`'s first 10 screened candidates alphabetically are
    # ALL `Int.div_*`/`Int.dvd_*` inequality lemmas, and combining
    # `Init.Data.Int.DivMod.Basic` (7, ediv/emod boundary cases) with
    # `Mathlib.Data.Int.Basic` (8, dvd/natCast/one gcd_emod lemma) reaches 15
    # screened, first 10 overwhelmingly div/dvd/ediv-boundary-and-natCast. Both
    # are PURELY the same mathematics as `integer-division`, which is ALREADY
    # held-out (v2) -- blind beside blind, the natural-induction-and-divisibility
    # precedent from draw 2 -- and R9-clean: zero of either family's first 10
    # collide with a kernel declaration.
    #
    # Module-path sort places these four as
    #   Init.Data.Int.DivMod.Basic  (integer-division-boundary-cases)
    #   Init.Data.Int.Lemmas        (integer-basic-arithmetic)
    #   Init.Data.Nat.Basic         (natural-basic-arithmetic)
    #   Mathlib.Data.Int.Init       (integer-division-inequalities)
    # so the mechanical cycle assigns held-out, development, train, held-out --
    # two NEW held-out families (R5), both R9-clean and matching their one
    # adjacency exactly (blind beside blind); the two development/train slots
    # are unconstrained novel math that happens to be mostly already-proved
    # (a `check-autogenesis-already-proved.py` finding, not a selection
    # criterion). No target outcome was consulted; this is the SET a lane
    # chose, the assignment is still the mechanical rule above.
    "integer-division-boundary-cases": (
        "Init.Data.Int.DivMod.Basic", "Mathlib.Data.Int.Basic"),
    "integer-basic-arithmetic": ("Init.Data.Int.Lemmas",),
    "natural-basic-arithmetic": ("Init.Data.Nat.Basic", "Init.Data.Nat.Lemmas"),
    "integer-division-inequalities": ("Mathlib.Data.Int.Init",),
    # --- draw 4, 2026-08-29 (ADR-0615) ---------------------------------------
    # Re-measured: 14 modules now carry >= 10 fully screened, unused
    # candidates (down from draw 3's 18 -- four consumed by draw 3). Twelve of
    # the fourteen are `*.Gcd`, `*.ModEq`, `*.Prime.*`, `*.Factorial.*`,
    # `*.Choose.*`, `*.Bitwise.*` -- draw 3's own exclusion list, unchanged:
    # each still sits over the SAME mathematics as a v1 family that is
    # development or train (natural-gcd/integer-gcd, natural-modular-
    # equivalence/integer-modular-equivalence, natural-primes, natural-
    # factorial, natural-binomial, natural-bitwise), so a held-out assignment
    # there is still the natural-division violation.
    #
    # That leaves exactly TWO modules with no existing-family adjacency:
    # `Init.Prelude` (35 screened, Nat order/comparison bridging -- the same
    # module draw 3's round 1 considered and dropped) and
    # `Mathlib.Data.Int.Order.Basic` (13, sign-based Int multiplication
    # inequalities). Screened, checked, NOT assumed: `Init.Prelude` is 30 of 35
    # ALREADY DECLARED in this kernel's own prelude (R9-contaminated, same
    # shape as draw 3's basic-arithmetic finding -- "no family covers this"
    # and "the kernel has never proved this" are different claims), and
    # `Mathlib.Data.Int.Order.Basic` is adjacent to the ALREADY-PARTITIONED
    # `integer-order` (Init.Data.Int.Order, development, v1) -- a held-out
    # assignment there would put fresh blind rows beside published Int-order
    # math. Both are fine for development/train (neither partition is blind,
    # so neither hazard applies there) but NEITHER may land held-out.
    #
    # So the two held-out slots need supply from BELOW the 10-candidate floor,
    # combined across several small modules the way draw 3 combined two Int
    # modules to reach `integer-division-boundary-cases`. Two candidates
    # thread every needle (checked, not assumed):
    #
    #   `Init.Data.Range.Polymorphic.{Int,Nat}Lemmas` (8 + 8 = 16) -- bounded
    #   INTERVAL INDUCTION principles (rcc/rco/roc/roo, left/right) over both
    #   fragments. No v1/v2 family covers interval induction; the nearest
    #   named family (`natural-induction-and-divisibility`, draw 2, held-out)
    #   is a DIFFERENT argument (divisibility-flavoured induction, module
    #   `Mathlib.Data.Nat.Init`) -- blind beside blind is fine per that same
    #   draw's precedent, and this is not even the same shape.
    #
    #   `Mathlib.Data.Int.{Order.Lemmas,Lemmas}` +
    #   `Mathlib.Algebra.Order.Group.Unbundled.Int` +
    #   `Init.Data.Dyadic.Basic` (3 + 7 + 2 + 1 = 13) -- every one an
    #   `Int.natAbs` identity. No existing family names natAbs at all.
    #
    # Both screened at 0/13 and 0/16 IN-ENV (R9-clean) and 0 glyphed (S6,
    # landed this draw -- see check-dispatchable-frontier.py). `Init.Prelude`
    # and `Mathlib.Data.Int.Order.Basic` are 30/35 and 0/13 IN-ENV
    # respectively, irrelevant to their dev/train slots.
    #
    # Primary-module ordering is chosen, not incidental: the module-path cycle
    # is mechanical, so the FAMILY SET is picked such that the two held-out-
    # safe families land at cycle positions 0 and 3 (mod 3 = held-out) and the
    # two contamination/adjacency-only-safe-for-dev/train families land at 1
    # and 2 (development, train). Verified by running assign_partitions():
    #
    #   Init.Data.Range.Polymorphic.IntLemmas  (range-induction)          held-out
    #   Init.Prelude                           (natural-order-bridging)   development
    #   Mathlib.Data.Int.Order.Basic           (integer-order-inequalities) train
    #   Mathlib.Data.Int.Order.Lemmas          (integer-absolute-value)   held-out
    #
    # No target outcome was consulted; the SET and the primary-module choice
    # within each tuple are a lane's judgement, the assignment is still the
    # mechanical rule above.
    "range-induction": (
        "Init.Data.Range.Polymorphic.IntLemmas",
        "Init.Data.Range.Polymorphic.NatLemmas"),
    "natural-order-bridging": ("Init.Prelude",),
    "integer-order-inequalities": ("Mathlib.Data.Int.Order.Basic",),
    "integer-absolute-value": (
        "Mathlib.Data.Int.Order.Lemmas",
        "Mathlib.Data.Int.Lemmas",
        "Mathlib.Algebra.Order.Group.Unbundled.Int",
        "Init.Data.Dyadic.Basic"),
    # --- draw 5, 2026-08-30 (ADR-0620) ---------------------------------------
    # SIX families: the largest draw the cycle permits on TWO held-out families
    # (`ceil(n/3)`, so n=6 is the last size before a third held-out slot opens).
    # That ceiling is the binding constraint of this draw and the reason it is
    # six rather than the nineteen the proposer reports as ready.
    #
    # THE MEASURED FINDING, which changes what a draw can be from here on.
    # Held-out-SAFE supply is nearly exhausted, while dispatchable supply is
    # abundant. Measured 2026-08-30 over all 94 modules carrying survivors:
    #
    #   * A module belongs to exactly ONE family -- `select`'s `module_family`
    #     is a dict -- so the 193 survivors still sitting in
    #     `Init.Data.Int.DivMod.Lemmas` are unreachable: `integer-division`
    #     owns that module. Owned modules cannot supply a new family at all.
    #   * Of the 19 modules the proposer calls ready, `Mathlib.Data.Nat.Log`
    #     and `Mathlib.Data.Nat.Sqrt` yield ZERO here (HELD_OUT_CONSTRUCTIONS),
    #     leaving 17 drawable.
    #   * Every one of those 17 is over mathematics an existing DEVELOPMENT or
    #     TRAIN family already publishes -- gcd, ModEq, Prime, factorial,
    #     choose, bitwise, fib, Int basics. Draws 2, 3 and 4 each excluded
    #     exactly this list from held-out and the reason is unchanged: a blind
    #     family over published mathematics is the natural-division violation
    #     ADR-0615 records. They are fine for development/train, where nothing
    #     is blind, and that is where all four dispatchable families below go.
    #   * So both held-out slots had to come from UN-OWNED modules below the
    #     10-candidate floor with no development/train adjacency, combined the
    #     way draw 3 and draw 4 combined theirs. The whole of that supply is
    #     24 propositions across eight modules. This draw takes 20 of them.
    #     **After this draw ~4 remain, so draw 6 cannot satisfy R5 from
    #     un-owned modules at all.** That is a real terminal condition and it
    #     is recorded in ADR-0620 rather than worked around here.
    #
    # THE TWO HELD-OUT FAMILIES. Both are R9-clean by measurement, not by
    # argument: 0 of 10 selected rows in either has a declaration of the same
    # Mathlib name in the kernel environment (the natural-binomial
    # contamination shape, ADR-0542, checked before preregistration).
    #
    #   integer-multiplicative-structure (held-out) -- `Init.Data.Int.Cooper`
    #   (3: dvd_of_mul_dvd, dvd_emod_add_of_dvd_add, dvd_mul_emod_add_of_dvd_
    #   mul_add) + `Mathlib.Algebra.Group.Int.Units` (7: mul_eq_one_iff_eq_one_
    #   or_neg_one and its relatives). One coherent question -- what a product
    #   lets you conclude about its integer factors. The Cooper rows are the
    #   same mathematics as `integer-division`, `integer-division-boundary-
    #   cases` and `integer-division-inequalities`, ALL THREE of which are
    #   already held-out: blind beside blind, the draw-2 precedent. No family
    #   names Int units at all.
    #
    #   descent-and-well-ordering (held-out) -- `Mathlib.Data.Int.LeastGreatest`
    #   (2: exists_least_of_bdd, exists_greatest_of_bdd) +
    #   `Mathlib.NumberTheory.SumFourSquares` (4) +
    #   `Mathlib.Order.Interval.Finset.Nat` (4: Nat.cauchy_induction and
    #   relatives). One coherent question again -- the extremal principle and
    #   the descent arguments built on it: well-ordering of a bounded integer
    #   set, forward-backward (Cauchy) induction, and Lagrange's four-square
    #   theorem with Euler's identity. `cauchy_induction` is adjacent to
    #   `natural-induction-and-divisibility` and `range-induction`, both
    #   held-out; the other two modules have no existing family.
    #
    #   `Mathlib.NumberTheory.{SumTwoSquares,PythagoreanTriples}` were
    #   available and are deliberately NOT taken: `Int.sq_ne_two_mod_four` is
    #   mod-4 arithmetic, adjacent to the TRAIN family
    #   `integer-modular-equivalence`, and it is not worth a mild leak to buy
    #   slack. Both held-out pools are therefore exactly 10 with none dropped.
    #
    # THE FOUR DISPATCHABLE FAMILIES are the four highest-yield drawable
    # modules (117, 82, 80, 87 survivors), all gcd/ModEq -- precisely the
    # mathematics draws 2-4 excluded from HELD-OUT and explicitly allowed in
    # development/train.
    #
    # PRIMARY-MODULE ORDERING IS CHOSEN, NOT INCIDENTAL, exactly as in draw 4:
    # the cycle is mechanical over `FAMILY_MODULES[f][0]` sorted lexicographically,
    # so the SET and each tuple's first element are picked to put the two
    # held-out-safe families at cycle positions 0 and 3. Verified by running
    # assign_partitions():
    #
    #   Init.Data.Int.Cooper            integer-multiplicative-structure  held-out
    #   Init.Data.Int.Gcd               integer-gcd-algorithm             development
    #   Init.Data.Nat.Gcd               natural-gcd-algorithm             train
    #   Mathlib.Data.Int.LeastGreatest  descent-and-well-ordering         held-out
    #   Mathlib.Data.Int.ModEq          integer-congruence-lemmas         development
    #   Mathlib.Data.Nat.ModEq          natural-congruence-lemmas         train
    #
    # No target outcome was consulted. R6 re-derives the assignment and R10
    # ties it to the preregistered one.
    "integer-multiplicative-structure": (
        "Init.Data.Int.Cooper",
        "Mathlib.Algebra.Group.Int.Units"),
    "integer-gcd-algorithm": ("Init.Data.Int.Gcd",),
    "natural-gcd-algorithm": ("Init.Data.Nat.Gcd",),
    "descent-and-well-ordering": (
        "Mathlib.Data.Int.LeastGreatest",
        "Mathlib.NumberTheory.SumFourSquares",
        "Mathlib.Order.Interval.Finset.Nat"),
    "integer-congruence-lemmas": ("Mathlib.Data.Int.ModEq",),
    "natural-congruence-lemmas": ("Mathlib.Data.Nat.ModEq",),
    # --- draw 7, 2026-08-30 (ADR-0654) ---------------------------------------
    # Draw 6 was declined twice. ADR-0645 declined it because no held-out-safe
    # family existed and named `Nat.dist` + `Nat.nth` as the unblock; ADR-0653
    # declined it again because the lane that declared `Nat.dist` also proved
    # five exact Mathlib mirror names, two of them inside the first ten a draw
    # takes, so R9 refuses `Mathlib.Data.Nat.Dist` for held-out forever.
    # `Nat.fermatNumber` has since landed (nat_prelude/fermat_number.rs), which
    # is the third unblock ADR-0653 measured and the one it called cheapest.
    #
    # THIS FAMILY SET IS NOT CHOSEN -- IT IS THE ONLY LAWFUL ONE. Enumerated
    # over all 2^11 subsets of the eleven un-owned modules at the PER_FAMILY
    # floor: a subset is lawful iff every cycle position congruent to 0 mod 3
    # is occupied by a held-out-safe module and R5's two-family minimum holds.
    # Exactly ONE subset survives, and it is this one. The reason it is forced:
    #
    #   * Held-out-safe means R9-clean in the first ten AND no published v1
    #     family over the same mathematics. Exactly two modules qualify --
    #     `Mathlib.Data.Nat.Nth` (R9 0/10, no family names an nth-selector) and
    #     `Mathlib.NumberTheory.Fermat` (R9 0/10, no family names Fermat
    #     numbers). The other nine are each adjacent to a PUBLISHED v1 family
    #     (natural-bitwise, natural-primes, natural-factorial, natural-gcd,
    #     natural-binomial, integer-gcd -- all development or train), or, for
    #     `Mathlib.Data.Nat.Dist`, contaminated at R9 2/10.
    #   * R5 needs two held-out families, so ceil(n/3) = 2 and n is 4, 5 or 6.
    #   * `Mathlib.NumberTheory.Fermat` sorts LAST of all eleven (NumberTheory
    #     > Data > Batteries/Init), so it lands at index n-1, which must be 3.
    #     Hence n = 4 and `Mathlib.Data.Nat.Nth` must be index 0, so nothing in
    #     the set may sort before it.
    #   * The only two ready modules sorting strictly between Nth and Fermat
    #     are the two Prime modules. They fill indices 1 and 2.
    #
    # THE TWO PRIME FAMILIES ARE LAWFUL PRECISELY BECAUSE THEY ARE NOT BLIND.
    # Draws 2-5 excluded `*.Prime.*` from HELD-OUT because v1 `natural-primes`
    # is development -- published, seen mathematics that lanes work. That
    # exclusion is a held-out exclusion only: ADR-0653 states the rule directly
    # for the Dist case ("perfectly good for development or train, where
    # nothing is blind and contamination is a fast-closure feature rather than
    # a defect"), and these two land at development and train.
    #
    # STATED LIMITATION, because it is the one thing here that is a judgement
    # rather than a measurement: two of `fermat-numbers`' ten blind rows
    # (`Nat.fermat_primeFactors_one_lt`, `Nat.pow_of_pow_add_prime`) mention
    # `Nat.Prime`, and this same draw dispatches twenty prime rows. That is
    # shared VOCABULARY, not a shared statement -- neither name appears in
    # either Prime pool, and a blind family must be allowed to use developed
    # tools or nothing could ever be held out. It is recorded rather than
    # waved past because it is the nearest thing to an adjacency in this draw.
    #
    # `Mathlib.Data.Nat.Dist` is NOT drawn, against ADR-0653's recommendation
    # to take it as development or train. It sorts BEFORE `Mathlib.Data.Nat.Nth`,
    # so including it either lands it at index 0 (held-out -- R9 refuses) or
    # pushes Fermat off index 3. The uniqueness enumeration above is what shows
    # this is forced rather than an oversight; Dist remains real supply for a
    # draw whose held-out slots come from elsewhere.
    "natural-nth-selector": ("Mathlib.Data.Nat.Nth",),
    "natural-prime-arithmetic": ("Mathlib.Data.Nat.Prime.Basic",),
    "natural-prime-characterizations": ("Mathlib.Data.Nat.Prime.Defs",),
    "fermat-numbers": ("Mathlib.NumberTheory.Fermat",),
    # --- draw 9, 2026-08-30 (ADR-0830) ---------------------------------------
    # ADR-0762 (draw 8, declined) measured the un-owned floor at 7 modules, all
    # either R9-contaminated (`Mathlib.Data.Nat.Dist`, `Mathlib.Data.Nat.
    # Factorial.Basic`, `Mathlib.Data.Int.GCD`) or topically adjacent to a
    # PUBLISHED development/train family (`natural-bitwise`, `natural-gcd`,
    # `natural-binomial`), and concluded draw 9 needs TWO NEW CONSTRUCTIONS
    # (`Nat.nthRoot` clean, a second unidentified) before any held-out-safe
    # family exists. Re-measured here, byte-identical: `env=2383`, same seven
    # modules, same contamination. That half of ADR-0762 still holds.
    #
    # What ADR-0762 did NOT check is whether several modules BELOW the
    # PER_FAMILY floor, each already admissible today (no new construction),
    # combine into >= 10 rows the way draws 3, 4 and 5 built
    # `integer-division-boundary-cases`, `range-induction` and
    # `integer-absolute-value`. They do. Two such combinations exist, checked
    # against `scripts/check-holdout-adjacency.py`'s real `screen_family` (R11)
    # rather than by inspection, and BOTH are R9/R11-clean with zero new
    # kernel declarations:
    #
    #   integer-elementary-identities (held-out) -- `Init.Data.Int.Basic` (6:
    #   `Int.ofNat`/`natCast` identities), `Init.Data.Int.Compare` (1: a strict
    #   order trichotomy), `Init.Data.Int.Linear` (2: `omega`-adjacent not-le/
    #   not-lt rewrites), `Mathlib.Data.Int.DivMod` (2: `emod`/`ediv`
    #   identities) -- 11 rows. Every constant CONST_RE extracts from these
    #   eleven statements is typeclass/operator PLUMBING under
    #   `check-holdout-adjacency.py`'s own `is_syntax` filter (`Int.ofNat`,
    #   `LE.le`, `HMod.hMod`, ... -- explicitly listed or pattern-matched), so
    #   `subject_constants` is EMPTY and both the topic and vocabulary signals
    #   are vacuously clean. Blind beside blind besides: the natCast rows sit
    #   next to the EXISTING held-out `integer-natcast` (draw 2) and the DivMod
    #   rows next to `integer-division`/`integer-division-boundary-cases`
    #   (held-out, v2/draw 3) -- the draw-2 precedent, not a new judgment call.
    #
    #   natural-elementary-bounds (held-out) -- ten small leftover Nat modules,
    #   none individually near the floor, each a basic order/bound/successor
    #   identity no existing family's topic or vocabulary reaches:
    #   `Mathlib.Data.Nat.SuccPred` (2), `Batteries.Data.Nat.Lemmas` (2),
    #   `Mathlib.Data.Nat.Basic` (1), `Mathlib.Data.Nat.Order.Lemmas` (1),
    #   `Init.SimpLemmas` (1), `Init.Data.Nat.Simproc` (1),
    #   `Mathlib.Algebra.Order.Group.Nat` (1), `Mathlib.Order.Monotone.Basic`
    #   (1), `Mathlib.Data.Nat.Sqrt` (1 -- the one row NOT excluded by
    #   `HELD_OUT_CONSTRUCTIONS`, about squeezing between consecutive squares
    #   rather than about `Nat.sqrt` itself), `Mathlib.Data.Nat.Digits.Defs`
    #   (1) -- 12 rows, of which `select()` keeps the alphabetically-first ten.
    #   This one is honestly a grab-bag rather than one clean subject (unlike
    #   `integer-absolute-value`'s four modules, all about `natAbs`) -- the
    #   remaining un-owned supply below the floor is this thin, matching
    #   ADR-0762's own count. `Init.Core`'s single survivor (`Nat.add_zero`)
    #   was deliberately EXCLUDED: it is already IN-ENV (R9-contaminated), the
    #   one leftover row this draw could not use for held-out.
    #
    # Both were verified with the real `select()` + `guard()` (R1-R11) in
    # memory before this edit, not by inspection: `GUARD PASSED`, both new
    # held-out pools 0/10 against the kernel environment, `_adjacency_screen`
    # (R11) raised nothing.
    #
    # THE TWO DISPATCHABLE SLOTS use ADR-0762's own stated ready supply rather
    # than inventing new adjacency risk: `natural-bitwise-basics`
    # (`Init.Data.Nat.Bitwise.Lemmas`, 33 rows, R9 0/10) and `natural-distance`
    # (`Mathlib.Data.Nat.Dist`, 18 rows, R9 2/10 -- `dist_comm`/`dist_self`,
    # harmless outside held-out) -- exactly the module ADR-0653's closing
    # recommendation named as "real supply for development or train" once a
    # draw's cycle positions allow it. Both duplicate an existing v1
    # development/train family's TOPIC (`natural-bitwise`, and Dist is
    # `natural-distance`'s own namesake) -- accepted for the same reason draw 7
    # accepted `natural-prime-arithmetic`/`natural-prime-characterizations`
    # beside v1 `natural-primes`: contamination in a PUBLISHED partition is a
    # fast-closure feature, not the ADR-0542 leak, which only threatens blind
    # rows.
    #
    # PRIMARY-MODULE ORDERING IS CHOSEN, as in every prior draw: the four
    # primaries sort `Init.Data.Int.Basic` < `Init.Data.Nat.Bitwise.Lemmas` <
    # `Mathlib.Data.Nat.Dist` < `Mathlib.Data.Nat.SuccPred`, so the mechanical
    # held-out/development/train/held-out cycle lands
    #
    #   integer-elementary-identities    held-out
    #   natural-bitwise-basics           development
    #   natural-distance                 train
    #   natural-elementary-bounds        held-out
    #
    # exactly the 2-held-out/2-dispatchable split R4/R5 require. No target
    # outcome was consulted; the SET and each tuple's primary module are a
    # lane's judgment under measured scarcity, the assignment is the mechanical
    # rule above. Full measurements: docs/plan/notes/nursery-refill-draw-9.md.
    "integer-elementary-identities": (
        "Init.Data.Int.Basic", "Init.Data.Int.Compare",
        "Init.Data.Int.Linear", "Mathlib.Data.Int.DivMod"),
    "natural-bitwise-basics": ("Init.Data.Nat.Bitwise.Lemmas",),
    "natural-distance": ("Mathlib.Data.Nat.Dist",),
    "natural-elementary-bounds": (
        "Mathlib.Data.Nat.SuccPred", "Batteries.Data.Nat.Lemmas",
        "Mathlib.Data.Nat.Basic", "Mathlib.Data.Nat.Order.Lemmas",
        "Init.SimpLemmas", "Init.Data.Nat.Simproc",
        "Mathlib.Algebra.Order.Group.Nat", "Mathlib.Order.Monotone.Basic",
        "Mathlib.Data.Nat.Sqrt", "Mathlib.Data.Nat.Digits.Defs"),
    # --- draw 11, 2026-08-30 (ADR-0925) ---------------------------------------
    # ADR-0910 declared `Nat.nthRoot`/`Squarefree` construction-only, predicting
    # this would open exactly two new held-out-safe un-owned modules once the
    # environment snapshot is refreshed. Re-screened here after a fresh release
    # build: both DO open (`Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas`,
    # 13 rows R9 0/10; `Mathlib.Data.Nat.Squarefree`, 11 rows R9 0/10), exactly
    # as measured. But R11 -- the adjacency screen, landed as CODE only today
    # per its own module docstring -- REFUSES `Squarefree` for held-out: 6 of
    # its drawn 10 rows are about `Nat.Coprime`/`Nat.Prime`/`Nat.gcd`, over the
    # vocabulary allowance of 5. This is a stricter, mechanised version of the
    # SAME judgment draw 8's note already made by hand
    # (docs/plan/notes/383-nursery-draw-8.md, "Eight of ten mention Nat.Prime,
    # Nat.Coprime or Nat.gcd... a different thing"). ADR-0910 did not run this
    # simulation, so this is new information: the two-construction plan alone
    # does not clear guard(). `Squarefree` is placed in `train` below instead
    # (R11 does not screen non-held-out partitions), which is not a loss --
    # ADR-0653's contamination-is-a-feature rule applies outside held-out.
    #
    # The substitute second held-out family is a below-floor combination in
    # the shape ADR-0900 already found and left unresolved: `Mathlib.Data.Nat.
    # {Size,Bits}` combined (12 rows, R9 clean). R11 permits it as a
    # DISCLOSURE rather than a refusal (topic 0, vocabulary 0/10 -- this
    # kernel's own extensive `Nat.bit`/`Nat.testBit`/`Nat.bitwise`/`Nat.size`
    # development shares no TOPIC or VOCABULARY with the drawn statements'
    # constants, it just shares the SUBJECT). `natural-nth-root` carries the
    # same kind of disclosure (stems `root`/`nth`/`nthroot` hit `CReal.
    # ivt_exact_root*`, `Complex.root_of_unity*`, `Nat.nth`/`nthAux` -- all
    # unrelated mathematics sharing a word, the same false-positive class
    # `natural-square-root`'s own accepted review names). Both reviewed by
    # hand and recorded in `holdout-adjacency-review-v1.json` (name-by-name,
    # not by count) before drawing; see that file for what was compared.
    #
    # TWO CAVEATS RECORDED, NOT RESOLVED, per docs/plan/notes/383-nursery-draw-8.md
    # and this draw's own status note:
    #   * `Nat.nthRoot_zero_left : forall a, Nat.nthRoot 0 a = 1` is drawn in
    #     `natural-nth-root`'s first ten and is very likely `Eq.refl` the
    #     instant ADR-0910's construction exists (its `n = 0` branch returns
    #     `1` unconditionally, independent of `a`), because the recursion
    #     branches on the LITERAL-zero first argument and never touches the
    #     second. `check-holdout-closed-evaluation.py`'s classifier requires a
    #     binder-free statement and this one has `forall (a : Nat)`, so it is
    #     invisible to that gate by the gate's own documented design -- this is
    #     the EXACT example its module docstring uses. Not excluded here
    #     (no lawful mechanism in this generator's scope removes one row from
    #     an alphabetically-drawn pool without an ADR-0542 amendment after the
    #     fact, and amending before a row is even preregistered has no defined
    #     meaning) -- flagged so a dispatch lane does not read a trivial
    #     acceptance of this ONE row as evidence of producer capability.
    #     `Nat.nthRoot_one_right : n.nthRoot 1 = 1` is NOT judged free by the
    #     same mechanism: `Nat.pow` recurses on its exponent, which is
    #     symbolic `n` here, so the search does not obviously reduce without
    #     real content (an argument close to `Nat.one_pow`).
    #   * `Nat.nthRoot.lt_pow_go_succ_aux` is drawn in the same ten and is an
    #     honest restatement of MATHLIB'S Newton-iteration auxiliary
    #     (`b <> 0 -> a < ((a / b^n + n*b)/(n+1) + 1)^(n+1)`), which our
    #     fuel-bounded linear-search construction has no counterpart to. It
    #     may be unprovable here for reasons unrelated to genuine mathematical
    #     difficulty; judge before dispatch, not after.
    #
    # A THIRD caveat, measured (not merely reasoned about) after this comment
    # was first drafted: `scripts/check-holdout-closed-evaluation.py` reports
    # `verdict=FAIL` against `natural-bit-decode` -- 2 of its drawn 10 rows,
    # `Nat.bit_false_zero : Nat.bit false 0 = 0` and `Nat.size_one : Nat.size
    # 1 = 1`, are BINDER-FREE ground equations decided by reduction over
    # `Nat.bit`/`Nat.size`, which this kernel already declared natively long
    # before this draw (unrelated to ADR-0910's constructions). Confirmed the
    # baseline (this file's committed state, no draw-11 families) passes this
    # gate at `violations=0`, so the 2 violations are introduced by drawing
    # this family, not inherited.
    #
    # An exhaustive substitute search (every below-floor un-owned module not
    # already excluded above, all pairs and triples, screened for R9 +
    # closed-evaluation + R11 topic/vocabulary together) found ZERO
    # alternatives -- reproducing ADR-0900's own conclusion that Bits+Size is
    # the only mechanically-clean-on-every-OTHER-axis below-floor combination.
    # `natural-nth-root` alone cannot satisfy R5's two-held-out-family
    # minimum, so the choice is exactly the one ADR-0695's docstring already
    # names for this shape: "accept and record the spend, but do not read
    # closed-eval 0 as nothing is spent" (383-nursery-draw-8.md, written about
    # `Nat.nthRoot_zero_left`, applies verbatim here). Accepted on that
    # precedent, same as `fermat-numbers` (3 of 10 closed, drawn before this
    # checker existed, repaired afterward by ADR-0542 amendment) -- the
    # difference here is the repair is flagged BEFORE preregistration rather
    # than discovered after. A future lane may reasonably amend
    # `Nat.bit_false_zero`/`Nat.size_one` (or the whole family) out of
    # held-out via ADR-0542 once dispatch reaches them; this lane does not,
    # per its own generator's rule that amending before a row is even
    # preregistered has no defined meaning.
    "natural-nth-root": ("Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas",),
    "natural-gcd-and-bitwise-basics": (
        "Mathlib.Data.Int.GCD", "Mathlib.Data.Nat.GCD.Basic",
        "Batteries.Data.Nat.Bitwise.Lemmas"),
    "natural-factorial-choose-and-squarefree": (
        "Mathlib.Data.Nat.Choose.Basic", "Mathlib.Data.Nat.Factorial.Basic",
        "Mathlib.Data.Nat.Squarefree"),
    "natural-bit-decode": ("Mathlib.Data.Nat.Size", "Mathlib.Data.Nat.Bits"),
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
    "integer-natcast": ("kernel-induction", "kernel-library-application"),
    "natural-coprimality": ("divisibility-library-application", "kernel-induction"),
    "natural-induction-and-divisibility": (
        "divisibility-library-application", "kernel-induction"),
    "natural-modulus": ("kernel-induction", "kernel-library-application"),
    "integer-basic-arithmetic": ("kernel-induction", "kernel-library-application"),
    "natural-basic-arithmetic": ("kernel-induction", "kernel-library-application"),
    "integer-division-inequalities": (
        "kernel-library-application", "modular-arithmetic-reconstruction"),
    "integer-division-boundary-cases": (
        "kernel-library-application", "modular-arithmetic-reconstruction"),
    "range-induction": ("kernel-induction", "kernel-library-application"),
    "natural-order-bridging": ("kernel-induction", "kernel-library-application"),
    "integer-order-inequalities": ("kernel-induction", "kernel-library-application"),
    "integer-absolute-value": ("kernel-induction", "kernel-library-application"),
    # --- draw 5, 2026-08-30 ---------------------------------------------------
    "integer-multiplicative-structure": (
        "divisibility-library-application", "kernel-library-application"),
    "integer-gcd-algorithm": ("divisibility-library-application", "kernel-induction"),
    "natural-gcd-algorithm": ("divisibility-library-application", "kernel-induction"),
    "descent-and-well-ordering": ("kernel-induction", "kernel-library-application"),
    "integer-congruence-lemmas": (
        "kernel-library-application", "modular-arithmetic-reconstruction"),
    "natural-congruence-lemmas": (
        "kernel-library-application", "modular-arithmetic-reconstruction"),
    # --- draw 7, 2026-08-30 (ADR-0654) ---------------------------------------
    # `Nat.nth p n` is a well-founded selector over a decidable predicate and
    # its rows are monotonicity/indexing facts, so induction plus the recursive
    # reconstruction route. `Nat.fermatNumber n = 2^(2^n) + 1` is likewise
    # recursive, and its rows are coprimality and ordering facts.
    "natural-nth-selector": ("kernel-induction", "recursive-function-reconstruction"),
    "natural-prime-arithmetic": (
        "divisibility-library-application", "kernel-library-application"),
    "natural-prime-characterizations": (
        "divisibility-library-application", "kernel-induction"),
    "fermat-numbers": (
        "divisibility-library-application", "recursive-function-reconstruction"),
    # --- draw 9, 2026-08-30 (ADR-0830) ---------------------------------------
    "integer-elementary-identities": (
        "kernel-library-application", "modular-arithmetic-reconstruction"),
    "natural-bitwise-basics": ("kernel-induction", "kernel-library-application"),
    "natural-distance": ("kernel-induction", "kernel-library-application"),
    "natural-elementary-bounds": ("kernel-induction", "kernel-library-application"),
    # --- draw 11, 2026-08-30 (ADR-0925) ---------------------------------------
    "natural-nth-root": ("kernel-induction", "recursive-function-reconstruction"),
    "natural-gcd-and-bitwise-basics": (
        "divisibility-library-application", "kernel-library-application"),
    "natural-factorial-choose-and-squarefree": (
        "divisibility-library-application", "kernel-induction"),
    "natural-bit-decode": ("kernel-induction", "kernel-library-application"),
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
#
# ADR-0616. That last sentence is the exit ADR-0615 named, and it did not work,
# because R3 compared `len(entries)` -- a FLAT COUNT of the extension -- against
# 214. Re-attesting a row changed nothing: 197 of 200 rows carried the real-Lean
# round trip and all 200 still counted as scaffolding, so the only way past the
# ceiling was the raise the ADR rejected. The comparison now says what the rule
# says. `attested_cohort` is every row that HAS been through the round trip and
# was accepted (v1's 214, plus the extension's accepted rows);
# `unattested_cohort` is every extension row that has not. A draw's new rows land
# in `unattested` by construction -- `surface_validation()` puts an id no run has
# covered there -- so the guard still binds on a draw and is still cleared only
# by running Lean, which is exactly the cadence ADR-0615 wanted.
#
# `not_elaborable` rows count on the UNATTESTED side deliberately. They have been
# through the round trip and Lean REFUSED them, so they are preregistered strings
# that are not propositions: strictly worse than a row nobody has checked, and
# they must never buy headroom.
V1_POLICY_RANGE = (100, 300)


def attested_cohort(v1_evaluation: list[Any], validation: dict[str, Any]) -> int:
    """Rows that went through the real-Lean round trip and were ACCEPTED.

    nursery-v1's 214 were accepted as a block: its source catalog records
    `observed_result: accepted-214-proof-free-axiom-types` against a pinned
    module whose sha256 still matches on disk. The extension's are accepted per
    row, by the same method, with a mandatory negative control v1's run did not
    carry -- see ADR-0616.
    """
    return len(v1_evaluation) + len(validation.get("attested", []))


def unattested_cohort(validation: dict[str, Any]) -> int:
    """Extension rows carrying no ACCEPTED round trip.

    Both buckets count: `unattested` (no run has read this row) and
    `not_elaborable` (a run read it and Lean refused it). The second is worse
    than the first, so folding them together is the conservative direction.
    """
    return (len(validation.get("unattested", []))
            + len(validation.get("not_elaborable", [])))


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

    **It freezes `preregistered_family_partitions`, not `family_partitions`.**
    Those are the same dict until an ADR-0542 amendment moves a family, and
    keeping them separate is what makes the amendment enforceable. The digest
    stops a hand edit that FORGETS to update it; it cannot stop a deliberate
    edit that recomputes it, and before this split there was no immovable
    reference to check an effective partition against -- the manifest was its
    own authority, so moving `natural-divisibility` out of held-out with no
    amendment record anywhere would have regenerated clean. See R10.
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


def preregistered_freeze() -> dict[str, str]:
    """What each earlier draw PREREGISTERED, before any ADR-0542 amendment.

    REQUIRED once the manifest exists, with no fall back to
    `family_partitions`: falling back would let a manifest that dropped the key
    make its own amended partitions the preregistered truth, which is exactly
    the hole R10 closes.
    """
    if not EXTENSION.is_file():
        return {}
    manifest = load_json(EXTENSION)
    partitions = manifest.get("preregistered_family_partitions")
    if not isinstance(partitions, dict) or not partitions:
        raise RefillError(
            f"{EXTENSION.name} carries no preregistered_family_partitions, so "
            f"there is nothing to check its effective partitions against")
    return dict(partitions)


def amendments() -> dict[str, dict[str, Any]]:
    """The ADR-0542 ledger, keyed by family.

    Required, not optional: an absent or unreadable ledger means a spend could
    not be checked, and a guard whose subject has vanished reports the same
    "no violations" as a guard that works.
    """
    if not SPLIT_POLICY.is_file():
        raise RefillError(
            f"the ADR-0542 amendment ledger is missing at {SPLIT_POLICY}; "
            f"without it no partition move can be checked against a recorded "
            f"breach")
    ledger = load_json(SPLIT_POLICY)
    recorded = ledger.get("amendments")
    if not isinstance(recorded, list):
        raise RefillError(f"{SPLIT_POLICY.name} carries no amendments list")
    by_family: dict[str, dict[str, Any]] = {}
    for item in recorded:
        if not isinstance(item, dict) or "family" not in item:
            raise RefillError(f"{SPLIT_POLICY.name} has a malformed amendment")
        family = item["family"]
        if family in by_family:
            raise RefillError(
                f"{SPLIT_POLICY.name} amends {family!r} twice; a held-out spend "
                f"is irreversible, so a second move has no defined `from`")
        by_family[family] = item
    return by_family


def _with_cycle(frozen: dict[str, str]) -> dict[str, str]:
    """Frozen families keep their partition; the cycle runs over the NEW ones.

    The cycle restarts at `held-out` for each draw's new family set, which is
    what makes R5's "at least two new held-out families" reachable at four
    families. Continuing one global cycle across draws would not.
    """
    assignment = {f: p for f, p in frozen.items() if f in FAMILY_MODULES}
    fresh = sorted((f for f in FAMILY_MODULES if f not in assignment),
                   key=lambda f: FAMILY_MODULES[f][0])
    for index, family in enumerate(fresh):
        assignment[family] = PARTITION_CYCLE[index % len(PARTITION_CYCLE)]
    return assignment


def preregistered_assignment() -> dict[str, str]:
    """What each draw preregistered, plus the cycle for this draw's new rows.

    No amendment touches this: what a draw preregistered is a historical fact,
    and it is the immovable reference R10 checks the effective assignment
    against.
    """
    return _with_cycle(preregistered_freeze())


def assign_partitions() -> dict[str, str]:
    """The EFFECTIVE assignment: the manifest's own, plus ADR-0542 amendments.

    The ledger is applied here so that recording an amendment and regenerating
    is enough to move the family -- and applying one twice is a no-op, because
    the regenerated manifest already carries `to`. It is applied ON TOP of the
    manifest rather than on top of `preregistered_assignment()`, which matters:
    the latter would make R10's no-amendment branch unreachable, since the only
    way for the two assignments to differ would be a ledger row. R10 has to be
    able to see a manifest someone moved by hand.
    """
    assignment = _with_cycle(frozen_partitions())
    for family, amendment in amendments().items():
        if family in assignment:
            assignment[family] = amendment["to"]
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


def derive_vocabulary_content(
        env: set[str], inventory: dict[str, dict[str, Any]],
        catalog: dict[str, Any],
        facts: dict[str, dict[str, Any]]) -> dict[str, Any]:
    """The two derived fields this script needs, re-derived independently.

    This script does NOT own `mathlib-statable-vocabulary-v1.json`;
    `gen-autogenesis-statable-vocabulary.py` does (ADR-0652). It used to
    build the WHOLE document and write it, which deleted the owner's
    `bridge_provenance` and `row_digest` -- ADR-0631's per-constant
    classification -- on every draw, while exiting 0.

    What survives here is the derivation, which is genuinely independent:
    constants come from the pinned inventory's `type_repr` here and from
    `mathlib-statement-constants-v1.json` there. It is used to CROSS-CHECK
    the owned artifact in `read_vocabulary`, never to overwrite it.
    """
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
    return {"bridge": sorted(bridge), "settled": rows}


def read_vocabulary(env: set[str], inventory: dict[str, dict[str, Any]],
                    catalog: dict[str, Any],
                    facts: dict[str, dict[str, Any]]) -> dict[str, Any]:
    """Load the OWNED vocabulary and confirm it agrees with our derivation.

    Reading rather than writing is the whole point: one producer per key.
    The agreement check is what a second writer used to buy us by accident
    -- two independent derivations of `bridge` and `settled` -- kept
    deliberately, and made to FAIL rather than to overwrite.
    """
    vocabulary = load_json(VOCABULARY)
    derived = derive_vocabulary_content(env, inventory, catalog, facts)
    for field in ("bridge", "settled"):
        on_disk = vocabulary.get(field)
        if on_disk != derived[field]:
            raise RefillError(
                f"{VOCABULARY.name}: `{field}` disagrees with this script's "
                f"independent derivation ({len(derived[field])} derived, "
                f"{len(on_disk) if isinstance(on_disk, list) else 'absent'} "
                f"on disk). This script does not own that file and will not "
                f"rewrite it -- regenerate with "
                f"scripts/gen-autogenesis-statable-vocabulary.py --write, "
                f"which owns it and emits bridge_provenance and row_digest "
                f"as well.")
    return vocabulary


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
          env: set[str], validation: dict[str, Any]) -> None:
    """Every rule the refill claims to respect, asserted rather than described.

    `validation` is the surface grade the emitted manifest will carry, computed
    from the same entries. R3 needs it, and it is a REQUIRED argument rather
    than something this function re-derives: a default would have to mean either
    "assume attested" (a guard that cannot fail) or "assume unattested" (a guard
    that refuses the committed manifest), and both are wrong answers to a
    question the caller already knows.
    """
    partitions = assign_partitions()
    frozen = frozen_partitions()

    # R10 -- an effective partition that differs from the preregistered one is
    # a SPEND, and it is legible only if the ADR-0542 ledger records it.
    #
    # Before this rule the extension manifest was its own authority: R8 froze
    # against `family_partitions`, so a hand edit that moved a family AND
    # recomputed `extension_sha256` regenerated perfectly clean, with no
    # amendment anywhere. The digest catches a careless edit, never a
    # deliberate one. Measured 2026-08-30 while amending `natural-divisibility`
    # -- the move the gate's own message demands -- which is when it became
    # clear the ledger and this manifest had no link at all.
    #
    # It reads the two dicts the MANIFEST records, not the two this module
    # recomputes. That is not a detail: `assign_partitions()` applies the ledger
    # last, so a recomputed comparison would make both the no-amendment branch
    # and the destination branch unreachable -- the assignment could differ from
    # the preregistered one only BY a ledger row, and would then agree with it
    # by construction. A guard that cannot fail is worse than no guard, and two
    # drafts of this rule had that shape before it was measured.
    #
    # It also runs BEFORE R6. R6 compares entries against the effective
    # assignment; if the assignment itself is illegitimate, saying so is the
    # more informative failure, and otherwise a bogus ledger row is reported as
    # an entry disagreement.
    ledger = amendments()
    preregistered = preregistered_freeze()
    for family, now in sorted(frozen.items()):
        was = preregistered.get(family)
        if was is None:
            raise RefillError(
                f"R10 {family!r} has an effective partition {now!r} and no "
                f"preregistered one, so nothing can say whether it moved")
        amendment = ledger.get(family)
        if amendment is None:
            if now != was:
                raise RefillError(
                    f"R10 {family!r} was preregistered {was!r} and the manifest "
                    f"assigns {now!r}, with no ADR-0542 amendment recording the "
                    f"spend; record the breach in {SPLIT_POLICY.name} or restore "
                    f"the preregistered partition")
            continue
        if amendment.get("from") != was:
            raise RefillError(
                f"R10 the {family!r} amendment records from="
                f"{amendment.get('from')!r} but the family was preregistered "
                f"{was!r}; the ledger does not describe this manifest")
        if amendment.get("to") != now:
            raise RefillError(
                f"R10 the {family!r} amendment records to="
                f"{amendment.get('to')!r} but the manifest assigns {now!r}")
        if now == "held-out":
            raise RefillError(
                f"R10 amended family {family!r} is assigned to held-out; a "
                f"family whose blind-evaluation value was spent cannot be "
                f"recycled into the blind population")

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

    # R3 -- the ceiling, applied PER COHORT (ADR-0615) and counted by
    # ATTESTATION rather than by manifest membership (ADR-0616). v1's own
    # `policy.evaluation_fact_count` governs v1, and is asserted here rather
    # than assumed; the UNATTESTED population may not outweigh the attested one.
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
    attested = attested_cohort(v1_evaluation, validation)
    unattested = unattested_cohort(validation)
    if unattested > attested:
        raise RefillError(
            f"R3 the unattested cohort would be {unattested} rows against "
            f"{attested} attested, so scaffolding would outweigh the "
            f"population that carries the real-Lean round trip. Attest rather "
            f"than raise it: scripts/attest-nursery-surface.py then "
            f"--ingest-surface-attestation")

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

    # R8 -- a family an earlier draw preregistered keeps EXISTING.
    #
    # R8 used to also refuse a MOVED partition, by comparing each entry against
    # `frozen`. That check is now R10's, and the split is not cosmetic: an
    # amended family's effective partition legitimately differs from its
    # preregistered one, so the old comparison would have refused exactly the
    # repair ADR-0542 prescribes. Re-aiming R8 at `preregistered_assignment()`
    # instead was tried and is WORSE THAN USELESS -- that function derives from
    # `frozen` itself, so the two can never disagree and the guard cannot fail.
    # R6 ties each entry to the effective assignment; R10 ties the effective
    # assignment to the preregistered one; together they cover what R8 covered.
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

    # R11 -- ADR-0653's adjacency rule, which was PROSE until 2026-08-30.
    #
    # R9 above compares a candidate's Mathlib NAME against the environment.
    # ADR-0762 measured what that leaves open: a draw putting
    # `Init.Data.Nat.Bitwise.Lemmas` and `Mathlib.Data.Nat.GCD.Basic` into
    # held-out -- beside `natural-bitwise` and `natural-gcd`, both DEVELOPMENT
    # and both worked by lanes that week -- is R9-clean 0/10 on each, and the
    # whole guard returned `GUARD PASSED -- 340 entries, 120 held-out rows`.
    # The rule that forbids it existed only in an ADR, so a lane could author
    # the ADR-0542 breach deliberately and see green.
    #
    # The screen lives in its own script because it is worth running on its own
    # (`scripts/check-holdout-adjacency.py`, registered in both aggregate
    # gates) and because it needs the fact ledger to recover v1's Mathlib names.
    # It is imported rather than reimplemented, and an import failure is a
    # REFUSAL: a draw that cannot run the adjacency screen has not passed it.
    #
    # R12 -- ADR-0695's closed-evaluation rule, applied at DRAW TIME rather
    # than found by the standing gate in a later audit. ADR-0695 recorded the
    # `fermat-numbers` spend and wrote in prose that "the next unblocking
    # constant should be screened for this before it is declared, not after."
    # Draw 11 repeated it anyway: `natural-bit-decode` preregistered held-out
    # on 2026-08-30 even though `Nat.bit false 0 = 0` and `Nat.size 1 = 1`
    # were already decided by reduction over `Nat.bit` (2026-08-28) and
    # `Nat.size` (2026-08-24), both admitted days before the draw (ADR-0950).
    # Prose did not hold the second time either, so this is a guard now.
    if new_entries:
        _adjacency_screen(new_entries, env)
        _closed_evaluation_screen(new_entries, env)


def _adjacency_screen(new_entries: list[dict[str, Any]], env: set[str]) -> None:
    """R11's body. Separate so the import failure has one place to be reported."""
    try:
        spec = importlib.util.spec_from_file_location(
            "_holdout_adjacency", ROOT / "scripts/check-holdout-adjacency.py")
        adjacency = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(adjacency)
    except Exception as exc:  # noqa: BLE001 -- any failure means the screen did not run
        raise RefillError(
            "R11 the adjacency screen (scripts/check-holdout-adjacency.py) "
            f"could not be loaded, so ADR-0653's rule was not applied: {exc}")

    new_rows: dict[str, list[Any]] = {}
    new_partition: dict[str, str] = {}
    for entry in new_entries:
        new_partition[entry["family"]] = entry["partition"]
        new_rows.setdefault(entry["family"], []).append(
            adjacency.Row(entry["source_name"], entry["module"],
                          frozenset(entry["constants"])))
    # `resolve_families` needs only these two from this module, and passing a
    # namespace rather than `sys.modules[__name__]` keeps it working when this
    # file is itself loaded by path (which every in-memory draw probe does --
    # `module_from_spec` does NOT register in `sys.modules`).
    existing_rows, existing_partition, _counts = adjacency.resolve_families(
        types.SimpleNamespace(read_inventory=read_inventory, CONST_RE=CONST_RE))
    # A family this draw ADDS cannot also be part of what is already published;
    # scoring it against itself would make the screen vacuous, and
    # `screen_family` raises rather than allow it.
    for family in new_rows:
        existing_rows.pop(family, None)
    try:
        adjacency.assert_draw_lawful(new_rows, new_partition, existing_rows,
                                     existing_partition, env=env)
    except adjacency.RefusalError as exc:
        raise RefillError(str(exc))


def _closed_evaluation_screen(new_entries: list[dict[str, Any]], env: set[str]) -> None:
    """R12's body. ADR-0695/ADR-0950: a NEW held-out row already decided by
    reduction is not blind, whatever anyone has or has not proved about it.

    Scoped to rows THIS DRAW ADDS, matching R9 and R11 -- an earlier draw's
    rows are frozen, and repairing one already drawn is an ADR-0542 amendment,
    not something a later invocation of this generator can silently undo.

    Imports the standing gate (`check-holdout-closed-evaluation.py`) by path
    rather than reimplementing its classifier, mirroring `_adjacency_screen`'s
    pattern for `check-holdout-adjacency.py`: a failed import is a REFUSAL,
    not a silent skip, so a draw that cannot run this screen has not passed
    it either.
    """
    try:
        spec = importlib.util.spec_from_file_location(
            "_holdout_closed_evaluation",
            ROOT / "scripts/check-holdout-closed-evaluation.py")
        classifier = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(classifier)
    except Exception as exc:  # noqa: BLE001 -- any failure means the screen did not run
        raise RefillError(
            "R12 the closed-evaluation screen (scripts/"
            "check-holdout-closed-evaluation.py) could not be loaded, so "
            f"ADR-0695's rule was not applied: {exc}")

    violations = []
    for e in new_entries:
        if e.get("partition") != "held-out":
            continue
        statement = e.get("statement")
        if not statement or not classifier.is_closed_evaluation(statement):
            continue
        names = classifier.constants(statement)
        undeclared = [n for n in names
                      if n not in env and not classifier.source_declares(n)]
        if undeclared:
            continue
        violations.append((e["fact_id"], e.get("family", "?"), statement))
    if violations:
        raise RefillError(
            f"R12 {len(violations)} held-out candidate(s) are closed "
            f"evaluations already decided by reduction over constants this "
            f"kernel already declares, so they are not blind: "
            f"{violations[:5]}. Exclude these rows before preregistering; "
            f"see ADR-0695 and ADR-0950.")


def stored_surface_validation() -> dict[str, Any]:
    """What the manifest already records about its own surface grade."""
    if not EXTENSION.is_file():
        return {}
    got = load_json(EXTENSION).get("surface_validation")
    return got if isinstance(got, dict) else {}


def stored_cross_population_exemptions() -> list[dict[str, Any]]:
    """Carry `cross_population_component_split_exemptions` across a regen.

    ADR-0855 introduced this key directly on the committed manifest, by hand,
    reviewed against a live union-component sweep -- it is authored, not
    derived, so `build_extension` has no formula to reproduce it. Without this
    function a plain (non-`--check`) regeneration silently drops the key
    (ADR-0900 named this as a residual, unfixed defect: "a REAL run of the
    generator would still overwrite the file and drop that key"). Measured
    while landing draw 11: dropping it un-exempts three already-reviewed
    cross-population components with zero held-out members and a component
    digest each of which still matches its recorded `component_fact_ids`
    verbatim -- so `check-autogenesis-nursery.py` goes red on work this draw
    never touched. Carrying the raw list forward is safe specifically because
    `validate_exemptions` re-derives each entry's digest from its own
    `component_fact_ids` and refuses silently-stale ones; this function does
    not interpret the list, only preserves it for that revalidation.
    """
    if not EXTENSION.is_file():
        return []
    got = load_json(EXTENSION).get("cross_population_component_split_exemptions")
    return got if isinstance(got, list) else []


def surface_validation(entries: list[dict[str, Any]],
                       ingest: pathlib.Path | None = None) -> dict[str, Any]:
    """Derive the surface grade from a real Lean run, never assert one.

    The grade used to be the flat literal `"quotation"`, which was true when it
    was written and became false the moment a real Lean run happened. A literal
    also cannot degrade: a later draw that adds rows would inherit whatever the
    string claimed, and the new rows would silently carry an attestation nobody
    ran for them. So this reports three DISJOINT sets, matched row by row:

      attested        the run read this row and Lean accepted it
      not_elaborable  the run read this row and Lean REJECTED it
      unattested      no run has covered this row at all

    A new draw lands its rows in `unattested` automatically. That is the point:
    absence of evidence has to look different from evidence of acceptance.

    WHY THIS LIVES IN THE MANIFEST AND NOT IN ITS OWN ARTIFACT. The first
    version wrote `nursery-v2-extension-surface-attestation.json`, and
    `check-autogenesis-holdout-isolation.py` correctly refused it: that gate
    forbids ANY artifact from naming a held-out fact id except the files which
    define a population, and 70 of these 160 rows are held-out. Exempting a new
    file, or hashing the ids to slip past a syntactic walk, would both weaken a
    guard that exists because prose failed to hold this line. The manifest is
    already exempt and already names every held-out member it preregistered, so
    the grade belongs here -- beside the rows it grades.

    With `ingest`, a fresh `attest-nursery-surface.py --json-out` record is
    folded in. Without it, the stored result is carried forward and re-matched
    against the current entries, so `--check` is reproducible and a new draw
    still degrades honestly.
    """
    base: dict[str, Any] = {
        "quotation_method": (
            "formal.statement is a BYTE-IDENTICAL quotation of the pinned "
            "statement-only extractor's `type` field. Nothing is transcribed, "
            "so there is no transcription to attest."),
        "per_row_binding": "source_statement_sha256",
        "attestation_method": (
            "declare every formal.statement as an axiom after `import "
            "Mathlib`; no theorem value and no proof is read. This is the "
            "method create-autogenesis-mathlib-fact-catalog.py records in "
            "surface_validation.method for nursery-v1."),
        "attestation_command": (
            "python3 scripts/attest-nursery-surface.py --manifest "
            "artifacts/autogenesis/nursery-v2-extension.json --json-out <tmp> "
            "&& python3 scripts/gen-autogenesis-nursery-refill.py "
            "--ingest-surface-attestation <tmp>"),
        "host_requirement": (
            "a Mathlib checkout at the pinned commit WITH .lake/build "
            "populated. As of 2026-08-29 that is s5 "
            "(~/lean-import-scale/mathlib4, 6.2 GB build, Lean 4.30.0, run in "
            "3.6 s for all 160 rows). provision-lean-import-toolchain.sh "
            "provisions a checkout but does NOT build Mathlib, so it is not "
            "sufficient. `command -v lean` returns nothing on a host that HAS "
            "Lean; elan keeps toolchains off PATH -- see "
            "docs/contributor-guide/lean-surface-attestation.md."),
        "means": (
            "acceptance is syntax/type evidence about the STATEMENT, not proof "
            "evidence about the claim. Every row remains open or closed on its "
            "own merits; nothing here settles anything."),
    }

    ids = [e["fact_id"] for e in entries]
    if ingest is not None:
        record = load_json(ingest)
        if record.get("negative_control_rejected") is not True:
            raise RefillError(
                f"{ingest} records a run whose negative control was ACCEPTED, "
                f"so the run distinguishes nothing and cannot grade any row")
        # ADR-0616. An accepted row now counts toward R3's attested cohort, so
        # WHICH Mathlib the run read is load-bearing rather than descriptive.
        # Every `formal.statement` here is a byte-identical quotation of the
        # extractor's output at SOURCE_COMMIT; a run against any other commit
        # grades those strings against a library they were not quoted from, and
        # would silently buy ceiling headroom for a round trip that never
        # happened at the pinned version.
        if record.get("mathlib_commit") != SOURCE_COMMIT:
            raise RefillError(
                f"{ingest} records a run against Mathlib "
                f"{record.get('mathlib_commit')!r}, not the pinned "
                f"{SOURCE_COMMIT}; a row quoted from one commit is not "
                f"attested by elaborating it against another")
        covered = set(record.get("attested_fact_ids") or [])
        if not covered:
            raise RefillError(
                f"{ingest} lists no attested_fact_ids, so no row can be "
                f"matched to it")
        failures = {f["fact_id"]: f for f in record.get("failures", [])}
        source = {
            "host": record["host"],
            "mathlib_commit": record["mathlib_commit"],
            "lean_version": record["lean_version"],
            "module_sha256": record["module_sha256"],
            "negative_control_rejected": True,
            "elapsed_seconds": record.get("elapsed_seconds"),
        }
        not_elaborable = [
            {"fact_id": i, "source_name": failures[i].get("source_name"),
             "lean": failures[i].get("lean")}
            for i in sorted(ids) if i in failures
        ]
    else:
        stored = stored_surface_validation()
        source = stored.get("source")
        if not source:
            base["grade"] = "quotation"
            base["weaker_than_v1_because"] = (
                "nursery-v1's 214 statements were re-elaborated as axioms "
                "after `import Mathlib` and accepted "
                "(accepted-214-proof-free-axiom-types). These have not been: a "
                "pretty-printed type is not guaranteed to re-parse.")
            base["attested"] = []
            base["not_elaborable"] = []
            base["unattested"] = sorted(ids)
            return base
        not_elaborable = [row for row in stored.get("not_elaborable", [])
                          if row["fact_id"] in set(ids)]
        covered = set(stored.get("attested", [])) | {
            row["fact_id"] for row in stored.get("not_elaborable", [])}

    rejected = {row["fact_id"] for row in not_elaborable}
    base["source"] = source
    base["attested"] = sorted(i for i in ids if i in covered and i not in rejected)
    base["not_elaborable"] = not_elaborable
    base["unattested"] = sorted(i for i in ids if i not in covered)
    base["grade"] = (
        "real-lean-axiom-elaboration-per-row" if not base["unattested"]
        else "mixed-real-lean-and-quotation-per-row")
    if not_elaborable:
        base["not_elaborable_means"] = (
            "Lean will not accept these statements as propositions, so they "
            "were preregistered as something that is not a well-formed "
            "proposition and cannot be closed as stated. ADR-0615 forbids "
            "rewriting a preregistered formal.statement, so they are RECORDED "
            "here, not repaired and not deleted.")
    return base


def limitations(validation: dict[str, Any]) -> list[str]:
    """What this cohort still does NOT carry -- derived, never asserted.

    ADR-0616. This list used to be a literal, and it went false the same way the
    grade did before ADR-0615's predecessor made THAT derived: it said "these
    statements carry the quotation grade, not v1's real-Lean round-trip
    attestation" while `surface_validation.attested` in the same file named 197
    rows that had had exactly that round trip. A file asserting both is worse
    than one asserting only the weaker claim, because a reader cannot tell which
    sentence is current.

    So the attestation clause is computed from the run, and what remains is the
    difference attestation does NOT repair: v1's partitions are frozen against
    DECLARED DEPENDENCY WEAK COMPONENTS (`policy.split_component_authority`,
    `split_leakage: no-declared-component-may-cross-evaluation-partitions`),
    while this cohort's `source_group` is the Mathlib defining module and no
    component analysis was run. Two theorems in different modules can sit in one
    dependency component, so a held-out row here can be entailed by a train row
    here and nothing in this manifest would see it. That is a property of the
    ROW, not of the statement, and no amount of elaboration touches it.
    """
    attested = len(validation.get("attested", []))
    unattested = len(validation.get("unattested", []))
    rejected = len(validation.get("not_elaborable", []))
    total = attested + unattested + rejected
    if attested and not unattested and not rejected:
        grade_note = (
            f"All {attested} statements carry the same real-Lean round-trip "
            f"attestation as nursery-v1's 214 -- declared as proof-free axioms "
            f"after `import Mathlib` at the pinned commit, per row and with a "
            f"negative control v1's block run did not carry.")
    elif attested:
        grade_note = (
            f"{attested} of {total} statements carry the same real-Lean "
            f"round-trip attestation as nursery-v1's 214; {unattested} have "
            f"had no run and {rejected} were REFUSED by Lean. Only the "
            f"attested rows may be reported beside v1's as one attested "
            f"population; see surface_validation for which is which.")
    else:
        grade_note = (
            f"These {total} statements carry the quotation grade, not v1's "
            f"real-Lean round-trip attestation; the two must not be reported "
            f"together as one attested population.")
    return [
        "Lean surface propositions are not Axeyum kernel-core terms.",
        grade_note,
        "Attestation does not make this an evaluation population equivalent to "
        "nursery-v1's. v1 freezes partitions against declared dependency weak "
        "components (policy.split_component_authority); here source_group is "
        "the Mathlib defining module and no dependency-component analysis was "
        "run, so a held-out row can share a component with a dispatchable one "
        "and nothing in this manifest sees it. Attestation grades the "
        "STATEMENT; this is a property of the ROW.",
        "Any depends_on on these facts is ledger-owned and accrued after the "
        "fact (ADR-0615), never the preregistered component analysis above.",
        "Mathlib declarations remain external prior art and every Axeyum "
        "fact here remains open.",
    ]


def build_extension(entries: list[dict[str, Any]],
                    reasons: Counter,
                    validation: dict[str, Any]) -> dict[str, Any]:
    partitions = assign_partitions()
    counts = Counter(e["partition"] for e in entries)
    attested = V1_EVALUATION_ENTRIES + len(validation.get("attested", []))
    unattested = unattested_cohort(validation)
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
        "surface_validation": validation,
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
        # What each draw preregistered, before any ADR-0542 amendment. This is
        # the freeze (`frozen_partitions`) and the reference R10 checks the
        # effective `family_partitions` against; the two differ exactly where a
        # recorded breach says they should.
        "preregistered_family_partitions": preregistered_assignment(),
        "family_modules": {f: list(m) for f, m in sorted(FAMILY_MODULES.items())},
        "route_hypotheses": {f: list(r) for f, r in sorted(FAMILY_ROUTES.items())},
        "coverage": {
            "entries": len(entries),
            "families": len(FAMILY_MODULES),
            "per_family": PER_FAMILY,
            "partition_counts": dict(sorted(counts.items())),
            "v1_evaluation_entries": V1_EVALUATION_ENTRIES,
            "combined_evaluation_entries": V1_EVALUATION_ENTRIES + len(entries),
            "attested_cohort_entries": attested,
            "unattested_cohort_entries": unattested,
            "unattested_cohort_ceiling": attested,
            "ceiling_authority": (
                "ADR-0615 as amended by ADR-0616. nursery-v1's "
                "policy.evaluation_fact_count 100..300 governs nursery-v1, "
                "which check-autogenesis-nursery.py checks against its 214 "
                "entries alone. The rule on THIS cohort is ADR-0601's "
                "'scaffolding, never headline': the UNATTESTED population may "
                "never outweigh the attested one. It is counted by attestation, "
                "not by manifest membership -- an extension row Lean accepted "
                "as a proof-free axiom against the pinned Mathlib is on the "
                "attested side, by the same method and the same command that "
                "produced nursery-v1's accepted-214-proof-free-axiom-types. "
                "not_elaborable rows count as UNATTESTED: Lean refused them, so "
                "they are worse than unchecked and must never buy headroom. "
                "When this binds, attest (scripts/attest-nursery-surface.py) "
                "rather than raise it."),
            "screen_rejections": dict(sorted(
                (k, v) for k, v in reasons.items() if not k.startswith("selected:"))),
        },
        "limitations": limitations(validation),
        "entries": entries,
        # ADR-0855, carried forward rather than derived here -- see
        # `stored_cross_population_exemptions`'s docstring for why a plain
        # regeneration used to drop this key silently (ADR-0900).
        "cross_population_component_split_exemptions":
            stored_cross_population_exemptions(),
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
            "type. " + surface_grade_note(entry["fact_id"]) + " Preregistered in "
            "artifacts/autogenesis/nursery-v2-extension.json, which carries "
            "the partition; that manifest, not this file, is the split "
            "authority. Screened against the mirror-divergence registry and "
            "the statable-here vocabulary before preregistration."),
    }


def surface_grade_note(fact_id: str) -> str:
    """The one sentence a fact may honestly say about its surface grade.

    Read from the manifest's `surface_validation`, for the same reason that
    field is derived rather than asserted: a literal cannot degrade. This text
    used to assert the QUOTATION grade unconditionally -- true when written,
    false for 159 rows the moment a real Lean run happened, and still not the
    whole truth for the row Lean REJECTED.
    """
    stored = stored_surface_validation()
    source = stored.get("source") or {}
    commit = (source.get("mathlib_commit") or "?")[:12]
    host = source.get("host") or "?"
    rejected = {row["fact_id"] for row in stored.get("not_elaborable", [])}
    if fact_id in rejected:
        return ("Lean REJECTED this statement. Re-elaborated as an axiom after "
                f"`import Mathlib` against Mathlib {commit} on {host}, it does "
                "not elaborate, so what is preregistered here is not a "
                "well-formed proposition and cannot be closed as stated. "
                "ADR-0615 forbids rewriting a preregistered formal.statement, "
                "so this is recorded, not repaired. See "
                "surface_validation.not_elaborable in "
                "artifacts/autogenesis/nursery-v2-extension.json.")
    if fact_id in set(stored.get("attested", [])):
        return ("Re-elaborated as a proof-free axiom after `import Mathlib` "
                f"against Mathlib {commit} on {host} and ACCEPTED -- the same "
                "grade as the 214 nursery-v1 rows. Acceptance is syntax/type "
                "evidence about the statement, never proof evidence about the "
                "claim.")
    return ("This row carries the QUOTATION grade, weaker than the 214 "
            "nursery-v1 rows, which were re-elaborated as axioms after "
            "`import Mathlib` and accepted: a pretty-printed type is not "
            "guaranteed to re-parse and this one has not been tried.")


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

# The exact clause the generator used to emit for every extension fact. A real
# Lean run made it false for 159 rows and incomplete for the one Lean rejected.
STALE_GRADE_CLAUSE = (
    " -- the QUOTATION grade, weaker than the 214 nursery-v1 rows, which were "
    "re-elaborated as axioms after `import Mathlib` and accepted.")


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


def sync_surface_notes(entries: list[dict[str, Any]]) -> int:
    """Refresh only the surface-grade sentence, only where it is still generated.

    `notes` is NOT a preregistered field, so ADR-0615 permits this -- but a lane
    that closed a mirror may have written its own note, and overwriting that
    would destroy real work. So a file is rewritten only when its current
    `notes` is byte-identical to what this generator would have produced under
    SOME grade sentence. Anything else is reported and left alone.
    """
    grades = [
        surface_grade_note(entry["fact_id"]) for entry in entries[:1]
    ] if entries else []
    rewritten = skipped = repaired = 0
    for entry in entries:
        path = fact_path(entry["fact_id"])
        if not path.exists():
            print(f"SURFACE_NOTES_MISSING|{shown(path)}")
            skipped += 1
            continue
        existing = json.loads(path.read_text())
        want = fact_for(entry)["notes"]
        if existing.get("notes") == want:
            continue
        # Is the note still one this generator wrote, under any grade sentence?
        template_head = ("Open in Axeyum. The external theorem declaration is "
                         "prior art, not a locally constructed proof.")
        template_tail = ("Screened against the mirror-divergence registry and "
                         "the statable-here vocabulary before preregistration.")
        current = existing.get("notes") or ""
        if not (current.startswith(template_head)
                and current.endswith(template_tail)):
            print(f"SURFACE_NOTES_HAND_EDITED|{shown(path)}|left alone")
            skipped += 1
            continue
        existing["notes"] = want
        path.write_text(render_fact(existing))
        rewritten += 1

    # Second pass: the stale grade CLAUSE inside a note a lane extended.
    # 35 facts that lanes closed carry their own prose around the generated
    # sentence, so the template guard above correctly declines to overwrite
    # them -- and they were still asserting the quotation grade, which a real
    # Lean run has made false. Replacing the exact clause preserves every word
    # the lane wrote. Guarded on an exact substring: a note that does not carry
    # it verbatim is not touched.
    for entry in entries:
        path = fact_path(entry["fact_id"])
        if not path.exists():
            continue
        existing = json.loads(path.read_text())
        current = existing.get("notes") or ""
        if STALE_GRADE_CLAUSE not in current:
            continue
        existing["notes"] = current.replace(
            STALE_GRADE_CLAUSE,
            ". " + surface_grade_note(entry["fact_id"]))
        path.write_text(render_fact(existing))
        repaired += 1
    missing = sum(1 for e in entries if not fact_path(e["fact_id"]).exists())
    print(f"SURFACE_NOTES_SYNCED|rewritten={rewritten}|clause_repaired={repaired}"
          f"|hand_edited_left_alone={skipped - missing}|missing={missing}"
          f"|entries={len(entries)}|grades={len(grades)}")
    # A hand-edited note left alone is the guard WORKING, not a failure. A
    # missing fact file is a real inconsistency between manifest and ledger.
    return 1 if missing else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true",
                    help="re-derive everything and fail if the tree differs")
    ap.add_argument("--snapshot-from", type=pathlib.Path,
                    help="rewrite the environment snapshot from shape_search stdout")
    ap.add_argument("--ingest-surface-attestation", type=pathlib.Path,
                    metavar="RECORD",
                    help="fold an attest-nursery-surface.py --json-out record "
                         "into the manifest's surface_validation. Without it "
                         "the stored grade is carried forward and re-matched, "
                         "so a new draw's rows degrade to `unattested` rather "
                         "than inheriting a claim nobody ran for them.")
    ap.add_argument("--sync-surface-notes", action="store_true",
                    help="rewrite the surface-grade sentence in extension fact "
                         "notes from the attestation record. Touches ONLY a "
                         "notes field still matching a generated template, so "
                         "a hand-edited note is never clobbered.")
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

        # ADR-0652: READ, never write. This script is not the owner.
        vocabulary = read_vocabulary(env, inventory, catalog, facts)

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
        # Computed once and handed to both: R3 counts the attested/unattested
        # split, and the manifest publishes it. Deriving it twice would let the
        # guard and the emitted file disagree about the very thing being gated.
        validation = surface_validation(entries,
                                        args.ingest_surface_attestation)
        guard(entries, v1_nursery, env, validation)
        extension = build_extension(entries, reasons, validation)

        # One entry, and it must stay one: VOCABULARY belongs to
        # gen-autogenesis-statable-vocabulary.py (ADR-0652), and
        # check-generated-artifact-ownership.py fails if this script can
        # write it.
        outputs = {EXTENSION: render(extension)}

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

        if args.sync_surface_notes:
            return sync_surface_notes(entries)

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
              + f"|combined={V1_EVALUATION_ENTRIES + len(entries)}"
              # ADR-0616: the two numbers R3 actually compares. Printing the
              # entry count alone hid that 197 rows had been attested while the
              # ceiling still counted all 200 as scaffolding.
              + f"|attested={extension['coverage']['attested_cohort_entries']}"
              + f"|unattested={extension['coverage']['unattested_cohort_entries']}")
    except RefillError as error:
        print(f"autogenesis-nursery-refill: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
