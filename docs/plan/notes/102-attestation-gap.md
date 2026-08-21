# attestation-gap — the detail

Lane `agent-attestation-gap`, 2026-08-18. Everything below is measured on this
checkout unless it says otherwise.

## 1. The brief's number, and where it came from

The brief opened with "270 render a Lean module and split 125 BOUND / 124
ATTESTED / 21 DECLINED", flagged as coming from a capability row and asked to be
re-measured. Re-measured:

    LRA_HYP_BINDING|instances=135|hypotheses=298|mutants_caught=1259|
    mutants_accepted=427|unjustified=0|structural=102|structural_nodes=3372|
    structural_caught=381|structural_accepted=19|anchored=73|anchored_nodes=1098|
    anchored_caught=269|anchored_accepted=3|structural_anchored=66|attested=5|
    attested_vacuous=0|spine_assertions=541|represented_assertions=296|
    undecomposable_spine=0|failures=0

**attested = 5, not 124.** Commits `8e4894de4` (ArrayAxiom renders the query's
own terms), `b9d2f0a77`, `96c9f285b` and `a31a3aea2` had already moved 95 rows to
`structural`, 9 to `bound` and 10 to `anchored`. The capability row in
`crates/axeyum-solver/src/capabilities.rs` was never updated, and it is the
artifact a brief is written from. Corrected in this lane, with the staleness
itself recorded in the row so the next reader knows the failure mode.

The script's own docstring was also partly stale (it said 9 attested where the
manifest said 5, and 20 declined where 20 was right but mis-split 13/7 by logic
when the true split is 16 quantified / 4 not).

## 2. The two causes, counted

The brief asked which cause dominates: fragment classifier declined (solver work)
vs. binder cannot tie theory content back (checker work). On the 5 that remain,
neither is the answer — the actual split is:

| n | cause | whose work |
| --- | --- | --- |
| 2 | the rendered term is the output of a REWRITE the file does not contain (`bvredand x` → `bvcomp x (bvnot #b000000)`; `(= a0 a0)` → `true`) | a rewrite-step certificate; a different object |
| 2 | the same, as a CONSTANT-FOLD: both `replace_all` rows assert `(= A B)` where the arena folded A and B to distinct literals | same |
| 1 | genuinely bare: `ext27` forces FOUR leaf disequalities and a bare pair cannot say which | emitter, or nothing |

The manifest counts these 3/2; the truer count is 1/4, and it already says so in
prose while counting the other way ("which puts them in the rewrite class
below"). Corrected.

## 3. The finding: a second self-refuting module

`3076b6ae0` found the corpus's first — `Not (Eq.{1} α t t)`, refuted by Lean's
own `rfl` — and made its route decline. The predicate it left recognized that one
shape and ran only over the attestation class.

Widening it to the property — `Not X` with `X` provable by reflexivity alone, an
`And`-tree of `Iff p p` / `Eq τ t t` — and running it over **every** rendered
module found a second:

    corpus/regression/cvc5/qf_bv/cvc5__cli__regress0__bv__holes__extract-concat.smt2
    axiom axeyum.reconstruct.hyp._41 :
      Not (And (Iff prop._24 prop._24) (And (Iff prop._23 prop._23) … ×11))

All eleven conjuncts have the SAME name on both sides (checked, not eyeballed).
The `QfBv` route builds its refutation out of `Iff.refl` by design — the
soundness argument is that the reflexive proof fails to type if the lowering is
wrong — and here the bit-blaster hashed the two sides of the query's equality to
the same propositional atoms, so every per-bit `Iff` collapsed onto one opaque
constant. The result typechecks, `#print axioms` is clean, and the identical
module would be accepted for a file that said something else.

Blast radius, measured over the 269 modules that rendered before the fix: **4,652
axioms, exactly 1 self-refuting.** So the emitter declines it, at
`gate_module_content` — the single boundary every route's module crosses, chosen
so a route that degenerates later declines on first exercise rather than shipping
the artifact. `270 → 268` rendered.

The Rust guard is fail-OPEN on anything it cannot parse (a pi-type reads as "no",
which every quantified route needs); the Python predicate is the independent
second opinion, sharing no code.

## 4. DECLINED is a class now, and it worked immediately

Its manifest entry used to read: *"listed so a later sweep does not re-discover
them as news. They are NOT checked."* Both costs of that were live. The
self-refuting module above was sitting in it. And a class nothing runs on can
only be entered — so on its first run as a two-sided pin it evicted two of its
own members, the `bug593` rows (QF_UF and QF_UFBV), which bind structurally at 12
term nodes each with all four corruptions caught.

## 5. …and reading their φ is the other finding

`structural` means less than it reads. The `bug593` query is

    ¬(f (g x) = f (g y)) ∧ ¬(f (g x) = f (g z)) ∧ ¬(f (g y) = f (g z))

and the module renders `¬(fd_fun_0 fd_arg_1 = fd_fun_0 fd_arg_4)` — the emitter
collapses each argument `(g x)` into ONE opaque `fd_arg_N : Bool`, so every
rendered side is a 2-node application. The query's only 2-node applications are
`(g x)`, `(g y)`, `(g z)`, so the injective correspondence found is

    fd_fun_0 → g      fd_arg_1 → x     fd_arg_4 → y     fd_arg_9 → z

not the intended `fd_fun_0 → f`, `fd_arg_1 → (g x)`, which no injective renaming
can express because a rendered LEAF may only stand for a query LEAF. Under the
accepted renaming the module reads `¬(g x = g y)`, which this file does not say.

This is not unsoundness and not a defect in the pin: `structural`'s stated claim
is that every rendered term is a subterm of the query under one injective
renaming, and the docstring is explicit that what the module *asserts* is the
anchor's question. But it is the first measured case of the class being earned by
a renaming that is not the intended one, and the honest reading is **"the module
names terms this file contains"**, not "the module says what this file says". The
two coincide for the `ArrayAxiom` rows and do not coincide here. Pinned in the
structural manifest's own note, beside the rows.

The move out is the one that took 89 `ArrayAxiom` rows from content-free to
structural: render the argument's structure instead of collapsing it.

## 6. What is NOT done, and why

**The gate is RED at HEAD `570b5c738`.** Measured from a clean
`scripts/lane-snapshot.sh HEAD` build, so it is not this lane and not another
lane's uncommitted work: **133 of 249 pinned instances fail.**

    107  `axeyum.reconstruct.lra.x._N declares type CReal, not the opaque carrier Real`
     10  the same with `Int`
     19  `hyp._N is not built from Not, And and equalities between rendered terms`

`a6ee37c6a` ("the SHIPPED front door reconstructs over the constructed reals")
migrated the LRA route's carrier without the transcription checker's carrier
vocabulary following it. Fixing that means teaching `CARRIER_PREFIXES`,
`lean_atom`, `PRELUDE_AXIOMS` and `sort_compatible` a new carrier — a migration
that only the reals lane can do correctly, and exactly the kind of change that
loosens a checker if done by a lane that does not know which laws are sound. Left
undone deliberately.

Consequences for this lane's evidence: the full-sweep numbers in §1 are from the
last binary built before that migration. Everything this lane ADDED is verified
per-instance and offline instead — 17/17 declined, 5/5 attested, 2/2 bug593
structural, 191 unit tests, 6 mutations with no survivors.

No fact was scaffolded. `scripts/new-fact.py` runs the evidence command and
proves each pattern fails on mutated output; with the sweep red at HEAD the
command's exit status would record the CReal breakage, not this lane's result.

**Two more reds at HEAD, both other lanes':**

- `docs/research/08-planning/capability-matrix.md` was out of sync with
  `capabilities.rs` (an ADR renumber 0468 → 0483 reached the source, not the
  generated matrix). Regenerated here as a side effect.
- `cargo +stable clippy -p axeyum-solver --all-targets` fails on
  `examples/ring_interface_pin.rs:100` (`explicit_iter_loop`). Not touched.

## 7. Controls

`python3 scripts/tests/mutation_controls.py lra-hypothesis-binding`, baseline
green, **no survivors**. The six that concern this lane, with the count each
killed — the repository asks for exactly one and two of these are not:

| mutation | tests killed |
| --- | --- |
| self-refutation: a reflexive EQUALITY is recognized | 5 |
| self-refutation: the whole `And`-tree is walked | 3 |
| self-refutation: the two sides must be IDENTICAL | 2 |
| self-refutation is checked on every rendered module | 3 |
| declined: an instance that binds structurally must move | 1 |
| declined: an instance that is an attestation must move | 1 |

Two of these needed fixtures built before they could be killed at all, and both
survived their first run:

- the run-wide check was invisible because every self-refuting fixture was also
  an attestation, and `classify_attestation`'s own copy caught it. It needed a
  module that BINDS STRUCTURALLY and refutes itself.
- the declined class's structural guard was invisible because `STRUCTURAL_MODULE`
  is also a content-free skeleton, so the attestation guard downstream caught it
  either way. It needed a module that binds structurally without being an
  attestation.

That is the CLAUDE.md pattern verbatim — several guards rejecting through one
shared check, all but one removable with everything green.

The old attested-path self-refutation check went from killing a test to
**SURVIVED** the moment the run-wide check landed, so it is deleted rather than
kept: two checks of one property where only one can fire is how a guard becomes
decoration. `attested_vacuous=` leaves the summary line; `declined=` and
`vacuous_modules=` join it.
