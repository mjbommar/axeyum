# ADR-0771: Trust and circularity are read from the admitted term, and the identity map is derived

Status: accepted
Date: 2026-08-30
Index-summary: S2 audits every kernel-route settled fact against its own transitive `Kernel::declaration_dependencies` closure -- 1,956 of 2,041, against S0's measured circularity 38 of 2,117 -- through four guards that look at four different things, each of 15 deletions killing exactly one control; the derived identity map found 13 facts whose proof reaches a byte-identically-typed sibling, disclosed as a ratcheting backlog rather than resettled.
Index-status: accepted

Lane: `l0-s2-trust-circularity`. Phase: ADR-0717 L0,
`docs/plan/trusted-library-safety-roadmap-2026-08-30.md` phase **S2**.

## Context

ADR-0717's risk 4 is **contamination**: *"the target proof, an equivalent
imported theorem, an axiom, opaque, or quotient enters the dependency
closure"*, and the ADR says plainly that an empty axiom footprint addresses only
part of it.

The S0 census ([ADR-0746](adr-0746-the-safety-matrix-is-generated-and-gated.md),
`docs/plan/status/382-l0-safety-matrix.md`) measured how little of the ledger is
protected against that shape. Over 2,117 proved facts:

| protection | facts |
|---|---:|
| `env_footprint` (prelude-wide sweep) | 1,859 |
| `per_theorem_footprint` | 59 |
| `circularity` | 38 |

So almost every trust claim in this ledger is a **batch** measurement — "this
whole prelude has no axioms" — on a command whose fan-out reaches 463 facts. A
prelude-wide sweep is real evidence and it is the wrong instrument for two
questions: it cannot see a target entering its own closure, and it cannot see an
equivalent theorem standing in for the target.

## Decision

`scripts/check-trust-closure.py` computes the closure from the environment the
kernel admitted and audits every kernel-route settled fact against it. It reads
`kernel_declaration_projection` once — kind, name, footprint size, direct
declaration dependencies and the canonical `Kernel::render_lean` type for all
2,482 declarations — and reuses that one build for every check, per the
roadmap's own efficiency rule.

**Coverage: 1,956 subjects of 2,041 kernel-route settled facts (95.8%)**,
against S0's measured `circularity 38 / 2117`.

### Four guards, deliberately looking at four different things

The phase exit is that target injection, indirect target injection, axiom
insertion and checker-population deletion each fail through a **different**
guard. That is not pedantry: six of seven guards in one suite in this repository
were once removable with everything still green, because they all rejected
through one shared check. So the guards are disjoint in what they inspect:

| guard | what it looks at | nothing else |
|---|---|---|
| `guard_self_occurrence` | identity of the subject | — |
| `guard_alias_occurrence` | the derived identity map | — |
| `guard_forbidden_trust` | declaration KIND in the closure | — |
| `guard_population` | the enforced population | **no closure at all** |

The fourth exists because the other three cannot fail when there is nothing to
check, and deleting the subjects is the cheapest way to get a green run.

### The identity map is DERIVED, not authored

Two theorems whose `Kernel::render_lean` types are byte-identical state the same
proposition. Grouping on that string is the whole map: nobody writes an entry,
so nobody can write a wish. It is restricted to `Declaration::Theorem` on
purpose — `AxReal.add` and `AxReal.mul` share the rendered type
`AxReal -> AxReal -> AxReal` and are different opaque constants, not equivalent
statements; axioms are `guard_forbidden_trust`'s business.

It respects the carrier asymmetry [ADR-0716](adr-0716-row-two-of-a-decidable-subject.md)
depends on. `Nat.le_total`, `Int.le_total` and `Rat.le_total` render with three
different carriers and land in three different classes; `CReal.le_total` is
absent. A map that normalized carriers would collapse them and start rejecting
correct facts, so `scripts/tests/test-trust-closure.sh` pins the property
against the **real** environment rather than a fixture — a fixture's types are
whatever the suite writes.

## The finding, and why it is disclosed rather than resolved here

The environment has **15 identity classes, and in all 15 both members are ledger
facts.** Thirty proved facts state fifteen propositions. In **13 of the 15**,
one member's proof closure literally contains the other, so the second fact
proved a renaming of the first:

| fact | its subject | reached in its own closure |
|---|---|---|
| `F:rat-weak-law-of-large-numbers` | `Rat.weak_law_of_large_numbers` | `Rat.chebyshev_sampleMean_uncorrelated` |
| `F:int-characterization-le-total` | `Int.Characterization.le_total` | `Int.le_total` |
| `F:int-characterization-discrete` | `Int.Characterization.discrete` | `Int.no_int_between` |
| `F:int-characterization-zero-lt-one` | `Int.Characterization.zero_lt_one` | `Int.zero_lt_one` |
| `F:nat-peano-succ-injective` | `Nat.Peano.succ_injective` | `Nat.succ_injective` |
| `F:nat-succ-le-succ` | `Nat.succ_le_succ` | `Nat.le_succ_succ` |
| `F:nat-succ-sub-succ-eq-sub` | `Nat.succ_sub_succ_eq_sub` | `Nat.succ_sub_succ` |
| `F:creal-samplelowerbound` | `CReal.sampleLowerBound` | `CReal.rat_approx_lower` |
| `F:creal-sampleupperbound` | `CReal.sampleUpperBound` | `CReal.rat_approx_upper` |
| `F:ml430-nat-clog-monotone-48fe50c6` | `Nat.clog_monotone` | `Nat.clog_mono_right` |
| `F:ml430-nat-log-monotone-52fad774` | `Nat.log_monotone` | `Nat.log_mono_right` |
| `F:ml430-nat-coprime-coprime-dvd-left-2ce391d2` | `Nat.coprime_dvd_left` | `Nat.coprime_of_dvd_left` |
| `F:ml430-nat-coprime-dvd-of-dvd-mul-left-b0608cb9` | `Nat.dvd_of_dvd_mul_left` | `Nat.gauss_lemma` |

The two classes where both members are facts but neither reaches the other are
`Int.add_mul` / `Rat.int_right_distrib` and `CPoint.apollonius_from_stewart` /
`CPoint.apollonius_median`.

**No fact's status is edited by this lane.** An S2 audit does not get to
resettle a proposition, and the right owner for each of these is whoever owns
the fact. They are written to `artifacts/trust-closure/equivalent-pairs.tsv` as
a **ratcheting backlog**, which is the shape that cannot rot in either
direction: a pair not on the list rejects, so no new duplicate lands quietly,
and a listed pair that no longer occurs ALSO rejects, so a resolution has to be
recorded rather than silently absorbed. Neither direction is satisfiable by
adding a line.

Also found, and reported rather than fixed: **no theorem in the whole
environment reaches an axiom.** The only declarations with a nonzero footprint
are the 30 `AxReal.*` axioms themselves, and there are zero `Opaque`s and zero
`Quotient`s. So `guard_forbidden_trust` rejects nothing today. Its scan is real
(1,956 subjects) and its two branches are each mutation-verified against
fixtures, but the honest statement is that it is a tripwire, not a finding.

## The ledger's independence claim counted the producing run

`validate-facts.py` printed `3579 evidence row(s) re-derived by 2+ independent
checkers`. The producing run is not a re-derivation of itself.

Measured over the whole ledger: **1,581 of those 3,579 rows name the producing
run** — `producing-build (Kernel::add_declaration)` 1,333 times, plus 248 more
naming `Kernel::add_declaration` in another phrasing or a `*-producing-solve`.
For a kernel-route fact the proof term is built and admitted in one step, so
`add_declaration` IS the production; listing it beside `Kernel::axiom_footprint`
gives a row with one re-derivation, not two. **2,097 rows carry 2+ checks that
are not the production.**

Both the count and the wording change:

    3579 evidence row(s) checked by 2+ distinct checkers -- 1581 of those count
    the PRODUCING run as one of the two, so 2097 carry 2+ checks that are not
    the production itself

S0's census reported **1,356 of 1,984 facts** by matching the literal string
`producing`; reproduced on today's tree that is **1,359 of 1,989**, the drift
being three facts landed since. That measurement was right about what it
measured, and this classifier is broader on purpose: a checker named
`Kernel::add_declaration (re-derives the type from the proof term)` is the
producing build whether or not the word "producing" appears in it.

**ADR-0746 §"re-derived by 2+ independent checkers counts the producing run"
quotes the old line verbatim and is now stale in that one respect.** It belongs
to the S0 lane and is not edited here; this paragraph is the correction.

A classifier that matched nothing would report the ledger as fully independent —
the most flattering possible answer, and indistinguishable from a broken
pattern. So a zero is an ERROR naming the 1,581 it matched when written, and
that is mutation-verified: replacing the classifier body with `return False` in a
scratch copy gives exit 1 with that message, not a green run.

## Consequences

- `scripts/check-trust-closure.py --quiet` and
  `bash scripts/tests/test-trust-closure.sh` run in **both** aggregate gates.
- Three artifacts are pinned: `identity-map.tsv` (exact compare — a class
  appearing or vanishing is a review event), `equivalent-pairs.tsv` (the
  shrinking backlog above), and `population.json` (floors on subject count,
  coverage ratio and declaration count; growth is free, shrinkage rejects).
- A new duplicate proposition now costs a gate failure at the moment it lands,
  rather than being discoverable only by reading 2,482 rendered types.
- The identity map's exact compare will go red when a lane lands a theorem whose
  type duplicates an existing one. **That is the intended signal**, not churn:
  re-run `--update` after confirming the pair really does state one proposition.

## Alternatives considered

**Hand-author the identity map.** Rejected: an authored map records what someone
believed rather than what the kernel renders, and the whole failure class here
is a claim that outran its evidence. Deriving it also means it cannot be
silently narrowed to make a red gate green.

**Fail on the 13 existing duplicates instead of disclosing them.** Rejected on
ownership: resolving each one means deciding which fact keeps the proposition
and what happens to the other, and no fact's status is this lane's to change. A
permanently red gate is also a gate nobody reads.

**Reuse `check-fact-depends-derived.py` and extend it.** Partly done — its
subject-extraction regex is imported rather than copied, so the five measured
corrections in its comments cannot drift apart. Its own question (does authored
`depends_on` agree with the DIRECT proof edges?) is different from this one (what
is in the TRANSITIVE closure?), and merging them would have made one script that
two roadmap phases both own.

## Verification

    python3 scripts/check-trust-closure.py --quiet
    TRUST_CLOSURE|declarations=2482|identity_classes=15|kernel_facts=2041|
      subjects=1956|unresolved=85|absent=0|disclosed_equivalent_pairs=13|failures=0

    bash scripts/tests/test-trust-closure.sh
    baseline: 17 case(s) behaved
    TRUST_CLOSURE_CONTROLS|cases=17|mutations=15|not_exactly_one=0

Fifteen guard deletions, each killing exactly one case, **zero survivors**. The
four the phase exit names land on four different guards:

| mutation | guard | case killed |
|---|---|---|
| target injection | `guard_self_occurrence` | `target-injection` |
| indirect target injection | `guard_alias_occurrence` | `indirect-target-injection` |
| axiom insertion | `guard_forbidden_trust` | `axiom-insertion` |
| checker-population deletion | `guard_population` | `population-empty` |

    python3 scripts/check-autogenesis-holdout-isolation.py
    AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1109|settled=0|
      references=0|verdict=PASS

## What this lane did NOT do

Per the standing rule that a handoff's "blocked on X" is a claim about one route
and is reliably pessimistic, everything below is what this route did not reach,
not a claim that it is hard.

- **85 kernel-route settled facts resolve to no kernel declaration** and are
  therefore outside every guard here. That is down from
  `check-fact-depends-derived.py`'s 169 (the `kernel_declaration` fallback
  closes most of the gap), but it is a real coverage hole and it is reported,
  not inferred away. The ratio floor makes it unable to grow silently.
- **The 13 duplicates are disclosed, not resolved.** Each needs a fact owner to
  decide which of the pair keeps the proposition.
- **`guard_forbidden_trust` has never rejected real data**, because nothing in
  the environment reaches an axiom. Both branches are fixture-verified; neither
  has a positive instance in the tree.
- **Nothing here checks that a fact's `formal.statement` matches its subject's
  rendered type.** That is S1's question and
  `check-mirror-statement-fidelity.py`'s.
- **The closure is over declaration references, not over the Lean export.** A
  divergence between what this kernel admits and what pinned Lean accepts is
  S4's question, not this one's.
