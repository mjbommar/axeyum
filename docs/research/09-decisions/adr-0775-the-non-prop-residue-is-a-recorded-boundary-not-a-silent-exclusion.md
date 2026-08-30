# ADR-0775: The non-Prop residue is a recorded boundary, not a silent exclusion

Status: accepted
Date: 2026-08-30
Index-summary: Pinned Lean's kernel refuses a `theorem` whose type is not a
`Prop`; 73 of the constructed-real carrier's 2,058 declarations are of that
shape or depend on one, so the whole-carrier replay claim was false. It is
narrowed to the representable population (1,985, count equality enforced), the
exclusion is EARNED by requiring Lean to refuse the unfiltered export naming a
declaration this kernel independently classified, the superseded statement is
kept executable, and the residue becomes its own OPEN row.

Lane: `carrier-replay-overclaim`
Related: [ADR-0517](adr-0517-lean-has-two-checkers-and-the-kernel-is-the-one-we-target.md),
[ADR-0760](adr-0760-independent-replay-is-graded-per-declaration-by-name.md),
ADR-0717 (the trusted-library threat model), and
[the safety roadmap](../../plan/trusted-library-safety-roadmap-2026-08-30.md)'s
S1 and S4.

## Context

`F:lean-kernel-accepts-the-whole-constructed-real-carrier` was `proved`,
`proof_route: kernel-lean`, and said pinned Lean 4.30.0's own kernel accepts
**every** declaration that `build_creal_prelude` admits, with no reachability
filter, ending with as many constants as this kernel holds.

It is not true, and the same binary says so. `Lean.Environment.addDeclCore`
refuses a `theorem` whose type does not live in `Prop` — in Lean such a thing
must be a `def`. This kernel has no such rule, and uses the freedom
deliberately: `CReal.UniformConvergesOn` is `Type`-valued so a convergence
*rate* is data, since `Exists.rec` cannot eliminate into `Type`.
`CReal.weierstrassMTest` concludes in it.

Measured 2026-08-30 on pinned Lean 4.30.0 (`d024af09`), independently by
L0/S4's `real_lean_replay_census` and again by the corrected suite:

| | S4 census | corrected suite |
|---|---|---|
| population | 2,045 | 2,058 |
| representable | 1,972 | 1,985 |
| `theorem_type_not_prop` | 48 | 48 |
| `blocked_by_dependency` | 25 | 25 |

The two populations differ because the carrier grew between the runs; the
residue is the same 73.

**Nothing was proved wrong.** Lean rejected no proof — it refused a *kind*. So
this is a measured disagreement between two kernels about what may be called a
theorem, not a demonstrated soundness hole, and this ADR does not claim one.
What it was is 73 declarations of the flagship carrier holding no
independent-replay grade, with nothing in the ledger saying so. Two of them are
flagship results: `CReal.rolle_interiorExtremum` and
`CReal.mvt_interiorExtremum`, blocked by `CReal.hasDerivative_neg` and
`CReal.hasDerivative_add`.

### Why it went unseen for twelve days

The fact's own suite could not reach a verdict. `creal` needs 16 MiB of stack
in debug (`artifacts/kernel-stack-envelope.tsv`) and a `#[test]` thread has
2 MiB, so `build_creal_prelude` SIGABRTed before a single Lean process ran.
L0/S4 wrapped it in `on_a_deep_stack`; it then reached Lean and failed. That is
ADR-0717's **risk 5, false evidence** — a crash reading as absence — sitting
under a headline claim.

## Decision

1. **The claim is narrowed to the representable population**, and the exclusion
   is defined by Lean's admission rule rather than by anything we chose: a
   declaration is non-representable if it is a `Theorem` whose type is not a
   proposition, or if its dependency closure reaches one. Both facts are read
   from the kernel by `Kernel::infer` and
   `Kernel::declaration_dependency_closure`, never from a list.
2. **The narrowing must be EARNED, every run.** The suite hands pinned Lean the
   **unfiltered** export and requires it to fail, and requires the declaration
   Lean names to be one this kernel independently classified as
   not-a-proposition. Without that, "we excluded 73" would be a convenience.
3. **The superseded statement is preserved three ways**, per the safety
   roadmap's S1 rule that a corrected row keeps what it used to say: verbatim in
   the fact's `notes`; as an amendment row in
   `artifacts/ontology/settled-fact-statement-pins.json` carrying both SHA-256
   digests and a reason; and **executable**, as
   `the_superseded_whole_carrier_claim_is_refuted_by_the_same_binary`. Prose
   cannot go red; that test can, and will, if Lean ever accepts the unfiltered
   export.
4. **The part no longer claimed becomes its own OPEN row**,
   `F:lean-kernel-accepts-the-non-prop-residue-of-the-constructed-real-carrier`,
   rather than a footnote under a `proved` one. A narrowed claim stays honest
   only if what it drops has somewhere to be counted.
5. **The residue is enumerable in the run.** Every one of the 73 is printed by
   name with its typed reason, and `untyped=0` is asserted: the two classes must
   exhaust the residue, and every `blocked-by-dependency` blocker must itself be
   a not-a-proposition theorem, or `BlockedBy` would be a second unexamined
   exclusion route wearing the first one's name.

### Why the fact stays `proved` rather than being demoted

The corrected statement is strictly weaker than the old one and is exactly what
is measured and re-derivable today, with a negative control on a proof and
another on the kind rule. Demoting it would say we no longer have a carrier-wide
independent replay, which is false; leaving the old text `proved` would say we
have one we do not have. The status question is settled by which *statement* is
on the row, and the amendment ledger is what makes that visible rather than
convenient. The residue's `open` row is where the number that is *not*
established lives.

## Consequences

- `real_lean_creal_carrier_kernel_replay` goes from 1 test and 2 real-Lean
  invocations to 4 tests and 3, and `scripts/check-lean-gate.sh`'s counted floor
  rises 229 → 230.
- The classification lives in
  `crates/axeyum-lean-kernel/tests/support/creal_representability.rs`, included
  by `#[path]`, so `real_lean_replay_census`'s equivalent copy can adopt it with
  a one-line change when its owner next touches it. Two implementations of one
  rule that must stay in sync is a defect this repository has paid for before.
- **A fact about the residue must not cite the parent.** A count equality is a
  strong statement about a population and a weak one about a member; per-name
  grading is ADR-0760's census, and that is what an individual theorem's fact
  must cite.

## The guard question this raises, and the honest answer

`AXEYUM_REQUIRE_LEAN=1` was already in every one of the fact's checker commands.
It would **not** have caught the crash, and that was measured rather than
reasoned: reproducing the defect (running the prelude on the `#[test]` thread)
and running the fact's own corrected `checker_command` unchanged gives

    CHECKER_COMMAND_STATUS=101
      stack-overflow lines: 1     SIGABRT lines: 1
      toolchain banners:    0     lean-checked markers: 0
      REQUIRE_LEAN panics:  0

`AXEYUM_REQUIRE_LEAN=1` fires only when a toolchain cannot be *resolved*, and
the abort happens long before `lean_probe::lean_bin_or_skip` is reached — hence
zero panics from it.

**Every other guard was already fail-closed and none of them was wrong.** The
checker command's `out=$(cargo test …) && test …` exits 101 on a crashing suite;
`check-lean-gate.sh` fails the suite three separate ways (nonzero cargo status,
`unnamed-toolchain`, `0-lean-checks`). So the gap was **running**, not guarding:
the suite is registered in a gate that nobody ran for twelve days. Adding a
fourth guard to the same unrun gate would not have helped, and claiming
otherwise would be exactly the kind of unfalsifiable safety story this ADR is
correcting. The countermeasure that would have worked is the one the repository
already knows it needs — running the aggregate gate rather than a narrow
re-verification.

What *is* now cheaper is noticing a partial loss: the gate's counted floor is
the finest instrument available here, and going from 2 to 3 real-Lean
invocations means silently dropping any one of the three trips it.

## Mutation kill sets, as measured

Each mutation perturbs the SUBJECT rather than deleting an assertion that
currently holds — deleting an always-true assertion kills nothing by
construction and would report a survivor for the wrong reason. Run in this
lane's own worktree, never the shared checkout.

| mutation | tests killed |
|---|---|
| `is_a_proposition` always `true` | 3 — count/acceptance, superseded-claim refutation, typed residue |
| no `blocked-by-dependency` exclusion | 1 — count/acceptance only |
| Lean's count compared against the whole population (the superseded relation) | 1 — count/acceptance only |
| the refutation aimed at the FILTERED stream | 1 — superseded-claim refutation only |
| `on_a_deep_stack` removed (the historical crash) | all 4, and the `checker_command` exits 101 |

**The tamper control survived the first mutation, and it is recorded rather
than hidden.** With every declaration classified representable, the exported
stream carries all 48 non-proposition theorems, and
`pinned_lean_rejects_a_substituted_proof_…` still passed: Lean refuses the
tampered `CReal.Equiv.not_zero_one` before it reaches any of them, so the pass
is honest but carries no information about the classifier. An assertion was
added stating what that control assumes — a kind refusal must never be read as
a proof refusal — and it did **not** change the mutation's outcome. The two
guards fail on disjoint defects.
