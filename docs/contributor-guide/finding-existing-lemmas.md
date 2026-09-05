# Finding Existing Lemmas — retrieval is the bottleneck

More lane-hours have gone to re-deriving what already existed than to proof
difficulty. This is the measured account of where lemmas hide, which tools reach
them, and which hiding place no tool can reach.

The diagnosis that made this a first-class tooling deficiency is
[2026-08-27: retrieval is the bottleneck](../research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md);
this document is the operating procedure. Retrieval is one of the three gates on
marginal cost per theorem in
[the cost model](../formalized-math-2026-08/07-the-cost-model-and-pareto-position.md).

## Step 0 belongs to whoever writes the brief

`just brief <target…>` (`scripts/brief-step0.py`) derives the conclusion and
hypothesis heads from the target's `formal.statement`, runs the `shape_search`
query, and adds what the query alone cannot: whether a declaration with these
constants is already in the environment (by rendered type, never by name), every
module basename the target could mean **in both preludes**, and whether the
target is held-out, a mutation control, or divergence-blocked. It exits 3 when
its own control probe fails and 4 on a stale snapshot — the two failure modes an
ordinary `shape_search` call cannot self-report. Sub-second warm.

Measured 2026-08-31 over 429 lane status documents: `shape_search` appears in 30
(7.0%) against mutation testing's 180 (42.0%), and `brief-step0` in 10 (2.3%).
The gap is not emphasis — it is that the harness had no entry point anybody
reading about retrieval would encounter.

## The lemma you need usually exists, and the name search will not find it

**THE LEMMA YOU NEED USUALLY EXISTS, AND THE NAME SEARCH WILL NOT FIND IT.
THREE DISTINCT HIDING PLACES, ALL MEASURED 2026-08-27.** Four lanes in one
session reported their blocker already solved, in three different ways. The
common cost is not the rebuild -- it is that each lane first *sized* the work
as new, and two nearly built a duplicate.

1. **General infrastructure filed under its first consumer's module.**
   `CReal.bucketIndex` (a computed index on the unit-fraction grid, with four
   clamp lemmas) lives in `creal/uniform_continuity.rs` because a covering
   argument needed it first. It is now consumed by `crossing.rs`,
   `integral.rs` and `sqrt.rs`. A lane sent to build an Archimedean crossing
   index found it in step 0 and reduced its whole task to a rescaling.
2. **A reusable step built INLINE inside a larger declaration and never
   exposed.** `nat_prelude/powsq.rs`'s `declare_pow_half_split` builds a full
   `Nat` even/odd split (`e_eq_final`, twice -- once per branch) purely as
   scaffolding toward a `pow` equation. Nothing named it. A lane sent to build
   `Nat.even_or_odd` extracted it instead of re-deriving it. The same shape
   blocks the Weierstrass M-test today: `converges_of_scaled_cauchy`
   (`creal/convergence.rs:1356`) performs the `Within` -> CReal `close_within`
   step internally via `speedup_close` + one `Rat.natDivSucc_add` fusion, and
   the only PUBLIC lemma of that shape, `within_of_two_sided_le`, runs the
   **opposite direction**.
   <!-- was-absent: CReal.weierstrassMTest, CReal.close_within_of_within -- the claim above is historical; `scripts/check-absence-claims.py` (ADR-0611) fails if either is ever removed, and had this carried an `absent:` marker it would have gone red the day they landed instead of costing two lanes -->
**CORRECTION, 2026-08-27: the M-test example above is STALE, and it cost two
lanes.** `CReal.weierstrassMTest` was landed in full generality
(`creal/uniform_convergence.rs`, commit `1d08388a3`), along with
`CReal.close_within_of_within` — which solved the `Within` -> `close_within`
step NOT by extracting `convergence.rs`'s private helper as the text above
speculates, but by an independent route through the already-public
`sample_upper_bound`/`sample_lower_bound`. The coordinator read the stale text
as a live blocker and dispatched a lane at a finished task.

It happened TWICE in one hour. The same coordinator logged a deficiency
<!-- was-absent: Rat.sumRange -->
asserting `Rat.sumRange` had no diagonal/rectangle reindexing and dispatched an
Opus lane; `rat_prelude/diagonal.rs` already carried it, AND `complex.rs`
already ran the same argument over ℂ including the two-bound form that
`diagonal.rs`'s own module doc called missing.

**So the rule this section states for LANES applies to whoever writes the
brief, and more sharply**, because a brief multiplies the error by the lane it
dispatches: **verify a blocker still exists in the tree before treating it as
one — including a blocker this file names.** A file that records obstacles
accumulates stale ones by construction, and its authority is exactly what makes
them expensive. Cheap check, and the only one that works: grep the tree for the
declaration, with a positive control of the same kind.

3. **A lemma whose stated hypothesis is WEAKER than everyone assumes.**
   `CReal.sumRange_cauchy_of_dominated` is `∀ f g, (∀ k, le (abs (f k)) (g k))
   → …` -- it never required `f` nonnegative, so it **already covers signed
   series** and the separate absolute-convergence bridge is unnecessary for
   that purpose. TWO lanes discovered this independently, both against a brief
   that asserted the opposite. Read the signature, not the surrounding prose.

5. **THE SAME MODULE NAME EXISTS IN TWO PRELUDES, AND EVERYONE CHECKS THE
   WRONG ONE.** Measured 2026-08-29. Three successive totient triages, plus a
   brief I wrote pointing at it explicitly, all looked at
   `int_prelude/crt.rs` and concluded the Chinese Remainder machinery did not
   transport to a `Nat` counting argument. **`nat_prelude/crt.rs` also
   exists** — Nat-native, 17 KB, with `Nat.crt_unique` — and it transports
   directly. Combined with the existing pigeonhole
   (`injective_on_imp_surjective_on`) it gives the residue-pairing map's
   bijectivity with no Bezout witness at all.

   Two files, same basename, different preludes. `ls src/*/crt.rs` would have
   shown both in one command, and nobody ran it because everybody already
   "knew" where CRT lived. The same pair exists for `parity.rs`, `gcd.rs`,
   `division.rs` and others.

   **When a module you need is named for a mathematical topic rather than a
   carrier, check EVERY prelude for that basename before concluding anything
   about transport.**

6. **THE SAME ARGUMENT OVER A DIFFERENT AGGREGATE IN A DIFFERENT PRELUDE.
   This one defeats BOTH retrieval tools, which is why it is worth its own
   entry.** Measured 2026-08-30. A lane needed "counting over `[0,n)` is
   invariant under an injective self-map" and `320`'s triage had searched
   `permutation.rs`, `cardinality.rs` and `subset_product.rs` and correctly
   found nothing. The answer was **`Int.prodRange_permute`**, which had
   existed since Wilson's theorem: same induction, same
   `restrict_injective`/`restrict_maps_into` helpers, reusable skeleton --
   but over the **product** aggregate in the **Int** prelude.

   A name search misses it (nothing says `countRange`). `shape_search` misses
   it too, and that is the point: its conclusion head is `AxInt.prodRange`,
   so no `--concl AxNat.countRange` query can reach it. The only thing that
   finds it is recognising the PROOF SKELETON, which no index we have
   represents.

   So when a triage reports a permutation/reindexing/invariance lemma absent,
   **ask which other aggregates this development folds over** (`sumRange`,
   `prodRange`, `countRange`, `maxRange`) and **in which other preludes**, and
   read the one that is furthest along rather than the one that matches your
   carrier. Not everything transports -- that lane deliberately did NOT copy
   `prodRange_swap`'s adjacent-transposition machinery, because counting
   accumulates with `Nat.add` and a single point-change lemma replaced the
   whole apparatus -- but the skeleton did.

4. **THERE IS NO SINGLE SPELLING, so grep fails even when you DO know the
   name.** The kernel name is `CReal.congrOfUniformlyContinuous`; the Rust
   prelude field, the design docs, every brief and this file all say
   `congr_of_uniformly_continuous`. Measured 2026-08-27 over 447 `CReal`
   declaration names: **315 carry an underscore, 225 an internal capital, and
   117 carry BOTH.** So a lane grepping the spelling it read in a doc misses
   the declaration, and a lane grepping the kernel spelling misses every Rust
   call site. This is not a naming inconsistency to clean up -- the two
   conventions serve different layers -- it is a retrieval hazard to route
   around. `shape_search --name-like <either spelling>` normalizes; grep does
   not.

**The technique that works: search for the STEP, not the NAME -- and there is
now a tool for it (ADR-0608).** `examples/shape_search.rs` indexes **every**
declaration kind by conclusion head, per-hypothesis head and type constants
(1,838 declarations, ~13-21 s), and **fails on absence** with exit 1, printing
a same-kind positive control; exit 3 means *unanswerable*, deliberately
distinct. The canonical miss returns exactly one row from shape alone:

    cargo run --release -p axeyum-lean-kernel --example shape_search -- \
      --include-constructed --concl CReal.Equiv \
      --hyp CReal.UniformlyContinuousOn --hyp CReal.Equiv

Failing that, grep for the shape of the intermediate you need -- an index
computation, a case split, a direction of transport -- across the whole crate,
not for what you would have called the finished lemma.

**DO NOT ASSEMBLE THAT QUERY BY HAND. `just brief <target…>` DOES IT FOR
YOU, AND THIS SECTION NEVER SAID SO.** `scripts/brief-step0.py` derives the
conclusion and hypothesis heads from the target's `formal.statement`, runs
the `shape_search` query, and adds the three things the query alone cannot
give: whether a declaration with these constants is ALREADY in the
environment (by rendered type, never by name), every module basename the
target could mean **in both preludes** when a basename lives in two, and
whether the target is held-out / a mutation control / divergence-blocked. It
exits 3 when its own built-in control probe fails (so no ABSENT in that run
meant anything) and 4 on a stale snapshot -- the two failure modes an
ordinary `shape_search` call cannot self-report. Sub-second warm.

This is the step 0 of a brief, and it belongs to whoever WRITES the brief,
not to the lane. Measured 2026-08-31 over 429 lane status documents:
`shape_search` appears in 30 (7.0%) against mutation testing's 180 (42.0%),
and `brief-step0` in 10 (2.3%). The gap is not emphasis -- this file has
argued the point at length for four days -- it is that the harness had no
entry point anybody reading about retrieval would encounter.

**And the OUTCOME is now gated, which it was not.**
`scripts/check-shape-duplicates.py` reports declarations whose admitted
types are identical up to binder naming -- two proofs of one proposition,
which is exactly what a lane that could not find an existing lemma
produces -- and refuses any group that is not on record with a reason, in
both directions (an unadjudicated group AND an allowlist entry nothing
reports any more). It existed from 2026-08-27 and `check.sh` registered
only its UNIT TESTS, so the checker itself ran only when a human typed it;
its first automatic run found five unadjudicated groups, one a genuine
re-derivation of right-distributivity over Int (ADR-1170). It is an L0 gate
now, in `local-ci.sh`, `ci.yml` and `check.sh`, held there by
`check-l0-gate-enforcement.py`.

**What that gate does NOT cover, and no name-based or type-based tool can:
hiding place 2.** A reusable step built INLINE inside a bigger declaration
has no declaration of its own, so it has no type to compare and cannot
appear in any duplicate group. Re-deriving such a step is invisible to
every gate here. Only reading proof BODIES finds it.

**A STALE PREBUILT `shape_search` REPORTS A FALSE ABSENT, which is the one
failure this tool exists to prevent.** It indexes the declarations its own
binary was compiled against, so `target/release/examples/shape_search` left
over from an earlier build answers about an OLD environment. Measured
2026-08-27: a prebuilt copy in the shared checkout reported **1,845**
declarations against a current **1,850**, and did not know `CReal.integral_abs_le`
-- a declaration that had landed hours earlier. Harmless for an old lemma;
for a RECENT one it says ABSENT, exit 1, with a perfectly convincing
same-kind positive control beside it.

This is the general prebuilt-binary hazard (`target/release/examples/` takes
no cargo lock and is the right tool for measurement under contention) meeting
the one question where a wrong negative is expensive. **Before trusting an
ABSENT verdict, check the `declarations=` count in the coverage line against a
fresh build, or rebuild.** A FOUND verdict needs no such care -- a stale index
cannot invent a declaration.

**AND A STALE BINARY CAN PRODUCE A CONFIDENT *POSITIVE* THAT IS ALSO WRONG,
WHICH THE "FOUND NEEDS NO CARE" RULE ABOVE DOES NOT COVER.** Measured
2026-08-29: a stale prebuilt dumper emitted a **96 MB** Lean module for a
trivial `14x + 21y = 5` refutation. That binary predated
`reconstruct::MAX_LEAN_MODULE_BYTES`, so it produced the giant string where
the current code *declines* and exits 1 with zero bytes. The 96 MB number was
real output from real code -- just not the code in the tree.

It then survived two hops: a lane reported it, I wrote it into a brief as
"over the checker's 64 MB safety cap", and the cap is not the checker's at
all. The lane that finally measured it had to correct both the size story and
whose cap it was.

So the rule generalises past ABSENT verdicts: **a stale binary's output
describes an older tree in every direction -- absent, present, and how big.**
When a measurement will be quoted, rebuild or check freshness first, and when
a number seems implausible for the input, suspect the binary before the
algorithm. `--include-constructed` inventories are useless
here for case 2 by construction: an inline step has no name to list.

And note the asymmetry when you find one: extracting an inline step into its
own declaration is cheap and reusable; **re-deriving it beside the original
leaves two proofs of one fact that must stay in sync while the kernel happily
verifies both.** That has already happened once this session, with six private
helpers copied verbatim rather than reported.

**PROSE HAS NOT FIXED THIS, AND THE COUNT KEPT CLIMBING AFTER THIS SECTION WAS
WRITTEN.** Every brief in the 2026-08-27 session repeated "search for the STEP,
not the NAME", and lanes still reported reaching **thirteen** instances, with
more landing the same day: `CReal.equiv_of_le_le` and
`CReal.equiv_zero_of_small` were both budgeted as new work in a Fermat brief
and both already existed.

The most expensive was `CReal.congr_of_uniformly_continuous`, which stalled a
whole rung of `supOn`. A lane needed exactly it, searched
`creal/uniform_continuity.rs` -- the module where it BELONGS -- found nothing,
and stopped. It lives in `creal/integral.rs:17010`, because
`riemann_sum_split_exact_of_uc` consumed it first. **The search was competent
and its answer was correct**; you cannot find by name a thing whose name you do
not know. (Nor can it be strengthened to a global
`∀ x y, Equiv x y → Equiv (F x) (F y)` -- that form is FALSE for an arbitrary
witness, since `UniformlyContinuousOn` says nothing about `F` outside `[a,b]`.)

Because instruction demonstrably does not close it, it is logged as a
first-class TOOLING deficiency in
[`docs/research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md`](docs/research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md),
with shape-indexed retrieval over `kernel.environment()` dispatched against it.
Two things that write-up is careful about, and you should be too: the thirteen
is a **lane-reported tally that has not been independently audited**, and any
name index is **structurally blind to hiding place 2** -- an inline step has no
declaration to index, so no such tool can ever reach it.

Retrieval is one of the three gates on marginal cost per theorem named in
`docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md`
(contracts, retrieval, sharding). On this evidence it is the binding one:
**more lane-hours went to re-deriving what existed than to proof difficulty.**


## A handoff's "blocked on X" is a claim about one route

**A HANDOFF'S "BLOCKED ON X" IS A CLAIM ABOUT ONE ROUTE, NOT ABOUT THE
TARGET -- AND IT IS RELIABLY PESSIMISTIC.** Three instances on 2026-08-30, all
from lanes that verified the blocker instead of inheriting it:

- Two lanes recorded `Nat.dvd_mul` as "a factorization-existence statement
  with no short route found". A third tried the gcd construction
  (`k1 := gcd(k,m)`, `k2 := k/gcd(k,m)`) and closed it. Both earlier lanes had
  sized it before `Nat.gcd_mul_right` existed and neither had tried that route.
- The modular-cancellation family was recorded as needing new division-by-gcd
  machinery. What actually unlocked it was `Nat.gcd_cofactors_coprime`,
  **already present in `bezout.rs`**, which neither prior lane found -- and on
  the Int side `Int.gcd_div_gcd_div_gcd` and `Int.gauss_lemma` also already
  existed, contrary to the handoff that said otherwise.
- `Int.dvd_mul`'s handoff named three prerequisites. **Two were unnecessary**
  once the proof routed through `natAbs` bridging to the Nat lemma; only one
  was real, and it was cheap.

The mechanism is not carelessness. A lane that stops writes down what **its
own route** still needed -- honestly, and usually accurately about that route.
It cannot name the lemma that makes a different route work, because it never
looked for it. So a blocker list is a lower bound on what one path costs, and
says nothing about the cheapest path.

So: **when briefing against a handoff, tell the lane to verify each named
prerequisite in-tree and to consider whether a different route avoids it.**
Ask "which of these does the BEST route need?", not "how do we build these
three?". And note the asymmetry -- a handoff's report of what it LANDED is
reliable; its report of what REMAINS is a hypothesis.


