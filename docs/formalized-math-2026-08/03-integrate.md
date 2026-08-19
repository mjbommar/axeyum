# 03 — Integrate

**The question.** How does collected, aligned mathematics get *through*
`axeyum-lean-import` into an independently-checked environment — at population
scale rather than fixture scale?

> **This phase touches contested files.** `crates/axeyum-lean-kernel/` is owned
> by another lane. `crates/axeyum-lean-import/` is not, but it is one edge away.
> Sequence accordingly; see
> [`refactor-2026-08/00-parallel-work.md`](../refactor-2026-08/00-parallel-work.md).

## Where the path actually stands

```
axeyum-lean-import   official lean4export NDJSON 3.1.0, FAIL-CLOSED
                     17 genuine v4.30 fixtures, 10 test suites
K1 (import)          5/5 — on five PINNED SINGLE-ROOT fixtures
real Init/Std        13 of 40 well-known theorems admitted (2026-08-15)
population           dependency-closed Init/Std/mathlib: UNSTARTED
L3                   0/12 — the phase supplying Z, Dvd, finite sums
```

> **Three of those six lines were false by 2026-08-17 and are left standing so
> the correction is visible.** `13 of 40` was superseded by a **1,500**-declaration
> `Init`+`Std` census at **1,481 clean / 1 declined**
> ([`01-collect.md`](01-collect.md)); `population … UNSTARTED` is wrong twice over
> — `Init`+`Std` and a 400-declaration Mathlib sample were both censused, with the
> corpus retained so a re-run is identical rather than merely equivalent; and
> `L3 0/12` may still be open as an *import* milestone but its stated motivation
> is gone, because ℤ, ℚ, the constructed ℝ and ℂ were all **proved out natively**
> and read `axiom=0 opaque=0 quotient=0` from the kernel on 2026-08-19. We no
> longer need to import ℤ in order to have it. **S1 and S2 below have been run;
> read them as history, not as a queue.**

**Update 2026-08-15.** S1 has been run, five times over, at single-theorem
granularity, and it moved S2 ahead of everything else. The reader handled real
Lean output at every size tried and declined nothing; all 27 declines came from
the kernel's definitional equality, in four clusters
([`01-collect.md`](01-collect.md)). At a 13/40 admission rate a fail-closed
importer reports only the FIRST blocker in a stream, so the decline census S2
describes is not a later refinement — it is the only way to size the remaining
work.

The importer is real and its discipline is good: a private staging kernel that
publishes only after the complete stream succeeds, so an error cannot expose a
partial environment; unsupported string literals, unsafe/partial declarations,
unknown records and malformed or forward references all rejected rather than
skipped; quotient records buffered as one exact ordered package through the
kernel's atomic canonical-package gate.

**What has never been tested is scale.** The five streams committed on
2026-08-15 ARE dependency closures — `lean4export` emits the requested constant
plus everything it reaches — but the largest is 2,692 records and 106
declarations, and all five together are 4,919 records. The difference from there to a population is not linear; it is the
difference between a term and a graph with 8.4 M edges.

> **Scale has since been tested — corrected 2026-08-17.** The census reported in
> [`01-collect.md`](01-collect.md) runs **1,500** individually exported
> `Init`+`Std` declarations — **1,481 clean, 1 declined**, 15 resource, 3 export
> failures — and an earlier round censused a 400-declaration Mathlib sample. So
> "never tested" is wrong by three orders of magnitude in declarations, and the
> decline rate is 0.07% rather than the 27-in-40 this page still quotes above.
> One caveat carried over from the README rather than re-derived here:
> `ImportLimits`' record cap is a **harness** bound, not a kernel refusal, and
> streams that stop at `record count exceeds 2000000` must never be counted as
> declines. What remains untested is a single **dependency-closed population**
> rather than a thousand-odd individual closures.

## The four walls this will hit, all of them already seen

This project has hit the same class of wall four times in one day, and an import
of this size will hit it again. Naming them in advance is cheaper than
rediscovering them:

1. **Materialisation.** `parse_drat` had to hold whole proofs; reconstruction
   held 346 M arena nodes at 24.6 GB; the whnf cache was keyed on a *count*.
   **Assume the importer materialises the stream** until measured otherwise, and
   design the streaming story before the first population run.
2. **The arena.** The kernel's expression arena is monotone and never released —
   measured at ~76–100 bytes per interned node. A 308,129-declaration
   environment is a different order of magnitude from 17 fixtures, and *kernel
   arena checkpointing* is already on the roadmap for exactly this reason.
3. **Per-query rebuild.** Every reconstruction route calls `Kernel::new()` and
   pays ~26 ms of prelude construction, against 6.6 µs to revalidate a cached
   package — **~4,000×**. A large imported environment makes that tax
   proportionally worse, so kernel reuse is a *precondition* for this phase, not
   a follow-up.
4. **A gate that cannot see what it checks.** Formatting was blind to 156
   modules; clippy passed over a cached warning; a validator collapsed 228 errors
   into one message. An import gate must report **what it admitted and what it
   declined**, per declaration, or a partial import will look like a complete
   one.

## The staged plan

**S1 — One dependency-closed slice.** `Init` plus the transitive closure of a
single interesting theorem. Measure: declarations, edges, wire bytes, peak RSS,
wall time, and the decline list. This is the measurement that sizes everything
after it, and the requirements document already names it as the next step.

**S2 — Make declines first-class.** The importer is fail-closed on malformed
input, which is right. For a *population* the useful mode is different: admit
what is admissible, **name every declaration that was not, and why**. A report
saying "admitted 41,203, declined 812, here they are by reason" is a coverage
measurement. A hard failure on declaration 41,204 is not.

This is the same discipline as the claims checker's
`103 claims re-checked, 0 errors, 24 row(s) not re-checked here` — the clause
that names what it could not verify instead of passing silently.

**S3 — Close L3.** L3 is 0/12 and it supplies **ℤ, `Dvd`, and finite sums** —
i.e. exactly the content the [mathematics strand](../mathematics-2026-08/02-the-library.md)
identifies as the keystone. Note the strategic tension and resolve it
deliberately: **ℤ can be imported or constructed, and we are currently doing
both.** The other lane is building ℤ from proved ℕ; the importer could admit
Mathlib's. They are not the same artifact — one has our kernel's proofs behind
it, the other has Lean's — and the difference matters for the assumptions
metric.

**S4 — Population run, with a budget.** Only after S1–S3. Expect to fail; the
value is in *where*, and in the decline census.

## Lean has two checkers, and they disagree

**Measured 2026-08-18 (ADR-0517), and it changes what every sentence in this
strand means by "Lean accepted it."** Lean has two entry points and only one of
them is its kernel:

| route | what checks | verdict on the whole 470-declaration constructed-real carrier |
|---|---|---|
| `lean AxeyumCarrier.lean` | the **elaborator**, over surface syntax | **4 declarations refused**, 14.1 s |
| `lean --run scripts/lean/replay-lean4export.lean carrier.ndjson` | the **kernel**, `Environment.addDeclCore` from `mkEmptyEnvironment` | **all 470 accepted**, 1.4 s |

Three explanations were possible — our kernel is more permissive (a soundness
defect), the renderer emits bytes that do not say what the checked term says, or
a genuine bounded incompatibility. **It is the third.** Lean's elaborator will
not unfold a `theorem` while reducing; the four `CReal` declarations whose
type-checking must compute through `Nat.gcd` — whose Euclidean descent rests on
the *theorem* `Nat.mod_lt` — are therefore refused from `.lean` source and taken
by the kernel, which unfolds anything carrying a value. Re-spelling every
`theorem` as `def`, one token per line with no term changed, takes the carrier
from four refusals to clean; that is the isolation, and it is built as
`Kernel::set_render_proofs_as_def`.

The kernel result is not a bare exit status. The replay reports
`environment now holds 470 constants`, its exit status depends on that count
equalling the one read out of our kernel — so "accepted" cannot silently mean
"accepted a subset" — and swapping one proof for another closed proof makes the
same binary print `REAL LEAN KERNEL REJECTED … but it is expected to have type …`.

**The default did not change** ([ADR-0518](../research/09-decisions/adr-0518-proofs-stay-spelled-theorem-and-the-def-option-is-a-measuring-instrument.md)):
every `.lean` artefact this repository *ships* already elaborates clean under
`theorem`, so the switch costs 1.36–1.69x elaboration to buy nothing on the
shipped surface — and flipping it would make the suite that pins the divergence
report that Lean had closed it, a checker whose failure mode is a false
all-clear.

### The coverage hole this sat in, which is the part to learn from

Nothing found it for months because **emission is reachability driven**. Every
Lean cross-check in this repository renders the closure of *one refutation*, so
Lean had only ever seen the declarations some query cited: 343 of 465 when
ADR-0511's lane measured it, leaving **122 declarations that had never been
handed to any Lean at all**. The first time anything pointed Lean at the whole
set, two were refused outright and two more cascaded.

It is closed by `real_lean_creal_carrier_kernel_replay`, which exports the
**complete** environment and requires Lean's reported constant count to equal
our kernel's. Generalise the lesson rather than the fix: *a cross-check driven
by reachability measures the queries you ran, not the artifact you built.*

### State it as a limitation, because it is one

Two things are true and neither is a footnote:

- **The shipped `.lean` artefact still does not carry the whole carrier.**
  Measured through the front door on 2026-08-19
  (`--example front_door_carrier --require-axiom-free`, exit 0), the three
  fixtures emit 1,304,276 / 1,330,091 / 1,442,247 bytes over `CReal` with **zero
  carrier axioms** — but each is the closure of its own refutation. A reader who
  checks one of those files has checked what that refutation needed.
- **Four of the carrier's declarations are kernel-checkable but not
  elaborator-checkable.** No shipped artefact contains them. That is the whole
  claim, and it should be published at exactly that width — not softened, and
  not inflated into "Lean rejects our reals."

### How much real Lean actually runs, and what that number is not

Measured 2026-08-19 by running `scripts/check-lean-gate.sh` to completion on this
host (exit 0):

```
21 suites, 66 tests, 473 real-Lean checks (floor 219)
Lean 4.30.0, commit d024af099ca4bf2c86f649261ebf59565dc8c622, via the pin;
every suite confirmed it used that same binary
crosscheck content: 37 families carry a theory reconstruction,
                    40 are STRUCTURAL ATTESTATIONS   (lean_crosscheck: 77 of 77)
```

The gate exists because on 2026-08-14 every one of these suites printed `ok`
while running **zero** real Lean — it resolves the pin itself, sets
`AXEYUM_REQUIRE_LEAN=1` so a missing binary fails rather than skips, cross-checks
that each suite used the binary it was told to, and enforces a floor on the
summed count because an exit status cannot distinguish 219 checks from 2
(ADR-0514).

**And it says so about itself, which is the part to copy.** 473 is a count of
modules Lean *read*, not of propositions Lean *proved*: 40 of the 77 crosscheck
families emit a structural attestation — `axiom prop : Prop`, `axiom hyp1 : prop`,
`axiom hyp2 : Not prop`, then `False` by application — which Lean accepts
trivially and whose acceptance says nothing about the proposition. That is why
the gate floors the two halves separately; flooring only the sum would let theory
families be replaced by attestations with the headline unmoved. Any import
coverage number this phase produces should carry the same split.

### The size of the artefact, and why it is not shrinking

The 1.3 MB is the reason the whole-carrier question is awkward, so record where
that number came from and what it costs to move. A refutation over the
constructed reals first rendered at ~2.6 MB; scope-aware `let` sharing halved it
to ~1.3 MB, and that is the ceiling for anything the writer can do alone —
**99.84% of a query module is a development that is byte-identical for every
query over that carrier**, and the final theorem term is 4,193 bytes.

The remaining order of magnitude is not better sharing; it is emitting that
development once. A **split module layout** — `import` a once-emitted shared
prelude — takes the per-query half to **5,056 / 14,567 / 1,954 bytes**, i.e.
**257x / 91x / 738x**. The shared half is 1,715,764 bytes, compiles once in
14.4 s to a 3,786,256-byte `.olean`, after which each query module checks in
**0.102 s**.

**It is not the default, and that is the right call**
([ADR-0511](../research/09-decisions/adr-0511-the-shared-development-is-emitted-once-as-its-own-lean-module.md)):
the split is a **strictly weaker artefact for a third party**, because it needs
`--root` and `LEAN_PATH` rather than one file `lean` will read, and 17+ real-Lean
suites assume the single-file contract. It is supported, measured, and claimed
only where a suite runs the published recipe with a no-`LEAN_PATH` negative
control — without which "the import worked" is indistinguishable from "the query
module proved it alone."

## The measurement that makes this strand worth doing

Not "declarations admitted". This:

> **How many of Mathlib's declarations does an independent kernel, written by
> different people in a different language, accept — and where exactly does it
> disagree?**

A disagreement would be a genuinely significant finding about a library 284,457
theorems deep, and finding none is a strong assurance result. Either outcome is
publishable, and axeyum is one of very few systems positioned to produce it,
because it has a second kernel rather than a second copy of the first.

**Amended 2026-08-18: that question is ill-posed until it names a checker.**
"Lean accepts it" is two different measurements, and the section above shows they
give different answers on real declarations. A census that reports "Lean agrees"
without saying whether it ran the elaborator or `addDeclCore` is reporting a
number nobody can reproduce — and the two disagree in the direction that flatters
us, which is the direction to be most careful about. Every decline census in this
strand should name its route.

That is also why S2 matters more than S4: **the decline census is the result**,
not the leftovers.
