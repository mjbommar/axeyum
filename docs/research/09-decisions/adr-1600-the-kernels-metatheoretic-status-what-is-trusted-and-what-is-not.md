# ADR-1600: the kernel's metatheoretic status — what is trusted, what is checked, and what is not

Status: accepted
Date: 2026-09-04

Index-summary: the trusted core is 5,526 lines of function bodies across 9
files (derived by call-graph closure from the kernel's four admission gates,
`scripts/check-kernel-trusted-core.py`, measured 2026-09-04) out of 378,049
function-body lines in the crate; the kernel admits `Axiom`/`Definition`/
`Theorem`/`Opaque`/`Inductive`/`Constructor`/`Recursor`/`Quotient` with no
`Quot.sound`, `funext`, `propext` or choice; three soundness-critical guards
were mutation-verified to fire and one candidate (a phantom-parameter domain
check) was found to be currently redundant with a downstream check under
existing test coverage; the Lean 4.34.0-rc1 cross-check is red on one named,
open mutant (`level.max-kind:1322:max-to-imax`) that is not a soundness
defect; no consistency, normalization, or model-theoretic soundness proof
exists or is claimed.

Related: [ADR-0517](adr-0517-lean-has-two-checkers-and-the-kernel-is-the-one-we-target.md),
[ADR-1594](adr-1594-the-crosscheck-pin-moves-to-lean-4-34-0-rc1-and-follows-the-pin-file.md),
[`docs/contributor-guide/evidence-and-checker-discipline.md`](../../contributor-guide/evidence-and-checker-discipline.md),
[`docs/prover-track/research/13-residual-trust-surface.md`](../../prover-track/research/13-residual-trust-surface.md).

## Context

`python3 scripts/validate-facts.py` reports 2,487 proved facts with an empty
`axiom_footprint` on every one of them. Reviewer 10 (logic and foundations)
and reviewer 12 (the chair) both name the same gap independently
(`docs/math-department/10-logic-and-foundations.md`,
`docs/math-department/12-the-chair.md`, convergence C6 on
`docs/math-department/00-roadmap.md`): nobody outside this project can assess
that headline number without knowing what the checker that produced it
assumes. This ADR writes that down, measured rather than asserted, and closes
roadmap item W0-4. It adds no kernel code and proves no theorem; every claim
below names the command or the file that produced it.

## 1. Size of the trusted base

**Measured 2026-09-04 by re-running the existing, gated derivation:**

```
$ python3 scripts/check-kernel-trusted-core.py
kernel trusted core (derived from Environment::insert_unchecked)
  admission gates          4
    inductive.rs:331  Kernel::restore_nested_inductive_group
    inductive.rs:1639 Kernel::add_inductive_group
    quotient.rs:60    Kernel::add_quotient_package
    tc.rs:1543        Kernel::add_declaration
  trusted functions        256 of 8374
  trusted function lines   5526 of 378049
  ceiling                  5900
  per file (trusted / all function lines):
      1991 /   2027  tc.rs
      1984 /   2546  inductive.rs
       683 /   1005  lib.rs
       605 /    638  quotient.rs
       133 /    177  env.rs
        92 /    104  expr.rs
        32 /   1680  lean_export.rs
         3 /      3  level.rs
         3 /      3  name.rs
  NOT trusted              369866 function lines in 437 files (preludes, pretty-printer, arithmetic model)
ok: 5 guards, 0 failures
```

**The method, so the boundary is arguable rather than eyeballed.** A
declaration can only come to exist through `Environment::insert_unchecked`
(`env.rs`, `pub(crate)`). The script finds every non-test call site of that
function; each enclosing function is an *admission gate*; the trusted core is
the forward call-graph closure from the four gates above. Everything a gate
calls is trusted; everything that only *calls* a gate (a prelude, a producer,
a solver) is not, because that is what a kernel is for — it re-checks
whatever a caller hands it. This is why `nat_prelude.rs` (8,865 lines, plus
its `nat_prelude/` submodule split of over 200 files) contributes **zero**
trusted lines despite being the single largest file in the crate: it is
content the kernel checks, not code the kernel runs to check.

**Three things a hand estimate gets wrong, each measured rather than
assumed.** First, whole files are not trusted: `lib.rs` contributes 683 of
1,005 function-body lines and `lean_export.rs` only 32 of 1,680 — counting
files instead of the reachable functions overstates the surface by roughly
80% on `lib.rs` alone. Second, `lean_export.rs` is not interop-only:
`Kernel::is_k_like_inductive` (in the file everyone would file as "trusted
only for the Lean crosscheck") is reached from `k_like_major` → `reduce_rec`
→ `whnf` → `def_eq`, and K-like reduction is a soundness-critical ι-rule.
Third, there are four admission gates, not the three that name themselves
`add_*`: `restore_nested_inductive_group` inserts declarations directly after
nested-inductive expansion is checked under temporary names.

**A whole-file line count as a cruder sanity check.** Summing the nine
top-level source files that plausibly belong to the checker
(`lib.rs`, `env.rs`, `tc.rs`, `inductive.rs`, `expr.rs`, `level.rs`,
`name.rs`, `stack.rs`, `quotient.rs`), *excluding* every `#[cfg(test)]`
module (both separately filed — `env_tests.rs`, `tc_tests.rs`,
`inductive_tests.rs` — and the large inline `mod tests` block in
`quotient.rs`, 578 of its 1,324 lines), gives roughly 10,100 lines — about
1.8x the derived figure, because whole-file counting cannot see that most of
`lib.rs` and nearly all of `lean_export.rs` outside `is_k_like_inductive` sit
on the caller side of the four gates. **The derived, gated 5,526 is the
number to cite**; the whole-file figure is reported here only to show the
direction and size of the error a less careful method makes.

**This is a derived measurement, not a proof of correctness, and the script
says so.** The call graph over-approximates (loose method resolution misses
nothing; it can only ever *add* spurious edges), so 5,526 is an upper bound —
the safe direction for a trust claim. Its blind spots are trait dispatch and
function values passed without a direct call. Five guards in
`scripts/tests/test_check_kernel_trusted_core.py`, each mutation-verified
against a real incident, catch a new `insert_unchecked` call site, a `pub`
`Environment` mutator, growth past the 5,900-line ceiling, a file joining or
leaving the trusted set, and a scanner that goes blind and reports a
beautiful clean zero. The trusted-core NUMBER moving is not itself a defect —
it moved from 5,148 (2026-08-17) to 5,526 today as content and fixes landed —
but an *undetected* move is exactly the gap the ceiling and file-set guards
close.

**A second, separate reporting surface is worth naming here because it is
easy to conflate with the checker.** `Kernel::axiom_footprint` — the function
`scripts/validate-facts.py` and every `proved` fact's evidence ultimately
rest on for the "empty footprint" claim — lives in `lean_pp.rs`, **outside**
the derived trusted core (`lean_pp.rs` contributes only `is_k_like_inductive`
to the trusted set). That is correct: `axiom_footprint` cannot cause a wrong
proof to be *admitted* — it runs after admission, walking `decl_deps` to
collect every `Axiom`/`Opaque`/`Quotient` a proof transitively rests on. But
a bug in *it* can make a footprint claim wrong in the other direction: an
under-counted dependency edge would report `[]` for a proof that is not
axiom-free. This is a distinct trust question from "does the checker admit
only true things," and this ADR does not derive its own trusted-core bound
for it; a future lane extending `scripts/check-kernel-trusted-core.py` (or a
sibling script) to cover the *reporting* surface, not only the *admission*
surface, would close that gap the same way this one was closed for
admission.

## 2. What the kernel admits

Read from `crates/axeyum-lean-kernel/src/env.rs`'s `Declaration` enum and
`crates/axeyum-lean-kernel/src/inductive.rs`/`quotient.rs`, not from prose or
memory.

**Eight declaration kinds**, exactly:

| kind | what it is | δ-unfolds? |
|---|---|---|
| `Axiom` | an asserted constant with no value | never |
| `Definition` | `def name : ty := value` | yes, with a reducibility hint |
| `Theorem` | like `Definition`, but its value is opaque during lazy-δ (two theorems compare structurally before unfolding) | yes, but opaque-first |
| `Opaque` | checked at admission, never δ-unfolded thereafter | never |
| `Inductive` | a parametric/indexed type, admitted only via `Kernel::add_inductive*` | — |
| `Constructor` | one constructor of an `Inductive` | — |
| `Recursor` | generated by the inductive gate, carries its own ι-reduction rules | — |
| `Quotient` | one of Lean's four privileged quotient-package members, admitted only transactionally as a complete set | — |

**Universe handling** (`level.rs`, 46 lines, entirely inside the trusted
core, unchanged since 2026-08-17): `Level` is `Zero | Succ | Max | IMax |
Param`. `IMax l r` is the impredicative max — `Zero` when `r` is `Zero` (so a
`Pi` into `Prop` stays in `Prop`), `Max l r` otherwise. Declarations carry an
explicit `uparams: Vec<NameId>` list, and — the subject of the guard
demonstrated in §3 below — every `Param` a declaration's type or value
mentions must be one it declares; nothing else in the kernel compares the
parameters *occurring* in a term against the parameters a declaration
*binds*, so an unchecked declaration's `uparams` list is decorative rather
than enforced.

**Strict positivity** (`inductive.rs`): after WHNF, a constructor field's
domain may not mention any family in its own mutual group; this is checked
recursively through every `Pi` a field's type opens, over the *whole* mutual
group at once (positivity ranges over every family, every constructor, every
field — ADR-0352, TL2.11). §3 demonstrates this guard firing.

**Well-founded recursion is not a kernel primitive.** `WellFounded.fix` and
`Acc.rec`/`Acc.inv`/`WellFounded.fix_eq` are ordinary content, declared in
`prelude.rs` (a *checked* file, outside the trusted core) entirely from the
generic `Acc` inductive type and its kernel-generated recursor. Nothing in
the trusted core special-cases well-founded recursion; its soundness
therefore reduces to strict positivity and recursor generation for the `Acc`
family specifically, which is exactly the general machinery §1 already
counts.

**What is absent, checked by reading `quotient.rs` and grepping the trusted
core rather than asserting it:**

- **`Quot.sound` does not exist anywhere in the trusted-core files.** The
  quotient package installs exactly `Quot`, `Quot.mk`, `Quot.lift`,
  `Quot.ind` — Lean's own naming — and no fifth declaration. `grep -c
  'quot_sound\|Quot.sound\|QuotSound'` across every trusted-core file returns
  zero.
- **No `funext`, `propext`, or choice principle** is declared anywhere in the
  trusted core or the shared preludes as an axiom the kernel special-cases;
  none of `lib.rs`/`env.rs`/`tc.rs`/`inductive.rs`/`quotient.rs` references
  them.
- **No excluded middle.** The logic prelude is intuitionistic; `Nat.em_*`
  results (reviewer 10's reverse-mathematics pair) prove classical
  consequences *from EM as a discharged hypothesis*, never from an axiom.

This is the design choice reviewer 12 (the chair) names as "the metric and
the limitation are the same fact": the empty footprint on 2,487 facts is a
direct consequence of not having `Quot.sound`/`funext`/`propext`/choice
available at all, which is also exactly what blocks abstract algebra,
category theory, and the algebraic half of geometry (W0-1, not this ADR's
subject).

## 3. What guards it, and whether each guard can fail

There are **49 kernel integration suites**: 32 run at push
(`scripts/check-kernel-suites.sh --list`) and 17 more, all named
`real_lean_*` plus `kernel_differential`, are owned by
`scripts/check-lean-gate.sh` because they invoke an external Lean binary.

Per CLAUDE.md's rule ("delete one guard, require exactly one test dies"),
this ADR mutation-tested four soundness-critical checks — one more than the
three the brief suggested, because the third produced a finding worth
reporting honestly rather than a clean kill. Every mutation was made in a
private snapshot (`scripts/lane-snapshot.sh`, extracted to
`/data0/axeyum/scratch/`), never in the shared worktree; every mutation was
restored and verified byte-identical to the shared worktree
(`diff crates/axeyum-lean-kernel/src/{tc,inductive}.rs` against the snapshot
copies, both clean) before this ADR was written.

**Guard 1 — strict positivity** (`inductive.rs`, `check_group_positive_occurrence`).
Mutated the domain check inside the recursive-field walk
(`if self.mentions_group_family(domain, group) { return
Err(NonPositiveInductiveOccurrence...) }` → `if false && ...`). Result:
**both tests in `strict_positivity.rs` fail** (`public_twelve_row_contract_matrix`,
`generated_grammar_is_complete_and_byte_identical`), on the assertion
`left: ReflexiveOrNestedNotSupported ... right: NonPositiveInductiveOccurrence`
— a *different* rejection variant fires for these fixtures (a downstream
shape check happens to also reject them), so the mutation is caught by a
wrong-error-variant assertion rather than a wrongly-admitted declaration on
this suite's specific 840-case generated grammar. Restored file: 2/2 pass.

**Guard 2 — `Prop` large-elimination soundness** (`inductive.rs`,
`mk_group_recursors`'s `allows_large_elimination` computation). Mutated the
sole-constructor subsingleton test (`[constructor] =>
constructor.exposes_non_prop_fields` → `[constructor] => true`, i.e. always
permit large elimination for a single-constructor `Prop` family regardless
of whether it exposes non-`Prop` fields). Result: **exactly one test dies**
— `generated_prop_elimination_boundary_matrix` in
`prop_large_elim_soundness.rs`, on `constructors=1, data_fields=1,
proof_fields=0` (left 1, right 0) — while `non_subsingleton_prop_eliminates_only_into_prop`
and `prop_large_elim_derives_false`'s exploit test both still pass unaffected.
Restored file: 3/3 pass.

**Guard 3 — nested-inductive phantom-parameter domain check**
(`inductive.rs`, `instantiate_nested_parameter_prefix`, added specifically
to close the erasure route of upstream Lean kernel bug #14576: a container
parameter absent from every constructor field disappears from the
specialized auxiliary family, so nothing in the temporary expanded group can
reject an ill-typed argument in that slot). Mutated the `self.check_core(parameter,
domain, &mut ctx)?` call to a no-op. Result: **zero tests died** — all 5
tests in `nested_phantom_parameter_soundness.rs` and all 23 in
`nested_inductive_elimination.rs` and all 18 in `mutual_inductive_groups.rs`
still pass. The reason is in the guard's own doc comment, read *before*
mutating rather than after: "restoration re-infers the published surface and
does reject it... but that leaves the only gate far from the substitution
that erased the argument" — restoration (`ensure_nested_published_type`)
independently re-checks the ill-typed argument against the *original,
unspecialized* container parameter type, so under this repository's current
test corpus the outcome (rejection) is unchanged when this specific check is
deleted. **This is not evidence of a soundness hole** — the declaration is
still rejected, just by a different, later mechanism — but it is evidence
that this particular defense-in-depth line has no test that depends on *it
specifically*, contrary to what "delete a guard, require exactly one test
dies" would predict for a soundness-critical check. Flagged here rather than
silently reported as a clean pass, per this repository's own rule that a
checker (or, here, a guard) whose failure cannot be observed is worse than
none; closing it (a fixture where restoration's re-check cannot reach the
erased position, if one exists, or an explicit acknowledgment that it
cannot) is left to a lane that owns `inductive.rs`. Restored file verified
byte-identical to the shared worktree.

**Guard 4 — universe-parameter binding** (`tc.rs`,
`Kernel::check_declaration`, the check described in §2 and found by the
adversarial differential documented in
`docs/prover-track/research/13-residual-trust-surface.md`). Mutated the
`if let Some(param) = self.undeclared_universe_param(...)` body to never
return the error while keeping `param` referenced (so the mutant compiles).
Result: **exactly two tests die**, both directions of the same guard
(`an_unbound_universe_parameter_in_the_type_is_refused`,
`an_unbound_universe_parameter_in_the_value_is_refused`), while the
constructor-position variant and all three positive-admission controls in
the same seven-test file keep passing. Restored file: 7/7 pass, plus the 5
`nested_phantom_parameter_soundness.rs` tests re-confirmed unaffected in the
same run.

**What this establishes.** Three of four soundness-critical checks examined
have an observable, specific test dependency — deleting each breaks a
predictable, narrow set of tests and nothing else, which is the "checker
that can fail" property this repository requires. The fourth is real
defense-in-depth whose own dedicated suite currently cannot distinguish it
from the check it duplicates; mutation testing found this because, per this
repository's own documented limitation, it measures the guards a suite
*has*, and here it correctly reported that this particular line contributes
nothing this suite can observe losing.

## 4. The external cross-check

`lean-toolchain` pins `leanprover/lean4:v4.34.0-rc1` (moved from 4.30.0 on
2026-09-03, ADR-1594); confirmed against the live host:

```
$ bash scripts/check-lean-gate.sh --print-toolchain
bin=/home/mjbommar/.elan/toolchains/leanprover--lean4---v4.34.0-rc1/bin/lean
source=elan-pinned-toolchain
version=Lean (version 4.34.0-rc1, ..., commit 3447a668783dbce1a8fdb97101dd067687b2b418, Release)
pin=leanprover/lean4:v4.34.0-rc1
```

`scripts/check-lean-gate.sh` was run in full against this pin
(2026-09-04). Per-suite counts through `real_lean_wellfounded_elaborator_divergence`
(16 of 17 named suites; `kernel_differential` and `real_lean_wire_differential`
are the two most expensive and are reported separately below because of their
run time — hundreds of real Lean invocations each):

```
real_lean_inductive_crosscheck                  1 test(s),   1 real-Lean check(s)
real_lean_parametric_inductive_crosscheck       2 test(s),   2 real-Lean check(s)
real_lean_strict_positivity_crosscheck          1 test(s),   9 real-Lean check(s)
real_lean_nat_literal_crosscheck                1 test(s),   3 real-Lean check(s)
real_lean_nat_arithmetic_crosscheck             1 test(s),   2 real-Lean check(s)
real_lean_string_literal_crosscheck             1 test(s),   2 real-Lean check(s)
real_lean_local_let_zeta_crosscheck             1 test(s),   2 real-Lean check(s)
real_lean_structure_eta_recursor_crosscheck     1 test(s),   4 real-Lean check(s)
real_lean_structure_eta_crosscheck              1 test(s),   2 real-Lean check(s)
real_lean_string_monoid_crosscheck              2 test(s),   1 real-Lean check(s)
real_lean_compact_share_crosscheck              2 test(s),   2 real-Lean check(s)
real_lean_shared_prelude_crosscheck             3 test(s),   4 real-Lean check(s)
real_lean_kernel_replay                         1 test(s),   2 real-Lean check(s)
real_lean_creal_carrier_kernel_replay           4 test(s),   3 real-Lean check(s)
real_lean_replay_census                         5 test(s),   6 real-Lean check(s)
real_lean_wellfounded_elaborator_divergence     1 test(s),   4 real-Lean check(s)
kernel_differential                             2 test(s),  35 real-Lean check(s)
```

`real_lean_kernel_replay` is the load-bearing suite from ADR-0517: the
**whole** checked environment (all 470+ declarations, no reachability
filter) exported as `lean4export` NDJSON and replayed through Lean's own
`Environment.addDeclCore` — the kernel entry point, not the elaborator —
and its exit status depends on Lean's reported constant count equalling the
count read out of our kernel.

**`real_lean_wire_differential`** (in `axeyum-lean-import`, not itself one of
the 32 push-half suites, but one `check-lean-gate.sh` also runs) is the
adversarial direction: it damages exported NDJSON bytes in ways that stay
structurally valid and hands the *identical* bytes to both kernels, failing
only when ours accepts and Lean's refuses. This is the instrument that found
four real defects in three rounds during its own development
(`docs/prover-track/research/13-residual-trust-surface.md` §2) — three of
them the same shape, bookkeeping copied across a boundary and never
compared, including the universe-parameter-binding defect Guard 4 above
re-demonstrates. Its default budget is 396 mutants (`AXEYUM_WIRE_MUTANTS`)
per run, each a real Lean invocation (~12 minutes wall-clock for the full
sweep, measured below); it was run in full for this ADR as part of
`scripts/check-lean-gate.sh` rather than treated as a fifth guard
demonstration, because its own suite structure — one violation-reporting
test over a stratified corpus, not one test per mutant — does not fit this
ADR's per-guard mutation format.

**Known and currently red — reproduced fresh for this ADR, not taken on
faith.** `scripts/check-lean-gate.sh` was let run to completion against the
current tree and the 4.34.0-rc1 pin (2026-09-04; the full 396-mutant sweep
took 705.28s). It failed with exactly one violation:

```
WIRE_DIFFERENTIAL|generated=9638|checked=291|families=80|lean_kernel_rejected=103|
  lean_regeneration_mismatch=161|lean_malformed=0|lean_accepted=27|ours_declined=263|
  stricter_than_lean=0|aux_recursor_checked=17|aux_recursor_discriminated=17|violations=1

thread 'our_kernel_admits_nothing_the_real_lean_kernel_refuses' panicked:
OUR KERNEL IS MORE PERMISSIVE THAN LEAN'S on 1 of 291 mutants:
level.max-kind:1322:max-to-imax: OUR kernel admitted a stream the real Lean
kernel type-checked and REFUSED.
---- lean said ----
line 1332: REAL LEAN KERNEL REJECTED the declaration: (kernel) declaration
type mismatch, 'DecidablePred' has type
  (a : Sort u) → (a → Prop) → Sort (max u 1)
but it is expected to have type
  (a : Sort u) → (a → Prop) → Sort (imax u 1)

test result: FAILED. 4 passed; 1 failed.
```

Of 291 checked mutants this run, 263 were correctly declined by our kernel,
17 of 17 auxiliary-recursor mutants were discriminated, and exactly this one
was accepted here and refused by Lean on the wire. This matches, independent
of it, the account recorded the day the toolchain pin moved in
`docs/plan/status/495-coordinator-structures-tactics-2026-09-03.md`:
`level.max-kind:1322:max-to-imax` rewrites `DecidablePred`'s declared
`Sort (max u 1)` to `Sort (imax u 1)` on the wire. Our kernel admits it;
Lean's kernel refuses it **on the wire**, under both 4.30.0 and 4.34.0-rc1,
while **both accept the equivalent from source**
(`def T (α : Sort u) : Sort (imax u 1) := α → Prop`). The two levels are
equal for every `u` — `imax u (succ _)` is `max u (succ _)` — but Lean's C++
`normalize` rewrites the `imax` side to an unsorted `max u 1` while the
`max` side sorts to `max 1 u`, so its `is_equivalent` compares two spellings
of the same level and answers no; the elaborator hides this from source by
normalizing first. Our kernel's level-equality check is, on this instance,
*more complete* than Lean's own — correct for every `u`, where Lean's is not
— which is a defensible thing for an independent kernel to be, but it means
the differential's "ours accepts, Lean refuses" trigger fires on a case
where the divergence runs the *other* direction from every prior finding in
that suite's history (§4 above and
`docs/prover-track/research/13-residual-trust-surface.md` §2 name four prior
defects, all found where we were wrongly *permissive* relative to a rule
both kernels intend). The decision the status note names as open — record a
controlled, fixture-pinned exemption, or make this kernel's level check as
incomplete as Lean's for wire-compatibility — is **not decided here**; this
ADR records it, reproduced first-hand, and does not resolve it, per its
brief. `stricter_than_lean=0` in the same run confirms this is not a second
instance of a broader pattern within this sweep. This is the reason
`scripts/check-lean-gate.sh` is not yet in the push hook.

## 5. What has not been checked, and why

**No consistency proof.** Nobody has shown this type theory — or Lean's,
which it tracks — cannot derive `False`. By Gödel's second incompleteness
theorem, if this kernel's logic is consistent and can express enough
arithmetic to formalize its own proof predicate (it can: `Nat`, well-founded
recursion, and the recursors this kernel builds are exactly that expressive
power), **no proof of that consistency can be carried out inside this same
system**. A "the kernel proves itself consistent" result is not merely
undone here; it would be a red flag if it existed, since an inconsistent
system also proves everything, including its own consistency.

**No normalization proof.** Strong normalization (every well-typed term
reduces to a normal form in finitely many steps) is what would justify that
`whnf`/`def_eq` in `tc.rs` always terminates rather than merely terminating
on every input exercised by the 49 guard suites and the differential fuzzing
in §3–4. The general technique (reducibility candidates / logical relations,
extended to handle universes, strictly positive inductive families, and
well-founded recursion via `Acc`) is well understood in the literature for
type theories in this family, but no such proof has been carried out for
*this* kernel's exact admitted profile — nested and mutual inductive groups,
the K-like reduction rule, structure eta, and the quotient package's
`Quot.lift`/`Quot.ind` reduction together.

**No soundness proof relative to a model.** Nobody has built a set-theoretic
or realizability interpretation of this type theory's Pi/Sigma/inductive/
universe fragment and shown every admitted judgement is true under it. Model
constructions for closely related systems exist in the wider literature, but
whether any of them cover this kernel's *exact* admitted profile — its
specific quotient package (without `Quot.sound`), its specific nested/mutual
inductive and K-like/structure-eta rules, its specific universe-parameter
discipline — is itself unverified by this project and is not asserted here.

**Why a metatheory of this kernel cannot be done inside this kernel.**
Beyond Gödel's second theorem for consistency specifically: any of the three
results above, if attempted as a kernel declaration, would need to quantify
over "every well-typed term" or "every derivation" as an object the kernel
reasons about — a statement about the kernel's own type theory, stated
*in* that type theory. That is exactly the self-reference a sound system of
this strength cannot resolve in its own favor. A metatheorem of this shape
is a theorem in a stronger or orthogonal system *about* this one, never a
kernel declaration this kernel admits.

**What a relative result would require, concretely.** Three separate
ingredients, in a system *external* to this kernel:

1. A precise, on-paper specification of the exact rule set this kernel
   implements — not "Lean's type theory" in general, but this admitted
   profile specifically (the eight declaration kinds in §2, the positivity
   and large-elimination restrictions in §3, K-like reduction, structure
   eta, the quotient package's four members and no fifth). Nothing in this
   repository currently states that specification independently of the Rust
   source; the 49 guard suites and the differential in §4 are *tests against
   an implementation*, not a specification a proof could be checked against.
2. A model (set-theoretic, realizability, or a normalization-by-evaluation
   argument) built for that exact specification, in a meta-theory at least
   as strong as this kernel plus whatever the universe hierarchy needs
   (typically: enough of ZFC to interpret the universe levels this kernel
   admits). This is genuinely large, specialist work — comparable in scope
   to existing consistency results for the Calculus of (Co)Inductive
   Constructions — and nothing here should be read as claiming it is
   close, easy, or already substantially done.
3. A *second*, independent argument that the ~5,526 trusted-core lines
   measured in §1 correctly *implement* the specification from (1) — a
   software-correctness question distinct from the metatheory question in
   (2), and the one this repository's differential testing (§3–4) already
   provides strong, but empirical rather than proof-theoretic, evidence for.
   A metatheoretic consistency proof for the abstract rules would say
   nothing about whether this specific Rust code realizes them; that
   question is answered today by testing, adversarially and against an
   independent implementation, not by proof.

**What the 49 guard suites and the differential testing in §3–4 actually
are, stated plainly so the distinction is not lost:** strong, adversarially
designed, mutation-verified *evidence* that this kernel's admission gate
rejects what it should reject and accepts what it should accept, on every
input anyone has thought to construct — including inputs generated
specifically to be the shape a real defect would need (§4's four found
defects). That is categorically different from a proof that no input exists
which breaks it. Both are legitimate forms of assurance; conflating them is
the exact overclaim this ADR exists to prevent.

## Decision

Publish this account as the kernel's metatheoretic status. Concretely:

1. The trusted-core size a reader should cite is the derived, gated
   5,526 lines / 256 functions / 9 files from
   `scripts/check-kernel-trusted-core.py`, not a hand estimate — and any
   future citation of a "roughly Nk lines" figure for this kernel should
   re-run that script rather than quote a number from this or any other
   document, since the figure moves as content lands (5,148 on 2026-08-17,
   5,526 today) and only the script's own guards detect an *undetected*
   move.
2. `Kernel::axiom_footprint`'s status as a reporting function outside the
   admission-gate trusted core (§1) is recorded as a named, open gap: no
   script currently derives a trusted bound for the footprint-reporting
   surface the way `check-kernel-trusted-core.py` does for admission.
3. Guard 3's finding (§3) — a real, documented defense-in-depth check with
   no test that depends on it specifically — is recorded rather than fixed
   here, for a lane that owns `inductive.rs` to close.
4. The `level.max-kind:1322:max-to-imax` divergence (§4) is recorded as
   open and unresolved, per this ADR's brief; the decision between a
   controlled exemption and matching Lean's incompleteness is left to the
   lane that owns `real_lean_wire_differential`.
5. §5's three-part account of what a relative consistency/normalization/
   model-soundness result would require is the standing answer to "has this
   been proved sound," until one of those three ingredients is actually
   produced. Nothing in this repository currently claims otherwise, and this
   ADR is the citable source for that claim's absence.

## Consequences

- A hostile reviewer now has a single document to check the headline
  axiom-freedom claim against, with the derivation method for its own
  central number reproducible in one command.
- The distinction between "tested extensively against an independent
  kernel" (true, and demonstrated fresh in §3–4) and "proved sound" (not
  attempted, and explained in §5 why not here) is now stated once, in one
  place, rather than left for a reader to infer from the absence of a
  claim.
- Guard 3's finding gives the kernel-owning lanes a concrete, scoped,
  already-diagnosed follow-up: either a fixture that discriminates the
  phantom-parameter domain check from restoration's re-check, or an
  explicit acknowledgment in `inductive.rs` that the check is intentionally
  redundant and why that redundancy is still worth its cost (fails closer to
  the point of erasure, per its own doc comment).
- Nothing here changes what the kernel admits, what evidence a fact carries,
  or any published count. This ADR is documentation of measurements already
  true of the tree before it was written.
