# Lane diary: `quant-bv-shares`

**2026-08-14.** The real-Lean gate's first honest run rejected 1 of 70 proof
families, `quant_bv_source_instance_set`. This lane classifies that rejection,
fixes it, and folds the excluded suite back into the gate.

**Verdict: a printer/emitter defect. Not a reconstruction defect.** The kernel
proof term is well typed; the module *text* mis-associates the arguments of a
recursor application. Nothing in `crates/axeyum-solver/src/reconstruct/` was
changed to fix it — the whole fix is 15 lines in the Lean *writer*.

## Reproduced first, before trusting the report

```
$ ~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean q.lean
q.lean:1655:25: error: Application type mismatch: The argument
  axeyum_proof_share_33
has type
  Prop
of sort `Type` but is expected to have type
  ∀ (x2 : axeyum_proof_share_69), ?m.5 ⋯
of sort `Prop` in the application
  axeyum_proof_share_149 axeyum_proof_share_33
…
q.lean:1697:2: error(lean.unknownIdentifier): Unknown identifier `axeyum_proof_share_160`
$ echo $?
1
```

101 errors, in the two shapes the finding described. The module is 5431 lines /
358 036 bytes; the theorem is `axeyum_refutation : False`.

## The discriminating question, and how it was settled

**The technique first, because the technique is the transferable part.** A Lean
rejection has two possible causes and they are not equally bad:

* a **printer defect** — the kernel holds a well-formed term, the module text is
  wrong. Fixable, no soundness implication.
* a **reconstruction defect** — the proof object really is ill-typed and our own
  kernel accepted it. That is soundness-relevant and is owed a fact and an ADR.

You cannot tell them apart by reading the rendered module, because **the renderer
is one of the suspects**. The discriminator is to interrogate the *structural*
kernel objects — the `Declaration` and the `ExprId` graph in the environment —
and only then compare against the text. `crates/axeyum-lean-kernel/examples/
probe_add_structure.rs` exists as the worked example of exactly this technique
(built the same day to settle a printer-versus-defeq question for a different
bug), and `docs/reference/examples.md` catalogs it.

Applied here, in the order that settles it:

1. **Ask the kernel, not the text.** The reconstructor calls
   `require_infers_false(&mut ctx, proof)` before it renders anything
   (`crates/axeyum-solver/src/reconstruct/quant_bv_instance_set_lean.rs`) —
   `Kernel::infer` on this `ExprId`, required to yield `False`. The offending
   node is structurally an `App` spine
   `Or.rec a b motive m₁ m₂ t`: **six** arguments, all explicit, no binders left
   over. That is what the kernel accepted, and it is well typed.
2. **Ask Lean what the text means** (below): the module says something else.
3. **Change only the renderer and re-ask.** The same `ExprId` graph, printed by
   the fixed writer, is accepted. A reconstruction defect cannot be repaired by a
   renderer-only diff, so this closes it.

Now look at the *definition* the failing name refers to:

```
1651:def axeyum_proof_share_149 :=
1652:  @Or.rec axeyum_proof_share_69
1654:def axeyum_proof_share_150 :=
1655:  axeyum_proof_share_149 axeyum_proof_share_33
```

`Or.rec` takes six arguments. The writer hoisted a **one-argument prefix** of
that spine into its own `def`. Ask Lean what that `def`'s type is:

```lean
prelude
inductive Or (x0 : Prop) (x1 : Prop) : Prop where
  | inl : ((x2 : x0) -> Or x0 x1)
  | inr : ((x2 : x1) -> Or x0 x1)
axiom P : Prop
def s := @Or.rec P
#check s
```

```
s {x1 : Prop} {motive : Or P x1 → Prop} (inl : ∀ (x2 : P), motive ⋯)
  (inr : ∀ (x2 : x1), motive ⋯) (t : Or P x1) : motive t
```

There it is. Lean makes an inductive's **parameters** and a recursor's
**motive** implicit. `@` suppresses that insertion *for the application it is
written on*; it does not survive being cut in half. The hoisted `def` inherits
`{x1 : Prop} {motive : …}` as leading **implicit** binders, so the *bare*
reference `axeyum_proof_share_149 axeyum_proof_share_33` re-inserts
metavariables for both and type-checks the Prop `axeyum_proof_share_33` against
the `inl` minor premise. That is precisely the reported error, argument for
argument.

Symptom (2) is the cascade, not a second defect: a `def` whose body fails to
elaborate never enters the environment, so every later reference to it is an
unknown identifier. `axeyum_proof_share_160`'s body is at line 1685, which is
error #4 in the same run.

So: **printer defect.** The structural spine has six explicit arguments and
infers `False`; the text splits that spine across a `def` boundary that Lean
reads as three implicit binders plus a minor premise. The mismatch is entirely
in the rendering, and the minimal Lean witness above pins the mechanism, with
its own positive control: `def s := @Or.rec P; def s2 := @s Q; …` type-checks,
so what fails is specifically the *bare* reference, not the hoisting.

No fact and no ADR are owed: nothing our kernel accepted was ill-typed. Had step
1 come back the other way — `infer` succeeding on a term Lean calls ill-typed —
the correct move would have been to stop before changing any kernel behaviour,
report it, and record a fact plus an ADR. It is worth writing down that the
structural check is what makes that a decision rather than a guess.

## The fix

`crates/axeyum-lean-kernel/src/lean_pp.rs` —
`Kernel::hoisting_exposes_implicit_binders`, consulted by both arms of
`compact_share_candidates` (the repeated-node arm and the chunk-cut arm):

> Never hoist an application node whose spine head is a `Const` in `at_consts`
> and which is **under-applied**.

`at_consts` is already exactly the set of constants Lean regenerates for a real
`inductive` — its constructors and its recursor — and is already the reason the
writer prints `@` on them. Everything else the writer emits is an `axiom`/`def`
whose type it rendered itself, with every binder explicit, so nothing else can
leak an implicit binder. Saturation is read off the kernel's own declaration
type (`decl_binder_arity`), so the rule needs no Lean-side knowledge of which
binders Lean will make implicit.

Deliberately, the rule excludes only *proper prefixes*. The saturated node stays
shareable and its large arguments stay individually shareable, so the chunking
that bounds module size is preserved:

| | lines | bytes |
| --- | --- | --- |
| before | 5431 | 358 036 |
| after | 3693 | 365 769 (+2.2%) |

After the fix Lean exits 0 on that module and reports

```
'axeyum_refutation' depends on axioms: [axeyum.reconstruct.em._400,
 axeyum.reconstruct.hyp._134, axeyum.reconstruct.hyp._137,
 axeyum.reconstruct.prop._129, axeyum.reconstruct.prop._64]
```

— the two query hypotheses, their two atoms, and excluded middle. No `sorryAx`.

## The whole sweep, not just the one family

```
[lean crosscheck:representative] checked 70 of 70 modules … 0 FAILED
[lean crosscheck:full]           checked 163 of 163 modules … 0 FAILED
```

The exhaustive run (`-- --ignored`) is the answer to "is any other family
passing for a reason that would not survive scrutiny": every module of every
family, not one representative each, is read by Lean 4.30.0 and accepted. The
one caveat worth writing down is that `qf_ufbv_finite_pigeonhole` and friends
are *large* modules whose acceptance rests on `set_option maxRecDepth 100000`
being carried inside the module rather than passed on a command line — that is
deliberate (the artifact must be self-contained), but it means a Lean whose
default recursion bound changed would not silently start rejecting them.

## Regression coverage

`crates/axeyum-lean-kernel/tests/real_lean_compact_share_crosscheck.rs`, two
tests, two real-Lean invocations:

* a proof that forces the pre-fix writer to hoist `Or.rec P` — a text assertion
  that needs no Lean binary, plus the module through real Lean;
* a **negative control** that re-introduces exactly the defect by hoisting the
  one-argument prefix into `def axeyum_share_control` and referencing it bare.
  The same binary must reject it, so the pass above is evidence about our
  writer rather than a module Lean would accept however it was written.

Both fail on the unfixed writer (verified by disabling the guard in place):

```
a proper prefix of the `Or.rec` spine was hoisted; Lean re-implicits it
Lean rejected the compact-share module (…/v4.30.0/bin/lean)
test result: FAILED. 0 passed; 2 failed
```

## The gate

The exclusion is gone. `scripts/check-lean-gate.sh` now lists twelve suites
including `lean_crosscheck`, with **no environment variables set at all**:

```
check-lean-gate: real_lean_compact_share_crosscheck   2 test(s),   2 real-Lean check(s)
check-lean-gate: lean_crosscheck                     14 test(s),  70 real-Lean check(s)
check-lean-gate: 12 suites, 49 tests, 112 real-Lean checks (floor 105)
check-lean-gate: OK -- 112 modules/controls were read by a real Lean kernel
```

40 → 112 checks; the floor is raised 35 → 105 with the same ~6% headroom the
previous floor carried.

## Two things found on the way that were not mine

Both are `a5975725f`'s debt — that commit changed what the writer emits and did
not update what pins it. Both were **confirmed against a `git archive HEAD`
snapshot** before being touched, so the attribution is measured, not assumed.

1. `lean_pp::tests::renders_self_contained_module` asserted
   `module.contains("axiom False : Prop")`. Since every reachable inductive is
   emitted as a real `inductive`, it renders `inductive False : Prop where`.
   The only failing test in `axeyum-lean-kernel` (248 passed / 1 failed) —
   on HEAD, with my change reverted.
2. All 15 `crates/axeyum-solver/tests/fixtures/lean-modules/*.lean` byte-stability
   fixtures were stale: 7 `reconstruct::tests::*_is_byte_stable` failures on
   pristine HEAD. Re-blessed with `AXEYUM_BLESS_LEAN_FIXTURES=1` and re-checked
   through real Lean (`lean_module_fixtures`: 15 fixtures + 1 mutation control).
   Every changed line is `axiom … → inductive …` or `X.rec → @X.rec`; the diff
   contains **zero** `proof_share` lines, i.e. none of it is mine.
3. Four `(length, fnv1a)` pins over generated modules — `quant_affine_growth_lean`,
   `quant_counterexample_cover`, `quant_eq_partition_lean`, `quant_residue_lean` —
   likewise. Three of the four produce **byte-identical** output with and without
   my change (79 801 / 51 989 / 33 339); the fourth is 513 bytes *smaller* with
   it. Re-pinned, and — because two integers cannot distinguish "the printer
   improved" from "the printer broke", which is the reason this repo replaced
   that pattern with fixtures — each module was dumped and put through Lean
   4.30.0 first: all four accepted, `#print axioms` reporting only ledger axioms
   (`Int.add_assoc`, `Int.euclidean_decomposition`, …) and the query hypotheses,
   no `sorryAx`. The new numbers are checked, not merely blessed.

One further scrutiny pass, since "does any other family pass for a bad reason" is
not answered by an exit status: across the 174 exported modules on this box, none
declares an `axiom … : False` (which would make the refutation vacuous), and
every refutation module's goal is literally `theorem axeyum_refutation : False`.
The non-`axeyum.reconstruct.*` axioms that appear — `Int.add_assoc`,
`Int.left_distrib`, `Int.add_le_add`, `Int.add_lt_add_of_le_of_lt` — are all
`external-assumption` / `retained` rows in `docs/plan/generated/lean-axiom-ledger.md`
with SHA-256 bindings, so they are a declared trusted surface rather than a
surprise.

## A note on where the gates were run

The shared checkout would not build: another lane's in-flight `axeyum-cas` edits
leave `axeyum-solver` and `axeyum-cas` failing to compile (`missing field
`order``). Every gate here was therefore run against a `git archive HEAD`
snapshot with this lane's files copied in, extracted with `tar --touch` for the
mtime reason CLAUDE.md documents. `/tmp` is a 62 GB tmpfs with a quota that a
cold `target/` exhausts, so the snapshot lives under `~/.cache`.
