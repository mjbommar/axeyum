# 290 — The first contract-matched dispatch: clean import, honest decline

Date: 2026-08-27
Lane: flywheel-1

## Task

Discharge `F:ml430-int-add-modeq-left-ee732b5b` (`Int.add_modEq_left`,
`∀ {n a : ℤ}, n + a ≡ a [ZMOD n]`), the first fact `scripts/fact-frontier.py`
ever selected via a producer contract rather than a registered operation
(`producer-contract-int-modeq-family-v1`, route `kernel-lane`, landed the
same day by the `producer-contracts` lane —
[`docs/plan/status/135-producer-contracts.md`](../plan/status/135-producer-contracts.md),
[`289-producer-contract-admissibility.md`](289-producer-contract-admissibility.md)).
That lane's own status note is explicit about what it did and did not
establish: `selected_fact_id: F:ml430-int-add-modeq-left-ee732b5b` — "genuinely
still `epistemic_status: "open"`, no receipt fabricated." This task is that
receipt's first real attempt.

## Partition check (done first, per brief)

`artifacts/autogenesis/nursery-v1.json` entry for this fact:

```json
{
  "fact_id": "F:ml430-int-add-modeq-left-ee732b5b",
  "partition": "train",
  ...
}
```

**`train`, not `held-out`.** Safe to proceed under ADR-0542. The contract file
itself also states this was checked ("13 open, dependency-ready, all
`nursery-v1.json` partition `train` -- none held-out, checked 2026-08-27"),
and this task's own independent read of the nursery file confirms it.

## What the contract's recipe actually produced

### 1. s5-side adapter (lives on s5, not in this repo)

`/home/mjbommar/lean-import-scale/mathlib4/AxeyumAutogenesisIntAddModEqLeftV1.lean`:

```lean
import Mathlib.Data.Int.ModEq

namespace Axeyum.Autogenesis.Statement.IntModEqFamily

def intAddModEqLeft : Prop :=
  ∀ {n a : ℤ}, n + a ≡ a [ZMOD n]

end Axeyum.Autogenesis.Statement.IntModEqFamily
```

A new, standalone file (not an edit to the shared
`AxeyumAutogenesisIntModEqFamilyV1.lean` four other lanes/episodes may still
be using), matching the pinned source exactly: `Mathlib/Data/Int/ModEq.lean:351`,
`theorem add_modEq_left : n + a ≡ a [ZMOD n] := by simp` under
`variable {m n a b c d : ℤ}` (line 62). Same `encoding:
transparent-definition-of-prop` contract as the sibling refl/symm/trans/comm
adapters: one transparent `Prop` definition, no axiom, theorem, opaque
declaration, or proof value.

### 2. Identity manifest

Confirmed on s5 before doing anything else:

```
mathlib4  HEAD  = c5ea00351c28e24afc9f0f84379aa41082b1188f  (matches manifest)
lean4export HEAD = a3e35a584f59b390667db7269cd37fca8575e4bf  (matches manifest)
```

Compile + export:

```sh
cd /home/mjbommar/lean-import-scale/mathlib4
lake env lean AxeyumAutogenesisIntAddModEqLeftV1.lean \
  -o .lake/build/lib/lean/AxeyumAutogenesisIntAddModEqLeftV1.olean
lake env ../lean4export/.lake/build/bin/lean4export \
  AxeyumAutogenesisIntAddModEqLeftV1 -- \
  Axeyum.Autogenesis.Statement.IntModEqFamily.intAddModEqLeft \
  > int-add-modeq-left.ndjson
```

Result: exit 0, zero-byte stderr, 6,138 NDJSON records (32 `thm` records with
proof bodies, 105 `def`, 22 `inductive`, 0 `ax`). SHA-256
`db2b29da51d66b37aba70021658bfda288b0c5a7d01a84f8d5de7fff5d3122c8`, verified
identical after `scp` to this worktree before any further processing.

### 3. Import

```sh
./target/debug/examples/statement_adapter_import \
  int-add-modeq-left.ndjson \
  Axeyum.Autogenesis.Statement.IntModEqFamily.intAddModEqLeft
```

```
STATEMENT_ADAPTER_IMPORT|target=...intAddModEqLeft|goal_sha256=7ace82a88ff8785bea25c9f415790982d38bb119abfa3e3adbbb2fce1cbfa40a|target_content_sha256=3f26ee17f803fe3f9f9ff99708910a31c43981072fc4200088b6cf7ef9a2c9e7|dependencies=5|declarations=208|axioms=0|lean=4.30.0
GOAL|((n : Int) -> ((a : Int) -> Int.ModEq n (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAdd) n a) a))
```

**Clean.** 208 declarations independently admitted, 0 axioms. This
independently re-confirms docs/autogenesis/241/242's "Outcome, the same day"
section: the `Nat.div_rec_lemma` cascade that used to block every fact whose
statement mentions `%` on ℤ/ℕ is still bridged for a target neither of those
documents tested. The goal matches the fact's `formal.statement` exactly.

### 4. Producer

```sh
./target/debug/examples/modeq_family_operation \
  int-add-modeq-left.ndjson \
  Axeyum.Autogenesis.Statement.IntModEqFamily.intAddModEqLeft
```

```
Error: "producer declined: terminal goal is not an Eq/Iff shape this
schema's refl/symm/trans/Iff.intro combinators can close"
```

**`DeclineReason::TerminalNotClosed`.** This is the honest, correct outcome,
not a bug in the checker and not a reason to try harder against the same
tool. `propose_modeq_family` peels the two leading binders (`n`, `a`) into
free variables, retains them as candidate "hypotheses" (neither is
Eq-shaped, so neither helps), whnf-unfolds the terminal goal — `Int.ModEq n
(n+a) a` → `(n+a) % n = a % n` — and then only knows `Eq.refl`/`Eq.symm`/
`Eq.trans`/`Iff.intro` over *already-given* equalities. There is no
hypothesis to symm/trans over here (the fact is unconditional), and
`def_eq((n+a) % n, a % n)` does not hold for free `n, a` — computing it
requires an actual Euclidean-division identity, not a delta-unfold. Mathlib's
own proof is `:= by simp`, not `rfl`, which independently confirms this was
never a definitional identity.

Contrast with the four family members this exact producer already proves
(`int-modeq-{refl,symm,trans,comm}`, docs/autogenesis/242): every one of
those manipulates an *already-supplied* `ModEq`-typed hypothesis via
symm/trans/Iff.intro. `add_modEq_left` supplies none — it has to *derive* a
new equality, which is a strictly different (and strictly harder) proof
obligation this schema was never built to discharge. The producer's own
module doc says as much: it targets "the **definitional-equivalence
family**" — lemmas that are plain Eq/Iff combinators *given* the ModEq
hypotheses already at hand. `add_modEq_left` is a modular-arithmetic identity
family member, not a combinator-over-hypotheses member, despite sharing the
same `[ZMOD n]` surface shape the contract matches on.

## Is it already provable from this kernel's own `Int.ModEq` family?

No, and the reason is documented and load-bearing. This kernel's own
`Int.ModEq.add_left` / `Int.ModEq.add_right`
(`crates/axeyum-lean-kernel/src/int_prelude/modeq.rs`) are:

```
Int.ModEq.add_right : ∀ n a b c, 0 < n → ModEq n a b → ModEq n (a+c) (b+c)
Int.ModEq.add_left  : ∀ n a b c, 0 < n → ModEq n a b → ModEq n (c+a) (c+b)
```

both routed through `modEq_iff_dvd`, which itself requires `0 < n`. Mathlib's
`add_modEq_left` is **unconditional** — true for `n = 0` (trivially, `0 + a =
a`) and for negative `n` too (Euclidean `emod` is well-defined and periodic
regardless of sign). That makes it strictly stronger than anything
`modEq_iff_dvd` supports today, so it cannot be instantiated from the
existing declaration without new case-splitting on the sign of `n` — new
kernel-level work.

This exact `0 < n` gap is not a fresh discovery: two sibling facts already
carry this finding in their `notes` field —
`F-ml430-int-modeq-one-01d9de39.json` and
`F-ml430-int-modeq-neg-d6ff57b6.json` — both naming "a natAbs-based bound on
`emod`'s magnitude generalising `emod_lt_of_pos`" as the single missing
ingredient, and both noting `int_prelude/division.rs`'s own header already
flags it as not yet built. `F:ml430-int-add-modeq-left-ee732b5b` is a third
sibling blocked by the identical gap, and its `notes` field now says so (see
below), so a future lane does not have to re-derive this.

`crates/axeyum-lean-kernel/src/` is out of scope for this lane, so building
that generalization is not attempted here.

## Disposition

**`epistemic_status` stays `open`.** No evidence was attached (the fact
schema's semantic rule that an `open` fact must carry no evidence is
respected — nothing here is a proof). No operation was registered in
`artifacts/autogenesis/operations.json`: per ADR-0602 and
[doc 288](288-admission-precedes-registration.md)'s own finding, "admission
precedes registration" — fabricating a `proved` status or a registry entry
from a shape match alone, with no actual kernel-checked proof behind it, is
exactly the checker-that-cannot-fail defect this project has repeatedly found
and repaired elsewhere. A contract match is a capability claim, never a
completion claim (that is the whole reason ADR-0602 built a *separate*
artifact for it rather than reusing the operation registry).

`artifacts/autogenesis/mathlib-int-add-modeq-left-decline-v1.json` records
the full manifest (adapter, identity, import result, producer decline,
kernel comparison) in the repository's established `<name>-decline-v1.json`
format (`mathlib-int-fib-eq-zero-exact-decline-v1.json` and siblings).
`F-ml430-int-add-modeq-left-ee732b5b.json`'s `notes` field records the same
finding directly on the fact, in the style
`F-ml430-int-modeq-one-01d9de39.json` already established, so the next lane
selecting this fact (or a sibling with the same `0 < n` gap) is not reading
it as merely unattempted.

## What the recipe did NOT automate — the honest accounting ADR-0602 asked for

This is the first real exercise of a contract-driven dispatch end to end, so
here is exactly where a human (this lane) supplied judgment a machine could
not have, honestly itemized:

1. **Recognizing which family member this is.** The contract matches on
   `fragment: Int` + `statement_contains: "[ZMOD "` — a purely syntactic
   test. It says nothing about whether the target is a *combinator-over-
   hypotheses* fact (which this producer handles) or a *derive-a-new-
   arithmetic-identity* fact (which it does not). Distinguishing those two
   required reading the goal's logical shape (counting hypotheses, checking
   whether the terminal equality is already witnessed) — not something the
   contract's `statement_contains` predicate can see. This is not a gap in
   *this* contract specifically; any shape predicate expressive enough to
   catch it would need to symbolically evaluate the producer's own search,
   which is circular (you'd have to run the producer to know if the contract
   applies).
2. **Locating and writing the s5 adapter.** The contract names a `reference`
   (`modeq_family_operation.rs`) but not a template Lean file; I found the
   sibling adapter, matched its style, and had to independently read the
   pinned Mathlib source (`Mathlib/Data/Int/ModEq.lean:351`, and the
   `variable` block at line 62) to get the exact implicit-binder shape right
   (`{n a : ℤ}`, not `(n a : ℤ)` — getting this wrong would silently change
   the imported goal's type).
3. **The `-o` flag.** `lake env lean <file>.lean` alone does *not* write a
   persistent `.olean` (confirmed empirically: the first `lean4export`
   attempt failed with "unknown module prefix" because nothing had been
   written to `.lake/build/lib/lean/`). This is a documented Lean/Lake
   behavior, not project-specific, but nothing in this repository's docs
   said so and I had to diagnose it from the error message and the sibling
   file's already-built `.olean` path.
4. **Interpreting `DeclineReason::TerminalNotClosed` as a genuine negative
   result rather than a bug to route around.** The natural next move for an
   agent under pressure to "discharge the fact" is to weaken the checker,
   add a special case for this one lemma, or borrow a sibling theorem to
   force a pass. All three are exactly the defects CLAUDE.md's Hard Rules
   and Gotchas sections repeatedly flag (a checker that cannot fail;
   registering an operation whose admission claims something false). Judging
   that the correct response to an honest decline is to *record* it, not
   *engineer around* it, was a human call informed by reading this project's
   own prior incidents (doc 288 in particular), not something derivable from
   the contract or the error message alone.
5. **Connecting the decline to the pre-existing `0 < n` gap.** The contract
   and the producer's decline message say nothing about `int_prelude`'s
   conditional `ModEq.add_left`/`add_right`. Finding that this is the *same*
   gap two sibling facts already diagnosed required grepping the kernel
   source, reading `modeq.rs`'s inline documentation, and cross-referencing
   two other facts' `notes` fields — a research step outside anything the
   recipe or the contract specifies.
6. **The decision not to attempt the kernel-level fix.** A genuinely
   complete automation would either (a) know its own boundary and stop
   cleanly at "needs `crates/axeyum-lean-kernel/src/` work, out of scope," or
   (b) extend the producer if that extension is truly general. Recognizing
   which of those two applies — and that a natAbs-based `emod` magnitude
   bound is real, non-trivial mathematical construction rather than a
   "genuinely family-generic extension" of the *existing* Eq/Iff schema — is
   a scoping judgment, not a mechanical one.

None of the above is a criticism of the contract or the producer; both did
exactly what they claim to do (`producer-contract-int-modeq-family-v1`
"asserts only that the shape is dischargeable via `kernel-lane`, never that
any instance has been attempted or proved," and `modeq_family`'s decline is a
typed, honest, first-class outcome by design). The measurement this task
asked for is that a shape match plus a clean import plus a real producer run
still needed six distinct human judgment calls before landing on the correct,
honest disposition — none of them exotic, all of them real.

## Verification run

```
python3 scripts/validate-facts.py
  776 facts checked, 0 errors  (unchanged distribution: open=176, proved=591, ...)
python3 scripts/validate-autogenesis-operations.py
  (unchanged: no operation added)
python3 scripts/check-autogenesis-holdout-isolation.py
  (unchanged: no held-out fact touched)
```

No file under `crates/axeyum-lean-kernel/src/`, `crates/axeyum-cas/`,
`scripts/fact-frontier.py`, `scripts/validate-producer-contracts.py`, any
producer contract instance, `artifacts/import-backlog.json`, or
`python/axeyum/agent/` was touched.
