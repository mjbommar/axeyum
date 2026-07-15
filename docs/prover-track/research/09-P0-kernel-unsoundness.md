# P0 — `axeyum-lean-kernel` admits a proof of `False`

**Status: OPEN, reproduced, exploit committed.**
**Severity: P0.** The trusted admission gate accepts `theorem bad : False`.
**Found: 2026-07-15**, incidentally, while auditing the kernel for the prover track.

Reproduce:

```sh
cargo test -p axeyum-lean-kernel --test prop_large_elim_derives_false -- --ignored --nocapture
```

```
inferred type of `Eq.refl Two a` vs ascribed `Eq Two a b`:  def_eq = true
inferred type of the transported term: Const(NameId(20), [])   def_eq(.., False) = true
add_declaration(theorem bad : False) => Ok(())
```

The `#[ignore]` exists only so the exploit does not break other lanes' `just check`
in this shared checkout. It is not a judgement about importance.

## This is not a Lean-compatibility complaint

Worth stating up front, because the project's direction is Lean-*compatible*, not
Lean-*imitating*, and this finding does not depend on that choice.

The kernel implements **proof irrelevance** (`tc.rs:729-743`) and **impredicative
`Prop`** (`Sort 0`). In *any* type theory with those two features, permitting a
non-subsingleton `Prop` to eliminate into a larger universe is inconsistent. Lean
restricts large elimination to subsingletons for exactly this reason; so does
Rocq. This is a property of the theory we actually implemented, not a
divergence from someone else's design.

If we later choose a *different* theory, the constraint changes — but then the
change must be deliberate and the two features must be re-examined together. What
is not available is keeping proof irrelevance, keeping impredicative `Prop`, and
keeping unrestricted large elimination.

## The defect

`inductive.rs:36-37`:

> **Deferred** ... and the `Prop`-subsingleton large-elimination subtleties.
> The motive is always allowed to eliminate into an arbitrary `Sort v` here.

`build_recursor` mints a fresh elimination universe unconditionally
(`inductive.rs:589-595`):

```rust
// A fresh elimination universe parameter `v`, distinct from the
let elim_param = self.fresh_elim_param(uparams);
let elim_level = self.level_param(elim_param);
let elim_sort = self.sort(elim_level);
```

There is no check on the inductive's own sort. A `Prop`-valued inductive with two
constructors therefore receives a recursor that eliminates into `Type`.

The deferral was recorded as a *completeness* gap — a subtlety not yet handled.
It is a **soundness** gap. Everything else on the deferred list at
`inductive.rs:30-37` (recursive-indexed, reflexive, nested, mutual) is rejected
with an explicit error. This one is not rejected; it is silently admitted.
**Deferral by rejection is safe; deferral by permission is not.** That asymmetry
is the actual lesson.

## The derivation

1. `Two : Prop` with constructors `a`, `b`. Proof irrelevance gives `a ≡ b`
   — legitimate, and confirmed: `def_eq(a, b) = true`.
2. Large elimination (**the illegal step**) builds `f : Two → Answer` where
   `Answer : Type` has constructors `yes`, `no`. Iota gives `f a ≡ yes`,
   `f b ≡ no`. Confirmed: the recursor admits at `Sort 1` and both sides reduce.
3. `h : Eq Two a b := Eq.refl Two a` typechecks *because* `a ≡ b`. Confirmed:
   `def_eq(Eq Two a a, Eq Two a b) = true`.
4. `D : Answer → Prop` with `D yes ≡ True`, `D no ≡ False` — legitimate (`Answer`
   is a `Type`, so this elimination is unrestricted for good reason).
5. Transport `trivial : True` along `h` with motive `fun idx _ => D (f idx)`.
   Result: a term of type `D (f b) ≡ False`.
6. `add_declaration(Theorem { ty: False, value: <that term> })` → `Ok(())`.

Note that steps 1, 3, 4, 5 are all *correct*. `Eq` is a genuine subsingleton (one
constructor, no non-parameter fields), so its own large elimination is legitimate
and the exploit does not depend on the bug twice. The single illegal step is (2).

## Why nothing caught it

Three independent gates should each have caught this, and each was blind for a
different reason. That is the more alarming finding.

1. **The kernel's own tests** (~5k lines) declare enums via a helper hardcoded to
   `Sort 1` — `inductive/inductive_tests.rs:22-24`: *"Declare an enum-style
   inductive `name : Sort 1`"*. Every inductive test is a `Type`. The `Prop` case
   — the only one with a restriction — is untested. The test suite is dense
   exactly where the theory is unconstrained and absent exactly where it is not.

2. **The real-Lean cross-check does not run in CI**, and would not have caught it
   anyway. There is no `lean` on PATH and no `elan` in `.github/`; the
   `AXEYUM_LEAN_BIN` tests skip-and-pass, which is indistinguishable from passing.
   And even with Lean present, `lean_pp.rs:139-144` emits inductives,
   constructors, and **recursors as axioms** — so Lean re-checks *our generated
   recursor's use*, never its *generation*. The one gate positioned to catch a
   bad recursor is the one that takes the recursor on trust.

3. **The certificate/reconstruction discipline** is orthogonal. It ensures a
   proof term is checked *by this kernel*. If the kernel is unsound, the
   discipline faithfully checks nonsense. "Untrusted search, trusted checking"
   only pays if the trusted part is trustworthy; the whole architecture routes
   its assurance through this component.

The common cause: **the kernel is trusted by assertion rather than by
adversarial test.** ADR-0036:50-52 states the obligation — "the entire value is
that this core accepts exactly what Lean's kernel does" — and ADR-0036:62-65
names the risk precisely: "a wrong type-checker would wrongly accept proofs."
The obligation was stated and then never tested negatively.

## Blast radius

- **Every `Lean unsat` claim** in `bench-results/DOMINANCE.md` rests on this gate,
  including QF_ABV's 85/85 and the datatype chain's "axiom-free, `#print axioms`
  clean" claim in `docs/PARITY-STATUS-AND-PATH.md:56-61`.
- **In practice, probably no wrong result has shipped.** The exploit needs a
  non-subsingleton `Prop` inductive, and reconstruction builds a fixed vocabulary
  (`reconstruct.rs:10-21` — one carrier sort, atoms as axioms). It very likely
  never constructs one. **This is luck, not defense in depth** — nothing in the
  design prevents a future reconstruction route from declaring `Or`-shaped or
  `Exists`-shaped `Prop` inductives, which are precisely the non-subsingletons.
- **The claim that must be withdrawn is the strong one**: axeyum's kernel does
  *not* currently "accept exactly what Lean's kernel does." It accepts strictly
  more, including `False`.

## The fix

Restrict the elimination universe in `build_recursor` when the inductive lands in
`Prop`. Lean's criterion (a `Prop` inductive may eliminate into an arbitrary
`Sort v` iff it is a subsingleton):

- **zero constructors** (`False`, `Empty`) — allowed, vacuously;
- **exactly one constructor**, and every field of it is either (a) itself a proof
  (its type inhabits `Prop`), or (b) among the arguments of the constructor's
  result type (a parameter or index) — allowed;
- **otherwise** — the motive must be `Sort 0`, not a fresh `Sort v`.

This correctly permits `True`, `And`, `Eq`, `Iff`, `Acc` and correctly refuses
`Or`, `Exists`, and our `Two`.

Sizing: **S/M.** The criterion is local to recursor generation; the universe-level
plumbing (`fresh_elim_param`, `level_zero`) already exists. The hard part is not
the code, it is the test posture.

### The test posture is the real deliverable

The fix is small; the reason it was needed is not. Minimum bar:

1. Invert `prop_large_elim_derives_false.rs` into a negative test: `Two.rec` must
   not admit at `Sort 1`.
2. Parameterize the enum test helper over the sort level and run the entire
   existing inductive suite at `Prop` as well as `Type`.
3. Positive tests that the legitimate subsingletons (`True`, `False`, `And`, `Eq`,
   `Acc`) *retain* large elimination — a fix that over-restricts silently breaks
   the existing `Eq`-based reconstruction routes.
4. A standing **"kernel accepts `False`" fuzz/negative class**, in the spirit of
   the existing hard rule that partial operators carry a fuzz seed-class
   generating the degenerate argument. The kernel's degenerate arguments are
   `Prop` inductives, universe edge cases, and `Sort 0`/`Sort 1` boundaries.
5. Make the real-Lean cross-check a *gate* rather than a skip-and-pass, and
   extend `lean_pp` to emit inductives via Lean's `inductive` command rather than
   as axioms (`lean_pp.rs:125-128` already tags this "export slice TODO"), so
   Lean actually re-checks generation.

Without (4) and (5), the next kernel gap is found the same way this one was: by
someone deciding to look.

## Relationship to the prover track

This is a **hard prerequisite**, and it reframes the track's sequencing.

The prover track began by asking whether to build a construction layer on this
kernel. The answer is now conditional on something more basic: **the kernel is
not yet trustworthy, and its trustworthiness was assumed rather than
established.** A prover would put orders of magnitude more pressure on the kernel
than reconstruction does — arbitrary user- and agent-authored inductives, which
is exactly the surface this bug lives on. Reconstruction's fixed vocabulary is
what has been accidentally protecting us.

So: kernel hardening is P0 and precedes any prover phase. It is also *cheap*
relative to the prover, and it is valuable **whether or not the prover is ever
built** — P3.6/P3.7 need it regardless. That makes it the rare item that is
unconditionally worth doing, and the plan should treat it that way rather than as
prover-track scope.
