# P0 — historical: `axeyum-lean-kernel` admitted a proof of `False`

**Status: CONTAINED by `d26ad887` / ADR-0165; external gate added in
`a10c8cde`.**
**Severity: P0.** At the incident revision, the trusted admission gate accepted
`theorem bad : False`.
**Found: 2026-07-15**, incidentally, while auditing the kernel for the prover track.

Historical reproduction (checkout `2cb298e2`):

```sh
cargo test -p axeyum-lean-kernel --test prop_large_elim_derives_false -- --ignored --nocapture
```

```
inferred type of `Eq.refl Two a` vs ascribed `Eq Two a b`:  def_eq = true
inferred type of the transported term: Const(NameId(20), [])   def_eq(.., False) = true
add_declaration(theorem bad : False) => Ok(())
```

Current regression:

```sh
cargo test -p axeyum-lean-kernel --test prop_large_elim_derives_false
```

The complete former exploit is now active, fails inference at the separating
`Two.rec` function, and is rejected by `add_declaration`. The ignored scratch
probe was removed after its behavior became permanent regression coverage.

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

## The defect (historical)

`inductive.rs:36-37`:

> **Deferred** ... and the `Prop`-subsingleton large-elimination subtleties.
> The motive is always allowed to eliminate into an arbitrary `Sort v` here.

The former `mk_recursor` minted a fresh elimination universe unconditionally
(`inductive.rs:589-595`):

```rust
// A fresh elimination universe parameter `v`, distinct from the
let elim_param = self.fresh_elim_param(uparams);
let elim_level = self.level_param(elim_param);
let elim_sort = self.sort(elim_level);
```

There was no check on the inductive's own sort. A `Prop`-valued inductive with
two constructors therefore received a recursor that eliminated into `Type`.

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

## Why nothing caught it (incident analysis)

Three independent gates should each have caught this, and each was blind for a
different reason. That is the more alarming finding.

1. **The kernel's own tests** (~5k lines) declare enums via a helper hardcoded to
   `Sort 1` — `inductive/inductive_tests.rs:22-24`: *"Declare an enum-style
   inductive `name : Sort 1`"*. Every inductive test is a `Type`. The `Prop` case
   — the only one with a restriction — is untested. The test suite is dense
   exactly where the theory is unconstrained and absent exactly where it is not.

2. **The real-Lean cross-check did not run in CI**, and the original default
   exporter represented inductives, constructors, and recursors as axioms. The
   later `render_lean_module_with_inductives` path could emit flat real
   inductives, but no mandatory job exercised the relevant `Prop` recursor. The
   optional harness therefore skipped on CI and could not distinguish absence
   from success.

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

## Blast radius at discovery

- **Every `Lean unsat` claim** in `bench-results/DOMINANCE.md` rested on this gate,
  including QF_ABV's 85/85 and the datatype chain's "axiom-free, `#print axioms`
  clean" claim in `docs/PARITY-STATUS-AND-PATH.md:56-61`.
- **No wrong solver result was found.** The exploit needs a
  non-subsingleton `Prop` inductive, and reconstruction builds a fixed vocabulary
  (`reconstruct.rs:10-21` — one carrier sort, atoms as axioms). It very likely
  never constructs one. **This is luck, not defense in depth** — nothing in the
  design prevents a future reconstruction route from declaring `Or`-shaped or
  `Exists`-shaped `Prop` inductives, which are precisely the non-subsingletons.
- **The strong fidelity claim was invalid during the affected revisions.** The
  contained boundary now agrees with Lean on this class; that does not turn one
  repaired bug into proof of complete kernel equivalence.

## The fix (landed as ADR-0165)

Restrict the elimination universe in `mk_recursor` when the inductive lands in
`Prop`. Lean's criterion (a `Prop` inductive may eliminate into an arbitrary
`Sort v` iff it is a subsingleton):

- **zero constructors** (`False`, `Empty`) — allowed, vacuously;
- **exactly one constructor**, and every field of it is either (a) itself a proof
  (its type inhabits `Prop`), or (b) among the arguments of the constructor's
  result type (a parameter or index) — allowed;
- **otherwise** — the motive must be `Sort 0`, not a fresh `Sort v`.

This correctly permits `True`, `And`, `Eq`, `Iff`, and the syntactic shape of
`Acc`, and correctly refuses `Or`, `Exists`, and our `Two`. Full `Acc` admission
still awaits the separately deferred recursive-indexed fragment.

Implementation commit `d26ad887` classifies every opened non-parameter field in
its real local context, compares non-proof values against the exact constructor
result arguments, and uses `level_is_nonzero` for conservative polymorphic
result handling. Restricted recursors fix their motive at `Sort 0` and omit the
fresh leading universe parameter; the inductive itself remains admitted.

### Test posture delivered

The fix is small; the reason it was needed is not. The delivered gates are:

1. `prop_large_elim_derives_false.rs` retains the complete derivation and asserts
   both inference and trusted admission reject it.
2. Enum coverage spans both `Prop` and `Type`; computational polymorphic test
   datatypes now use a provably nonzero result instead of accidentally becoming
   propositions at universe zero.
3. Positive profiles cover `True`, `False`, `And`, `Eq`, `Iff`, exact exposed
   indices, and an accessibility-style direct-recursive proof field. `Or`,
   `Exists`, hidden data, nested-only index occurrences, and polymorphic
   multi-constructor results are negative profiles. Full Lean `Acc` remains
   outside the already-deferred recursive-indexed fragment.
4. A generated boundary matrix varies constructor count and proof/data field
   count, so the degenerate class is standing coverage rather than one witness.
5. `a10c8cde` pins Lean 4.30.0 and adds a mandatory CI test that renders real
   flat `inductive` commands, applies Lean's regenerated restricted recursor,
   and depends on its iota rule. `AXEYUM_REQUIRE_LEAN=1` makes absence fail.

## Relationship to the prover track

This is a **hard prerequisite**, and it reframes the track's sequencing.

The prover track began by asking whether to build a construction layer on this
kernel. The answer is now conditional on something more basic: **the kernel is
not yet trustworthy, and its trustworthiness was assumed rather than
established.** A prover would put orders of magnitude more pressure on the kernel
than reconstruction does — arbitrary user- and agent-authored inductives, which
is exactly the surface this bug lives on. Reconstruction's fixed vocabulary is
what has been accidentally protecting us.

The immediate P0 stop is cleared only for this defect. Kernel hardening remains
ahead of new assurance claims: broaden external checking beyond flat inductives,
add recursive-indexed coverage when that fragment lands, and continue treating
negative universe/inductive tests as part of the trusted-core acceptance bar.
