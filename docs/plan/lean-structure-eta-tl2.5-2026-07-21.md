# Lean structure eta — TL2.5 result

Date: 2026-07-21
Status: **complete for the independent kernel's structure-eta rule**

## Result

The independent Rust kernel now recognizes Lean's structure eta during
definitional equality:

```text
s  =?=  C params... (Proj I 0 s) ... (Proj I (n - 1) s)
```

The rule is symmetric and applies only when `C` is exactly saturated and its
parent inductive has exactly one constructor, zero indices, and no recursive
fields. Both expressions must first infer to definitionally equal types, then
every constructor field is compared with the corresponding projection from the
other expression. Eta remains a definitional-equality rule; it is not a WHNF
rewrite.

This closes TL2.5. It does not add a parser, elaborator, new import record, or a
new official dependency root. TL2.4 had already closed the exact projection
root. The next ordered kernel task is TL2.6: replace `Lit::Nat(u128)` with
arbitrary-precision storage before enabling Nat literal typing in TL2.7.

## Eligibility contract

The implementation follows pinned Lean 4.30's `try_eta_struct_core` and
`is_non_rec_structure` boundaries:

1. the eta-expanded side has a constructor constant at its application head;
2. the application has exactly `num_params + num_fields` arguments;
3. the parent inductive has one constructor, zero indices, and is non-recursive;
4. both operands have definitionally equal inferred types; and
5. each field argument is definitionally equal to the matching projection from
   the other operand.

Constructor admission already classifies every supported direct recursive
field. TL2.5 persists their aggregate `is_recursive` bit on the checked
inductive declaration, initially as a rollback-safe placeholder and then as the
post-constructor checked value. Definitional equality therefore consumes
trusted admission metadata instead of guessing from constructor count or
re-scanning unchecked syntax.

The upstream references are the pinned
[Lean 4.30 type checker](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/kernel/type_checker.cpp)
and
[inductive metadata predicate](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/kernel/inductive.cpp).

## Native evidence

`structure_eta.rs` adds seven focused integration cases:

1. a two-field neutral structure rebuilt from both projections is
   definitionally equal in both directions and passes declaration admission;
2. under-applying the constructor, duplicating one field, and rebuilding a
   different one-constructor structure all remain false equalities;
3. a zero-field one-constructor structure eta-expands, while an otherwise
   matching two-constructor family is explicitly ineligible;
4. a universe-polymorphic parameterized structure preserves the constructor's
   universe and type parameter;
5. a dependent second field is rebuilt using the prior projection;
6. a one-constructor indexed family is explicitly ineligible even when the
   rebuilt constructor has the same inferred type; and
7. a one-constructor direct-recursive family is explicitly ineligible, with
   the persisted recursion metadata checked.

The existing injected malformed-constructor test was updated to state its
non-recursive metadata explicitly. All prior projection inference/reduction,
inductive, proof-irrelevance, and recursor tests remain green.

## Official-Lean differential gate

`real_lean_structure_eta_crosscheck.rs` runs the same semantic fork through the
pinned official Lean 4.30 binary:

- Lean accepts `AxeyumEtaPair.mk p.left p.right = p` by `rfl`; and
- Lean rejects the mutation `AxeyumEtaPair.mk p.left p.left = p` by `rfl`.

The wrapper stays optional for local environments without Lean and fails closed
under `AXEYUM_REQUIRE_LEAN=1`. The recorded local required run used the exact
Lean 4.30.0 release at commit `d024af099ca4bf2c86f649261ebf59565dc8c622`.
One Lean worker, a 1 MiB thread stack, Lean's 4 GiB memory limit, and the shell's
4 GiB virtual-memory bound keep the gate deterministic on this high-core host.

## Validation

Under the hard 4 GiB shell bound and two Cargo jobs:

- `axeyum-lean-kernel` passes 179 unit tests and 25 integration cases across
  nine integration binaries;
- the new official-Lean required gate passes its positive and rejecting
  modules against pinned Lean 4.30;
- warning-denied all-target kernel Clippy passes;
- the kernel doctest passes with `TMPDIR` redirected into `target/` after the
  shared `/tmp` linker path hit its host disk quota; and
- touched Rust files pass standalone rustfmt.

The workspace-wide formatting gate still reports pre-existing unrelated
`axeyum-bench`/`axeyum-cas` drift. TL2.5 does not rewrite those files.

## Credit boundary

TL2.5 earns native K0 structure-eta and pinned official differential credit. It
does not broaden the exact K1 projection-root population, imply general
Lean-kernel parity, or close TL2.15. The generated seam-fuzz population still
lacks a projection/reduction/eta family, and recursive-indexed, positivity,
quotient, literal, mutual, nested, and reflexive kernel work remains separately
gated.
