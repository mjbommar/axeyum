# nat_prelude extraction — lab notebook (append-only)

Task: extract generic Nat arithmetic + Eq combinators from
crates/axeyum-lean-kernel/tests/rado_shell_arithmetic.rs into a reusable
`nat_prelude` module in axeyum-lean-kernel. Zero axioms. Negative controls.

2026-08-12T20:04:36-04:00
start: read source material

## 2026-08-12T20:07 baseline
`cargo test -p axeyum-lean-kernel --test rado_shell_arithmetic` -> **9 passed**, 0 failed
(count confirmed nonzero; build was already warm).

## 2026-08-12T20:10 design decisions
- Namespace: declare everything under the EXISTING `Nat` name root (`logic.nat`),
  i.e. `Nat.add`, `Nat.mul`, `Nat.pow`, `Nat.zero_add`, ..., `Nat.le`.
  Reason: `lean_pp::render_name` remaps the ROOT segment `Nat` -> `AxNat`, so the
  Lean exporter emits `AxNat.add` and cannot shadow real Lean's builtin `Nat.add`
  (verified in output below). Top-level names (`add`) would have collided with
  `int_prelude`'s axiomatized `add`.
- API shape: `build_nat_prelude(&mut Kernel) -> NatPrelude` (names only, matching
  int_prelude/arith_prelude idiom) PLUS a `NatOps` trait carrying the generic
  proof machinery as PROVIDED methods over two required accessors
  (`kernel()`, `nat_state()`), plus `NatState` and a ready-made `NatDev<'k>`.
  Reason: the rado closures are `&dyn Fn(&mut Dev, ExprId) -> ExprId` and call
  BOTH generic ops (`d.add`) and rado-local ops (`d.geo`). A helper struct that
  borrows/owns the kernel cannot express that; an extension trait lets `Dev` keep
  `geo`/`shellT` as inherent methods and inherit the rest, so every proof script
  in rado_shell_arithmetic.rs survives VERBATIM. That is what makes the
  extraction auditable.
- AXIOM CONSIDERED AND REJECTED: none. Nothing needed one. The candidate that
  might have (an ordering relation) is a real indexed inductive with a
  kernel-generated recursor, so `zero_le`/`le_trans`/`le_succ_succ`/
  `le_add_right` are proved. Nat.le.rec's motive is Prop-valued and the recursor
  is universe-monomorphic (`const_(le_rec, vec![])`).

## 2026-08-12T20:14 first compile of src/nat_prelude.rs
`cargo check -p axeyum-lean-kernel` -> clean on the FIRST attempt (0.88s).

## 2026-08-12T20:15 first run of src/nat_prelude/nat_prelude_tests.rs
`cargo test -p axeyum-lean-kernel --lib nat_prelude` -> **7 passed** (199 filtered out).
One warning: unused `mut` on a Fixture binding; fixed by dropping `mut`.
Every proof term was accepted by the kernel on the first attempt (no rejections
to debug) — the transcription from the rado development was faithful.

### Verbatim negative-control rejections (8/8), captured with --nocapture
NC1 swapped lemma arguments (`mul_assoc b a b` for a `mul_assoc a b b` goal):
  DeclarationValueMismatch
    declared : ((x0 : AxNat) -> ((x1 : AxNat) -> ((Eq.{1} AxNat) ((AxNat.mul ((AxNat.mul x0) x1)) x1)) ((AxNat.mul x0) ((AxNat.mul x1) x1))))
    inferred : ((x0 : AxNat) -> ((x1 : AxNat) -> ((Eq.{1} AxNat) ((AxNat.mul ((AxNat.mul x1) x0)) x1)) ((AxNat.mul x1) ((AxNat.mul x0) x1))))
NC2 wrong lemma (`add_comm` for a `mul_comm` goal): DeclarationValueMismatch
NC3 omitted induction step (`ih` handed back as the successor case):
  TypeMismatch
    expected : ((Eq.{1} AxNat) ((AxNat.add AxNat.zero) (AxNat.succ _fvar.2))) (AxNat.succ _fvar.2)
    got      : (fun (x0 : AxNat) => ((Eq.{1} AxNat) ((AxNat.add AxNat.zero) x0)) x0) _fvar.2
NC4 wrong base case (`refl 1` where `add zero zero = zero` is demanded):
  TypeMismatch
    expected : ((Eq.{1} AxNat) ((AxNat.add AxNat.zero) AxNat.zero)) AxNat.zero
    got      : ((Eq.{1} AxNat) (AxNat.succ AxNat.zero)) (AxNat.succ AxNat.zero)
NC5 transposed conclusion (true claim, wrong proof term): DeclarationValueMismatch
NC6 false identity `mul a b = add a b` by refl: DeclarationValueMismatch
NC7 bogus order fact `Le (succ n) n` from `Le.refl n`:
  DeclarationValueMismatch
    declared : ((x0 : AxNat) -> (AxNat.le (AxNat.succ x0)) x0)
    inferred : ((x0 : AxNat) -> (AxNat.le x0) x0)
NC8 reversed concrete bound `Le 3 1` from `le_add_right 1 2`: DeclarationValueMismatch
Each also asserts the rejected name never entered the environment.

axiom population: []  (the_nat_prelude_declares_no_axioms)

## 2026-08-12T20:19 rado_shell_arithmetic.rs rewritten to consume the prelude
Method: an asserting line-splice script (splice.py, kept next to this log) plus
removal of the 7 `lemmas(&mut d);` call sites; `rustfmt --edition 2024` on the
single file (NEVER `cargo fmt`).
`cargo test -p axeyum-lean-kernel --test rado_shell_arithmetic` -> **9 passed**,
same 9 test names, first compile.
FAITHFULNESS EVIDENCE: `diff -u rado_before.rs rado_shell_arithmetic.rs`, from
`theorem_solution_family` to EOF, contains ONLY the six removed
`lemmas(&mut d);` lines. Every Rado proof script is byte-identical.
Diff totals: 81 added lines, 651 removed.

## 2026-08-12T20:20 clippy -D warnings (first pass had 7, as warned)
7 errors: 5x `large_types_passed_by_value` (NatPrelude is 260 bytes > the
256-byte limit; the five private `declare_*` helpers took it by value) and 2x
`type_complexity` on `&dyn Fn(&mut Self, &[ExprId]) -> (ExprId, ExprId)`.
Fixes: helpers take `&NatPrelude` (and copy once inside), module-level
`#![allow(clippy::type_complexity)]` with a written justification (a type alias
cannot mention `Self`; the rado test file already carries the same allow).
2 more surfaced in the test file's `definition_names`/`theorem_names` helpers;
same fix. `cargo clippy -p axeyum-lean-kernel --all-features --all-targets --
-D warnings` -> CLEAN.

## 2026-08-12T20:21 gates
rustfmt --check on the 4 touched files: clean.
RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-lean-kernel --all-features --no-deps: clean.
cargo test -p axeyum-lean-kernel --all-features: every suite green
  (lib 206, rado 9, and all pre-existing integration suites unchanged).
Lib count moved 199 -> 206 (+7 new tests), all NONZERO and named in the output.

Export probe (unchanged test) still renders a real Lean module and the new
definitions come out as `def AxNat.add : ...` — i.e. the namespace choice does
NOT shadow real Lean's builtin `Nat.add`. Verified verbatim in the printed head
of the module.

## 2026-08-12T20:25 commit
f31102a77 — pathspec-only commit of exactly 4 files; `git show --stat` confirms
no other lane's files were swept (axeyum-cnf WIP from another agent was dirty
in the tree throughout and is untouched).

## Axioms considered and rejected: NONE were needed.
The only candidate was the order relation `≤`. It is a real indexed `Prop`
inductive admitted through `add_inductive`, so `zero_le`, `le_succ_succ`,
`le_trans` and `le_add_right` are theorems proved with the kernel-generated
`Nat.le.rec`. Nothing in this prelude is postulated.

## Kernel limits found (findings, not failures)
1. Nothing in the extracted development required a kernel feature that is
   missing. Every proof term was accepted on the first attempt.
2. `le_of_succ_le_succ` (INVERSION of the order) was NOT attempted and is not
   shipped: with only `Nat.le.rec` it needs a `pred`-style motive trick, which
   is library work, not a kernel limit — but it is unwritten, so the shipped
   order fragment cannot go "downward".
3. The prelude's namespace had to be `Nat.*` rather than top-level, because
   `int_prelude` already declares a top-level axiomatized `add`/`mul`. Two
   preludes cannot both be built into one kernel regardless (both call
   `build_logic_prelude`, which is idempotent only on a fresh kernel) — that is
   a pre-existing property, unchanged here.
