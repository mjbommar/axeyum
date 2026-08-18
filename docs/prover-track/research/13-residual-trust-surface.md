# The residual trust surface, measured

**What must a third party believe to accept an Axeyum result?** Written
2026-08-17 by `agent-kernel-trust`. Everything below is derived or measured;
where it is not, it says so.

Gödel's limit means some checker is believed rather than checked, so
*"untrusted fast search, trusted small checking"* reduces to three questions:
how small is the thing that must be right, how well specified is it, and what
corroborates it. This note answers all three, and is honest about the one that
is still open.

---

## 1. How small: 5,148 lines, derived not estimated

`scripts/check-kernel-trusted-core.py` (gated in both `just check` and
`scripts/check.sh`) derives the trusted core rather than listing it. The
derivation has one anchor: a declaration can only come into existence through
`Environment::insert_unchecked`, which is `pub(crate)`. Find its non-test call
sites; their enclosing functions are the **admission gates**; the trusted core
is the forward call-graph closure from those gates.

Callers are deliberately *excluded*. That is what a kernel is for: a prelude, a
solver, or a reconstruction pass may be arbitrarily wrong and the gate re-checks
it. This is why 16k lines of `nat_prelude/` are **content, not checker**.

Measured 2026-08-17:

| | |
|---|---|
| admission gates | **4** |
| trusted functions | **244 of 794** |
| trusted function-body lines | **5,148 of 34,468** |
| files contributing any trusted line | **9 of 44** |

Per file (trusted / all function lines):

```
  1936 /  2498  inductive.rs      683 /  995  lib.rs        32 / 891  lean_export.rs
  1644 /  1673  tc.rs             131 /  175  env.rs         3 /   3  level.rs
   605 /   638  quotient.rs        92 /  104  expr.rs        3 /   3  name.rs
```

Three things the previous hand estimate ("roughly 9.4k lines") got wrong:

1. **`lean_export.rs` is not interop-only.** `Kernel::is_k_like_inductive`
   (32 lines) lives there and is reached from `k_like_major` → `reduce_rec` →
   `whnf` → `def_eq`. K-like reduction is a soundness-critical iota rule:
   believing a family is K-like licenses reducing a recursor application whose
   major premise is not a constructor. It is on the trusted path, in the file
   filed as "trusted only for the Lean crosscheck".
2. **There are four admission gates, not three.**
   `restore_nested_inductive_group` inserts declarations directly, after the
   nested-inductive expansion has been checked under temporary names. It has
   carried adversarial coverage since round 4 (below); through round 3 it had
   none.
3. **Whole files are not trusted.** `tc.rs` contributes 1,644 of its 1,673
   function-body lines but `lib.rs` only 683 of 995 and `lean_export.rs` 32 of
   891. Counting files overstates the surface by ~80%.

The call graph over-approximates (loose method resolution), so **5,148 is an
upper bound** — the safe direction for a trust claim. Its blind spots are trait
dispatch (`Display`, `Index`) and function values passed without a call; the
guard that survives a missed edge is the pinned *set of files*, not the count.

Five guards, each with a negative control in
`scripts/tests/test_check_kernel_trusted_core.py`, and each driven to failure:
a new `insert_unchecked` call site; a `pub` `Environment` mutator; growth past a
ceiling; a file joining or leaving the trusted set; and floors, because a
scanner that goes blind reports a beautiful clean zero.

**This does not say the 5,148 lines are correct.** Nothing static can. It says
what the question is about, and stops the answer drifting silently.

---

## 2. What corroborates it: an adversarial differential, which found a defect

Before 2026-08-17 every real-Lean check ran the *agreement* direction — we
render a term we chose to emit, Lean accepts it, 77 families pass. That
corroborates the terms we emit. It cannot corroborate the checker: a kernel that
accepted everything would pass all 77.

`crates/axeyum-lean-import/tests/real_lean_wire_differential.rs` runs the
soundness direction. It exports a checked development as an official
`lean4export` NDJSON 3.1.0 stream, damages the stream in ways that stay
structurally valid (every index still points at a real, earlier table entry), and
hands the **identical bytes** to both kernels — ours via
`axeyum_lean_import::import_ndjson`, Lean's via
`scripts/lean/replay-lean4export.lean` → `addDeclCore` from
`mkEmptyEnvironment`. Same bytes, so no argument is needed that two renderings
agree; `addDeclCore`, so no elaborator, no implicit-argument inference, no
coercions, no `Init`.

Only one outcome is a failure: **ours accepts and Lean rejects**.

First run, 92 mutants: 60 genuine Lean kernel rejections, 0 unreadable,
**1 violation**. `Acc.inv`'s proof with one application argument rewired was
admitted here and refused by Lean with `application type mismatch: @Acc Prop`.
Ten different values in that argument position were all accepted, which is what
"never checked" looks like from outside.

**Cause.** `Kernel::check_core` (`axeyum-lean-kernel/src/tc.rs`) has a
bidirectional fast path: checking a `Lam` against an expected `Pi` compared the
two domains with `def_eq_core` and recursed into the body — bypassing
`infer_lambda`, and with it the domain's `infer_sort_of`. `def_eq_core` reduces,
so an ill-typed domain that *beta-reduces* to the expected one was erased before
anything checked it. Minimal case, accepted here and rejected by Lean 4.30.0:

```
h : (True -> True) -> True
theorem t : True := h (fun (_ : (fun (x : Sort 1) => True) trivial) => trivial)
```

Lean's kernel cannot have this bug: it has no bidirectional path at all — it
infers and then `isDefEq`s, and `inferLambda` calls `ensureSortCore`.

Fixed by adding the sort check to the fast path. Permanent regression coverage
in `axeyum-lean-kernel/tests/lambda_binder_domain_must_be_a_type.rs`, with the
well-typed twin as a control; removing the fix fails exactly the soundness test
and leaves the control passing. 306 kernel unit tests and all 39 kernel
integration suites pass with the fix.

**Was it exploitable?** Not demonstrated. The accepted term still reduces to a
well-typed one and the declaration's own type is independently sort-checked, so
no derivation of `False` follows from this alone. The honest statement is: an
ill-typed subterm could sit in a proof this kernel admitted, in a position no
check ever visited. That is the shape an unsoundness has, whether or not this
instance is one — and it is the second time a `def_eq`-erases-the-difference
pattern has bitten this kernel (see `09-P0-kernel-unsoundness.md`).

**Limits of the instrument, stated.** 32 of the 92 mutants were rejected by us
and accepted by Lean. All 32 lie inside `inductive` records, and the replay
script deliberately does not replay the constructors and recursors an inductive
group carries — Lean regenerates them. So Lean's acceptance there is not evidence
about the mutated bytes; those positions are simply never delivered to its
kernel. The suite prints this count rather than asserting on it.

---

## 3. What a third party must still believe

Four things, in descending order of how well we can defend them.

1. **The ~5,254 lines are correct.** Bounded, gated, and corroborated in the
   adversarial direction by a differential against an independent kernel — which
   is the strongest available evidence and is still not a proof.

   **Updated 2026-08-18: four defects, not one.** The first run of one mutation
   family found one — a lambda binder domain checked only for `def_eq`, so an
   ill-typed domain that beta-reduced to the expected one was erased before
   anything checked it. Widening to **51 families / 134 checked mutants** found
   two more, and both were categorical rather than incidental:

   - a declaration's `levelParams` list was **decorative** — nothing compared the
     universe parameters occurring in a term against the ones the declaration
     declares, because inference treats an unbound `Param` exactly like a bound
     one, and `Const(c, us)` substitutes *positionally* for the declared list;
   - the recursor `k` flag was never validated on import, and `k` licenses
     ι-reducing a recursor application whose major premise is not a constructor.

   The first universe fix also **left one violation behind**, because the
   inductive gate type-checks its own group and never routes through
   `check_declaration` — a check placed in a *caller* of an admission gate is
   outside the trusted core, which is exactly what the derived boundary in §1 is
   for.

   **Round 3, same day: a fourth, and it is the third instance of one pattern.**
   The corpus was widened to **66 families over a development that now carries a
   Type-valued structure, a `Nat` literal, an indexed family, a parameterized
   family and a mutual group** — constructs the earlier rounds' `Prop`-only
   development never put on the wire — and **2 violations in 126 mutants**
   followed, one defect reached through `True.rec` and `Acc.rec`:

   - a **recursor's** `levelParams` was decorative. Renaming the motive universe
     parameter at the binding site, leaving the type and every ι-rule mentioning
     the old name (now free), was admitted here; Lean's kernel generated
     `Sort uparam.0` where the stream said `Sort u`. Round 2's universe-closure
     check could not have caught it: a recursor is *generated* by this kernel
     and then compared, never admitted from the stream, so the kernel is never
     handed the exported binding list — and the comparison alpha-renames the
     exported parameters onto the generated ones **positionally**, so a
     parameter the exported list does not bind is not in the map, passes through
     untouched, and `def_eq` accepts it.

   Four defects in three rounds. Three of the four are the same shape —
   *bookkeeping copied across a boundary and never compared* — and each was
   found only by looking somewhere the previous round had not. The instrument's
   own reach is the binding constraint, measured directly: with the round-3 fix
   reverted, a 66-mutant sweep passed clean and a 126-mutant sweep found the
   defect twice. So a clean round is evidence in proportion to its budget, and
   "the rate is levelling off" remains unsupported.

   Round 3 named a hole it could not close, and round 4 (2026-08-18) closed it
   by finding that the hole was in the instrument. Round 3 read "the undamaged
   nested stream fails on `axeyum_wire_rose.rec_1`" as *Lean's kernel does not
   build the auxiliary recursor*. It does. What does not know about it is
   `Environment.find?`, the **elaborator's** lookup: `addDeclCore` republishes
   only `Declaration.getNames`, and that function's own docstring says the list
   "does not include ... auxiliary recursors computed by the kernel for nested
   inductive types". Asking `env.toKernelEnv` instead returns the recursor Lean
   built, with its two motives, three minors and both ι-rules. One line of the
   replay script; no exemption; the residue is **zero bytes**, not a bounded
   allowance. Measured against pinned 4.30.0: all three official nested fixtures
   now replay clean where they previously failed with exactly one disagreement
   each, and 17 of 17 mutants confined to an auxiliary recursor were
   discriminated by Lean's kernel. `restore_nested_inductive_group` — the fourth
   admission gate — is adversarially covered, with a floor
   (`MIN_AUX_RECURSOR_DISCRIMINATED`) that fails if the lookup regresses or an
   absent constant is ever exempted rather than reported.

   The lesson generalises past this gate, and it is this repository's own:
   **an empty answer from a tool that was never pointed at your subject is
   indistinguishable from a strong negative result.** `Environment.find?` ran,
   returned a correct `none`, and answered a question about the elaborator's
   view that had been asked about the kernel's.

   `quot` records remain a genuinely undiscriminating axis: Lean's `addDeclCore`
   ignores the carried types for a quotient package and adds its own, so it
   accepts every damaged quotient record. That one is a property of the
   interface, not of where we looked.

   What would change this estimate is rounds that find nothing, not rounds that
   are not run.

2. **The preludes state what they claim to state.** ~16k lines of
   `nat_prelude/`, `int_prelude/`, `rat_prelude/`, `string_prelude/` are content,
   so a bug there cannot admit a false theorem — but it can produce a *true
   theorem about the wrong thing*. If `Nat.gcd` is not gcd, every theorem about
   it is sound and worthless. Nothing in the trusted-core measurement addresses
   this; the kernel guarantees the proof, not the statement.

3. **The transcription from SMT-LIB into the rendered statement.** This is the
   **known open gap**, and it is the weakest link, not the kernel. Evidence rows
   record `recheck` as `na` at the text front door because verifying the algebra
   does not re-derive the binding from the cited atoms to the query text. In
   plain terms: we can prove the rendered proposition, and we cannot yet
   mechanically show the rendered proposition is what the input file said. A
   reader who accepts (1) and (2) must still take (3) on inspection.

4. **The tooling reports what it measured.** This repository's own record is
   that tools have lied more often than the solver has been weak, and this
   session added two more instances, both live on the development host right now:

   - `crates/axeyum-lean-kernel/tests/support/lean_probe.rs` picks the
     **newest installed** elan toolchain, not the one `lean-toolchain` pins. With
     4.30.0 and 4.34.0-rc1 both installed, it selects 4.34.0-rc1, under which
     `scripts/lean/replay-lean4export.lean` does not even elaborate — so
     `real_lean_kernel_replay` fails on this host for a reason unrelated to
     anything it tests, and `scripts/check-lean-gate.sh` (which resolves
     differently, and finds 4.30.0) disagrees with it. Any "official Lean accepts
     it" claim is currently version-dependent. The wire differential pins 4.30.0
     itself and asserts the version rather than trusting discovery.
   - `cargo clippy -p axeyum-lean-kernel -- -D warnings` currently fails on 12
     dead-code errors in `src/rat_prelude/statements.rs` (another lane's
     in-progress work), so any lane linting the kernel gets a red that is not
     theirs.

---

## Reproduce

```sh
python3 scripts/check-kernel-trusted-core.py --verbose
python3 -m unittest scripts.tests.test_check_kernel_trusted_core

export AXEYUM_LEAN_BIN=$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean
cargo test -p axeyum-lean-import --test real_lean_wire_differential -- --nocapture
cargo test -p axeyum-lean-kernel --test lambda_binder_domain_must_be_a_type
```
