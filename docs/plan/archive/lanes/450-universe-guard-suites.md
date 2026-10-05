# Lane: universe-guard-suites — the three suites ADR-1495's universe guard refused, decided against Lean itself

<!-- plan-section: lane-status -->

**DONE, universe-guard-suites, 2026-09-03.** `scripts/lane-push.sh` was refused
on `main` at `76a8d109c`: `scripts/check-kernel-suites.sh` runs three tests that
fail with `ConstructorFieldUniverseTooBig`, all from ADR-1495's guard
(`c72fd281b`, 2026-09-01). **All three fixtures were Lean-illegal and the guard
is right; nothing in the kernel changed.**

Why nobody saw it: ADR-1495's own measurement was aimed at
`kernel_seam_fuzz` / `mutual_inductive_group_grammar` / `nested_inductive_grammar`,
and every lane since ran only its own prelude's `--lib` filter. These two suites
had not run since the guard landed.

**Decided against Lean 4.30, not against what makes the test pass.** Each shape
was rebuilt as a `.lean` file and handed to the pinned
`leanprover--lean4---v4.30.0` binary. Lean refuses all three with the same
message and accepts each corrected form (exit 0):

| fixture | family result universe | offending field | field's universe | Lean 4.30 |
| --- | --- | --- | --- | --- |
| `support/lean_shaped_string.rs` `String` (under `CharAtUniverseOne`) | `Sort 1` | 0: `List.{1} Char` | `Sort 2` | **refused** — "Parameter has type List MyChar at universe level 2 which is not less than or equal to the inductive type's resulting universe level 1" |
| `recursive_induction_hypotheses.rs` `generated_1p1i_type_d0_f2_v1` | `Sort 1` (`I (p : Type) : Type → Type`) | 0: `Sort 1`, the field the dependent-index production makes BE the index | `Sort 2` | **refused** — "Parameter `a` has type Type at universe level 2 …" |
| `recursive_induction_hypotheses.rs` `acc-indexed-dependent` | `Sort 1` (`I (p q : Type) : Type → Type`) | 1: `⦃a : Sort 1⦄ → {b : a} → I p q a`, type `imax 2 1` | `Sort 2` | **refused** — "Parameter has type ⦃a : Type⦄ → {_b : a} → I p q a at universe level 2 …" |

Field 0 of `acc-indexed-dependent` is `Sort 0`, whose type is `Sort 1` — legal
at `1 ≤ 1`, which is why the guard reports `field_index: 1` and not 0.

The rule cited is Lean's `check_constructor`: a constructor field's type must
live at or below the family's result universe, `Prop` (result level zero)
exempt because it is impredicative. This kernel implements it at
`crates/axeyum-lean-kernel/src/inductive.rs:2079`.

**The repair is ADR-1495's own: put the `type`-sorted families at `Sort 2`.**
That is exactly what ADR-1495 did to `tests/mutual_inductive_group_grammar.rs`;
these two suites were simply not in its measurement.

- `recursive_induction_hypotheses.rs`: `family_type`'s non-`Prop` base moves
  `Sort 1` → `Sort 2`. The pinned 768-case summary and its
  `descriptor-fnv1a64=0d245921566be735` are **unchanged** — the descriptor
  records the profile, the sort LABEL, the depth, the field count, the variant,
  the recursive-field count and the index production, never a universe or a
  field domain.
- `support/lean_shaped_string.rs`: under `CharAtUniverseOne` **alone**, `String`
  follows `Char` up to `Sort 2`. Every other mutation stays at `Sort 1`.

**The string mutation still measures what it names, and that is now asserted
rather than argued.** `build_string_literal_bootstrap` (`src/tc.rs`) never
inspects `String`'s own sort; it requires `String.ofList`'s domain to be
`List.{0} Char` and returns `None` at the first nonzero level. So
`every_bootstrap_clause_is_load_bearing` gained a two-sided control on
`env.list_level` — zero for `Mutation::None`, **nonzero** for
`CharAtUniverseOne`. Those are contradictory predicates over the same
expression, so neither can be vacuous while both pass, and the control can no
longer degenerate into "some other clause broke".

**Guard untouched, and re-measured.** `--lib inductive`: **56 passed, 0 failed**,
including `reject_ctor_field_universe_above_result_universe`, its polymorphic
twin, and all six admission/ordering controls the `pin-the-universe-guard` lane
split out. No ADR was needed (ADR-1575 was reserved for a guard change that did
not happen).

**The gate the push runs is green.**
`AXEYUM_CARGO=scripts/cargo-serialized.sh MEM_LIMIT_GB=64 scripts/mem-run.sh
scripts/check-kernel-suites.sh --no-lib` — the exact step in `hooks/pre-push` —
**exit 0, 32 suites, 193 tests, every suite `ran` with a nonzero count and none
`FAILED`**. `recursive_induction_hypotheses` 4, `string_literal_semantics` 11.
`kernel_declaration_projection` before (`main` at `76a8d109c`, in a
`lane-snapshot.sh` tree) and after: **15,887 rows each, byte-identical, zero
diff** — as the diff scope requires, since the change touches only three files
under `crates/axeyum-lean-kernel/tests/`.
`clippy -p axeyum-lean-kernel --all-targets -- -D warnings` exit 0, and that
coverage was **probed rather than assumed**: a deliberate `needless_range_loop`
appended to `string_literal_semantics.rs` made the same command fail, so the
green run really did lint the changed targets.

**A SECOND, UNRELATED PUSH BLOCKER IS STILL RED ON `main`, and this lane did not
fix it.** `scripts/check-kernel-suites.sh` *without* `--no-lib` also runs the
crate's own debug `--lib` sweep, and that target aborts:

    thread 'rat_prelude::det_mul_tests::det_mat_mul_computes_at_concrete_matrices'
      has overflowed its stack
    fatal runtime error: stack overflow, aborting
    (signal: 6, SIGABRT)

Reproduced on **unmodified `main` at `76a8d109c`** in a snapshot tree with none
of this lane's code present, so it is not caused by anything here. It is the
documented debug-frames class: the same test `--release` is **1 passed in
21.31s**. It matters because `cargo test --workspace --lib` is an earlier
`hooks/pre-push` step and will hit the same abort — the universe fix unblocks
one gate, not the whole battery. Owner needed.

**Measurement note for whoever runs the full group next.** The first attempt at
`scripts/check-kernel-suites.sh` (with `--lib`) under `cargo-serialized.sh`'s
DEFAULT `AXEYUM_CARGO_MEM=24G` was SIGKILLed part-way through the lib sweep, and
the script then reported **every one of the 32 integration suites as `0 INERT`**
— a truncated capture is indistinguishable from 32 empty suites in that table.
At `AXEYUM_CARGO_MEM=64G` the same command ran to completion and all 32 suites
reported their real nonzero counts with the `--lib` target as the sole failure.
Read the lib target's line before believing an INERT row.

<!-- plan-section: landed-changes -->

| 2026-09-03 | `131756de5` | Lane status stub: three kernel suites refused by ADR-1495's universe guard, under triage. |
| 2026-09-03 | `714e58f3a` | Moved three Lean-illegal test fixtures to the universe Lean 4.30 gives them (`Sort 1` → `Sort 2` for the `type`-sorted families; `String` follows `Char` under `CharAtUniverseOne` only), verified shape-by-shape against the pinned `lean` binary. Added the two-sided `list_level` control so the string mutation cannot degenerate. Kernel guard unchanged. |
