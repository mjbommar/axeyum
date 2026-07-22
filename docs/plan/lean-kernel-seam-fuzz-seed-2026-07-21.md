# Lean-kernel seam-fuzz seed — T6.0.3 / TL2.15

Date: 2026-07-21

Scope: the four kernel seams representable before projection, quotient, and
typed-literal work

Executable source:
[`crates/axeyum-lean-kernel/tests/kernel_seam_fuzz.rs`](../../crates/axeyum-lean-kernel/tests/kernel_seam_fuzz.rs)

## Result

T6.0.3's initial seam-first kernel-fuzz gate is implemented. One fixed-seed,
dependency-free harness registers the four current seams explicitly, runs **768
unique generated cases**, and reruns the complete population in the same test to
require an identical summary. Every case reaches the trusted theorem-admission
gate with `False` as its claimed type, rejects, and leaves no declaration behind.

This is a generated negative/property gate. It is not a proof of consistency,
not a Lean-differential corpus, and not completion of future TL2.15 seams.

## Exact population

| Family | Unique cases | Generated dimensions | Required observations |
|---|---:|---|---|
| `Prop` × elimination; proof irrelevance × iota | 192 | 2–4 constructors, every selected constructor, binder modes, beta/zeta wrapper depths 0–4 | distinct proofs remain definitionally equal; legal Prop elimination infers and iota-reduces; Type-valued elimination rejects; `False` admission rolls back |
| universes × inductives | 320 | first 288 exhaust `8 universe shapes × 4 constructor counts × 3 proof-field counts × 3 data-field counts`; 32 fixed-seed generated tail cases | recursor elimination-universe arity matches an independent semantic expectation; conservative parametric cases reject the old unrestricted shape; valid recursor constants infer; `False` admission rolls back |
| literals × reduction/admission | 256 | Nat `0`, `1`, `u128::MAX`, random 128-bit; empty, ASCII, Unicode, and embedded-NUL strings; beta/zeta depths 0–4 | lift/instantiate/level-substitution preserve literal identity; WHNF exposes but does not rewrite the literal; inference returns `UnsupportedLit`; `False` admission rolls back |
| **Total** | **768** | four active seam bits | **768/768 rejected `False` admissions; exact summary reproduced on a second run** |

The eight universe shapes are `0`, `1`, `u`, `succ u`, `max u 1`, `max u 0`,
`imax u 0`, and `imax 1 u`. The test states the provably-nonzero expectation in
its own enum rather than calling `Kernel::level_is_nonzero` to decide what the
assertion should be. This prevents the test from using the implementation under
test as its oracle.

## Failure and coverage contract

- Family seeds are fixed and printed into each case label:
  - Prop/elimination: `0xA0E1600300000001`;
  - universe/inductive: `0xA0E1600300000002`;
  - literal/reduction: `0xA0E1600300000003`.
- A failure reports the family, case index, and derived 64-bit case seed.
- A four-bit registry must observe all active seams.
- Constructor counts, wrapper depths, universe shapes, proof/data field counts,
  literal kinds, and all eight literal corners must each have nonzero coverage.
- The number of rejected `False` admissions must equal the complete unique-case
  population.
- A failed declaration must be absent from the environment afterward.
- Running the whole harness twice must produce equal structured summaries.

The existing
[`prop_large_elim_derives_false.rs`](../../crates/axeyum-lean-kernel/tests/prop_large_elim_derives_false.rs)
retains the complete historical exploit term; the new harness generalizes its
boundary rather than replacing that adversarial witness with a weaker unit test.

## Gate

Focused command:

```sh
MEM_LIMIT_GB=4 ./scripts/mem-run.sh cargo test \
  -p axeyum-lean-kernel --test kernel_seam_fuzz
```

`cargo test --workspace --all-features`, and therefore the existing `just test`
dependency of `just check`, discovers this integration test automatically. The
focused `just lean-kernel-seams` recipe provides a fast reproduction path.

Validation on the recorded slice:

- focused gate: 1/1 passed under 4 GiB;
- `cargo test -p axeyum-lean-kernel --lib --tests`: 177 unit tests and five
  integration tests passed under 4 GiB. The official-Lean wrapper ran in its
  locally optional mode; forcing `AXEYUM_REQUIRE_LEAN=1` correctly failed closed
  because this host has no Lean binary, so this slice takes no new official-Lean
  differential credit;
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings`: passed
  under 4 GiB;
- parity-document unit tests, generated-artifact checks, parity prose checker,
  repository link checker, and `git diff --check`: passed;
- touched-file rustfmt: passed. Workspace-wide `cargo fmt --all --check` remains
  red on pre-existing unrelated `axeyum-bench`/`axeyum-cas` formatting drift.

## Exact non-credit and next hooks

TL2.15 remains **PARTIAL**:

- projection × structure eta has no expression form or reduction rule before
  TL2.2–TL2.5;
- quotient reduction has no kernel package before TL2.10;
- literals are deliberately tested only as fail-closed declines; arbitrary-
  precision storage and typed reduction remain TL2.6–TL2.9;
- the harness has no official-Lean differential oracle or shrinker yet;
- strict positivity remains incidental to current recursive declines and must
  land under TL2.11 before recursive-indexed/reflexive admission broadens.

The immediate implementation order therefore advances to projection
TL2.2–TL2.5. Each newly admitted seam must add generated positive, negative,
`False`-admission, mutation, and official-comparison cases to this harness before
receiving TL2.15 credit.
