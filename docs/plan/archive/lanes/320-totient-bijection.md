# Lane: totient-mul — two more pieces toward `Nat.totient_mul_of_coprime`, the bijection route still not attempted

<!-- plan-section: lane-status -->

**DONE for this dispatch (`totient-mul`, 2026-08-30).** Landed two small,
fully-verified building blocks from `docs/plan/status/301-totient-
multiplicative.md`'s plan. Did NOT attempt `Nat.totient_mul_of_coprime`
itself, and did NOT attempt the CRT-bijection route `316-queue-sweep.md`
identified as the correct fix for `301`'s false `count_range_row_major`
claim — that remains the real remaining work, sized by `316` as several
more dispatches, and nothing in this session's budget changes that sizing.

## What already existed (did not need to build)

Before writing any code, ran `shape_search --include-constructed
--name-like coprime` (fresh build, `declarations=2301`) and `--name-like
gcd_mod`/`gcd_succ`. Confirmed landed by prior lanes and reused directly:

- `Nat.gcd_comm`, `Nat.coprime_div_left` (lane `totient-multiplicative`,
  `301`).
- `Nat.totient_coprime_totient_iff` (fact `F:ml430-nat-totient-coprime-
  totient-iff-3932cf83`, now `proved`) and `Nat.coprime_mul_of_coprime`
  (lane `totient-mult-finish`, `313`) — the coprimality-combine "weakest
  step" `301` flagged, landed via the prime-divisor contrapositive with no
  Bézout algebra.
- `Nat.coprime_mul_right_right`/`Nat.coprime_mul_left_right` (the two
  shrink-direction halves, `coprime_lemmas.rs`, pre-existing).
- `Nat.gcd_succ`, `Nat.mod_zero` (both pre-existing, `gcd.rs`/`defs.rs`).
- **Critically**, `316-queue-sweep.md` (already merged into `main` before
  this dispatch started) had already corrected `301`'s own Step 4
  (`count_range_row_major`): it is FALSE without `Coprime m n` — direct
  recomputation there found it fails at every tested non-coprime pair
  (`totient(4)=2` but `totient(2)*totient(2)=1` at `m=n=2`), because the
  identity is exactly CRT bijectivity of `x -> (x mod m, x mod n)`. This
  changed my brief's own framing (which cited the three remaining `ml430`
  totient mirrors as blocked only on `totient_mul_of_coprime`) — `316` also
  separately determined all three need a full prime-power-factorization
  framework this kernel does not have at all, independent of whether the
  coprime formula exists. **Read `316-queue-sweep.md` before dispatching
  another totient lane; do not re-derive this.**

None of this was rebuilt. `shape_search` confirmed `gcd_mod` and
`coprime_mul_iff`-shaped statements were genuinely ABSENT before this
session.

## What I landed

New file `crates/axeyum-lean-kernel/src/nat_prelude/totient_mul_coprime.rs`:

- **`Nat.gcd_mod_left_eq_gcd : ∀ x m, Eq (gcd (mod x m) m) (gcd x m)`**
  (`301`'s "Step 1", mod-gcd invariance). Case split on `m`
  (`cases_zero_succ`): at `m = 0`, `Nat.mod_zero` plus congruence; at
  `m = succ k`, chains `Nat.gcd_succ` (`gcd m x = gcd (mod x m) m`) with
  `Nat.gcd_comm` (bridging `gcd m x` to `gcd x m`) via `symm`/`trans`. Zero
  new induction — both ingredients were already declared before this file's
  dispatch point.
- **`Nat.coprime_mul_iff : ∀ x m n, Iff (Eq (gcd x (mul m n)) one) (And (Eq
  (gcd x m) one) (Eq (gcd x n) one))`** (`301`'s "Step 3" pointwise
  predicate identity, minus the `mod` substitution — see "What's still
  needed" below). **No `Coprime m n` hypothesis needed at all**: `mp`
  shrinks via `coprime_mul_right_right`/`coprime_mul_left_right` (both
  pre-existing), `mpr` is exactly `coprime_mul_of_coprime`. This was never
  stated as an `Iff` before, only as its two constituent one-way
  implications.

Both verified: kernel-checked at declaration time, plus a dedicated test
each (`gcd_mod_left_eq_gcd_applies_at_both_branches_and_symbolically`,
`coprime_mul_iff_applies_at_concrete_instances_and_symbolically`), each
exercising a concrete instance (both case-split branches for the first;
both a coprime AND a non-coprime concrete instance for the second, with
`gcd 2 2 != 1` checked directly so the non-coprime instantiation is not
vacuous) plus a genuinely free variable set via `LocalContext`/`infer_in`,
per this task's own "both checks are needed, they fail on disjoint defect
classes" instruction. Neither is attached to a fact — like `gcd_comm`/
`coprime_mul_of_coprime` before them, unregistered nat-prelude helper
theorems.

## What's still needed for `Nat.totient_mul_of_coprime`

Per `316`'s correction, the row-major counting shortcut does not work.
The two pieces this dispatch landed are real and reusable, but the actual
remaining path is the CRT-bijection route `316` sketched:

1. **The CRT self-map `g(x) := add (mul (mod x m) n) (mod x n)`**, its
   `MapsInto`/`InjectiveOn`/`SurjectiveOn` on `[0, mn)` (`301`'s "Step 0" —
   `301` says this "turned out NOT to be needed" for the row-major route,
   but `316` establishes the row-major route doesn't work, so Step 0 IS
   needed after all). Injectivity needs `Coprime m n` fed to
   `Nat.crt_unique` (`nat_prelude/crt.rs`, Nat-native, NOT the `int_prelude`
   one); surjectivity is free from `Nat.injective_on_imp_surjective_on`
   (`finite.rs`'s pigeonhole) once injectivity + `MapsInto` are in hand.
2. **"`countRange` is invariant under a domain bijection"** — a genuinely
   new primitive this kernel does not have in any form. I looked for it
   (`permutation.rs`'s `Nat.BijectiveOn`/`Nat.permInverse`,
   `cardinality.rs`'s two-bound pigeonhole, `subset_product.rs`'s
   `Nat.prodRangeIf`) and found the pieces a proof would COMPOSE from, but
   no existing "count is preserved under a bijective reindexing of `[0,n)`"
   statement. This is likely the largest remaining piece — sizeable on its
   own, probably comparable to `301`'s own "genuinely novel induction"
   sizing for `count_range_row_major`, which it replaces.
3. Once (1) and (2) exist, `countRange (fun x => beq (gcd x (mul m n)) 1)
   (mul m n)` reindexes along `g`'s inverse to a countRange over `[0,m) x
   [0,n)` pairs (needs a genuine "count over a product domain factors as a
   product of counts" step too — NOT the same statement as
   `count_range_row_major`, since it is now stated over the true bijection
   rather than a row-major peel), using [`declare_gcd_mod_left_eq_gcd`] and
   [`declare_coprime_mul_iff`] (both landed this session) to identify the
   per-coordinate predicates with `totient m`'s and `totient n`'s own
   predicates.
4. This is realistically comparable to `316`'s own sizing: several more
   dispatches, not a same-session close. The three declined `ml430`
   mirrors (`totient_dvd_of_dvd`, `totient_gcd_mul_totient_mul`,
   `eq_or_eq_of_totient_eq_totient`) need the FULL (non-coprime) formula on
   top of this, per `316` — a separate, larger prime-power-factorization
   framework this kernel does not have at all. Nothing in this session
   changes that.

## Files

- `crates/axeyum-lean-kernel/src/nat_prelude/totient_mul_coprime.rs` — new,
  `declare_gcd_mod_left_eq_gcd` and `declare_coprime_mul_iff`.
- `crates/axeyum-lean-kernel/src/nat_prelude.rs` — `mod totient_mul_coprime;`,
  two new `NameId` fields (placed immediately after `coprime_mul_of_coprime`,
  their last shared dependency), their `name_str` constructors, and two
  dispatch calls (placed immediately after `declare_coprime_mul_of_coprime`,
  where all of `mod_zero`/`gcd_succ`/`gcd_comm`/`coprime_mul_right_right`/
  `coprime_mul_left_right`/`coprime_mul_of_coprime` are already available).
- `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs` — two new
  tests, both added to `theorem_names` (environment-derived coverage
  assertion), determinism pin moved `93+574 -> 93+576` (taken from the
  panic's own mismatch: left `669`, right `667`).

## Verification

- `cargo check -p axeyum-lean-kernel --lib` — clean (checked before the
  first commit, per "commit within first 10 tool calls").
- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — **181 passed, 0
  failed** (179 baseline for this dispatch + 2 new tests, each confirmed to
  run by name with a nonzero count: `gcd_mod_left_eq_gcd_applies_at_both_
  branches_and_symbolically`, `coprime_mul_iff_applies_at_concrete_
  instances_and_symbolically`).
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` — clean.
- `rustfmt --edition 2024 --check` on every touched file — clean.
- `python3 scripts/check-test-attribute-integrity.py` — `0 findings`.

Did NOT run `./scripts/check.sh`, `cargo test --workspace`, or
`validate-facts.py`/fact-ledger checks — no fact file touched this session
(neither new lemma is registered to a fact; both are unregistered
nat-prelude helper theorems, same convention as `gcd_comm`/
`coprime_mul_of_coprime` before them).

## Commits

- `c8499b17e` — wip: `gcd_mod_left_eq_gcd` + `coprime_mul_iff`, kernel-check
  pending (landed within the first 10 tool calls; `cargo check` clean at
  that point, `cargo test` not yet run).
- `963e9724c` — kernel-verified, tests + coverage entry + pin.
- This status file's own commit follows.

<!-- plan-section: landed-changes -->

| 2026-08-30 | totient-mul | `Nat.gcd_mod_left_eq_gcd` and `Nat.coprime_mul_iff` (both new, axiom-free, `301`'s Steps 1 and 3 toward `totient_mul_of_coprime`) landed and verified in a new file `nat_prelude/totient_mul_coprime.rs`. Did not attempt `totient_mul_of_coprime` itself or the CRT-bijection route `316-queue-sweep.md` correctly identified as replacing `301`'s false `count_range_row_major` claim — sized as several more dispatches (a new "`countRange` invariant under a domain bijection" primitive is the largest missing piece, on top of the already-existing `nat_prelude/crt.rs` self-map). |
