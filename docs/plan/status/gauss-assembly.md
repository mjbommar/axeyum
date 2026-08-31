# Lane: gauss-assembly -- Gauss's-lemma connecting theorem, item 2

<!-- plan-section: lane-status -->

**Your lane's block (`PARTIAL`, gauss-assembly, 2026-08-31).** Read
ADR-1070 and `docs/plan/status/gauss-piece-3.md` first, per this lane's
brief's own standing rule that a handoff's "what remains" is a
hypothesis, not an inheritance. Verified all three cited items against
the tree before starting; none had moved since ADR-1070.

Landed **item 2 in full** (`gcd(m!, pp) = 1`, both the `Nat`-typed
coprimality ADR-1070 sized and the `Int`-typed bridge item 3's
`Int.ModEq.cancel` actually needs):

- `Nat.coprime_factorial_of_lt_prime` (`nat_prelude/gauss_lemma.rs`):
  `∀ pp m, PrimeCond pp → Lt m pp → gcd pp (factorial m) = one`. Induction
  on `m`, combining `coprime_of_lt_prime` (each factor `1..m` is below
  `pp`) via `coprime_mul_of_coprime`. Reused this file's existing
  `prime_condition` (from `primes.rs`) and the same bound-weakening shape
  `declare_modeq_prod_range_lt` (`int_prelude/prod.rs`) already uses.
- `Int.factorial_eq_of_nat_factorial` (new file
  `int_prelude/gauss_factorial_coprime.rs`): `Int.factorial m = ofNat
  (Nat.factorial m)`. `Int.factorial` and `Nat.factorial` are two
  independently-recursive constructions of the same function (the former
  a `prodRange` fold, the latter a direct `Nat.mul` recursion), and ADR-
  1070 flagged a possible extra `Nat.mul`-to-`Int.mul` distribution lemma
  as needed and unchecked for this bridge. **It was not needed**: `Int.mul
  (ofNat a) (ofNat b)` is defeq `ofNat (mul a b)` for SYMBOLIC `a`, `b`
  too, because `Int.mul`'s case split dispatches on the outer `Int`
  constructor only (not on the wrapped `Nat` values) -- one of the
  cheaper-than-sized outcomes this repository's standing rule about
  handoffs predicts.
- `Int.coprime_factorial_of_lt_prime`: combines the two above into
  `Int.Coprime (factorial m) (ofNat pp)`, purely by defeq (`Int.Coprime`/
  `Int.gcd`/`Int.natAbs` all unfold transparently on an `ofNat`-headed
  argument) plus one `gcd_comm` flip to match argument order -- no new
  proof content beyond the bridge and the Nat theorem.

All three admitted by the kernel on the **first attempt**, axiom-free
(confirmed via `theorem_axiom_footprint` at each declaration's kernel
name, camelCase for the two `Int` ones, snake_case for the `Nat` one --
this repository's standing gotcha about that tool's exact-name matching).
Each carries a concrete instantiation test (`pp := 7`, `m := 4`) alongside
the symbolic build, per the standing rule that a symbolic accept and a
concrete check fail on disjoint defect classes. The `PrimeCond` hypothesis
in each concrete test is a free variable registered in a `LocalContext`
(a bare top-level `Kernel::infer` rejects an unregistered fvar with
`UnboundFVar`; building an actual closed `PrimeCond(7)` witness would need
a real divisor case analysis and add nothing the test needs, since the
conclusion's TYPE does not depend on which proof inhabits that
hypothesis).

**What remains -- two items, NOT attempted this session**, exactly as
ADR-1070 sized them:

1. The per-term congruence `a·k ≡ ε_k · gaussFold(pp,a,k) [pp]` for
   `k = 1..m`. Not started; ADR-1070's route (case split on
   `gaussSignNeg`, `mod_self_congr`/`Int.mod_eq_of_nat_mod_eq` to lift the
   `Nat.ModEq` reasoning into `Int.ModEq`) is unverified against the tree
   this session -- **verify it before inheriting it**, per this file's own
   standing rule. One correction already known: ADR-1070 flagged a
   possible `Nat.mul`-to-`Int.mul` distribution lemma as needed for this
   step too; per this session's finding above, that step is free by defeq
   wherever it is `Int.mul` applied to two `ofNat`-headed arguments, so
   check whether item 1 actually needs it before building one.
2. The final assembly -- chains item A (`prodRange_scaledIndexEqPowMulFactorial`),
   the per-term congruence (item 1, still open), `Int.modEq_prodRange_lt`,
   `Int.prodRange_mul`, `gaussSignProdEqPowNegOneOfCount`, piece 2's
   `InjectiveOn`/`MapsInto` fed to `Int.prodRange_permute`, and item 2
   (this session, landed) fed to `Int.ModEq.cancel`. Blocked on item 1.

Verification this session: `cargo test -p axeyum-lean-kernel --lib
int_prelude::` (58 passed, 0 failed, up from 56); `cargo test -p
axeyum-lean-kernel --lib nat_prelude::` (269 passed, 0 failed, up from
268) -- both including the environment-derived
`every_*_declaration_is_checked_and_axiom_free` coverage assertions,
which caught all three new declarations as unlisted on the first run (as
designed) and were updated, not weakened. `cargo clippy -p
axeyum-lean-kernel --lib -- -D warnings` clean (one pre-existing-style
doc-comment lint pair in the new file, fixed, not suppressed).
`derived_laws`/`derived_lemmas` pinned array in `int_prelude_tests.rs`
recounted 229 -> 231 via `scripts/recount-pinned-inventory.py` (never
hand-incremented). No fact-ledger entries added this session (kernel
declarations only, matching `gauss-piece-3`'s own choice, since these are
internal connecting-theorem steps rather than named mathematical
propositions).

No premise in this lane's brief was found wrong against the tree, beyond
the one correction already logged above (the distribution lemma ADR-1070
flagged as unchecked turned out to be free).

<!-- plan-section: landed-changes -->

| 2026-08-31 | gauss-assembly | `Nat.coprime_factorial_of_lt_prime`, `Int.factorial_eq_of_nat_factorial`, `Int.coprime_factorial_of_lt_prime` (Gauss's-lemma connecting-theorem item 2, `gcd(m!,pp)=1` in both the `Nat`-typed and `Int`-typed forms item 3 needs) land axiom-free toward the connecting theorem (ADR-1070). Two of ADR-1070's two remaining items are now one: item 1 (per-term congruence) and item 3 (final assembly, blocked on item 1). |
