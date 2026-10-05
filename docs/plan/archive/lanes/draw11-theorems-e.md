# Lane: draw11-theorems-e — closing more of the ADR-0925 draw-11 dispatch queue

<!-- plan-section: lane-status -->

**Done (`DONE`, draw11-theorems-e, 2026-08-31).** Measured 10 dispatchable
at session start (`python3 scripts/check-dispatchable-frontier.py`),
matching the brief. Closed **6** `ml430` mirrors, all axiom-free
(`theorem_axiom_footprint`, `0` in every matched row):

- `Nat.add_factorial_lt_factorial_add : 2<=i -> 1<=n -> i+n! < (i+n)!` and
  its succ corollary `Nat.add_factorial_succ_lt_factorial_add_succ` — the
  strict companions of a sibling lane's already-proved `<=` pair.
  `le_dest`+`Exists.rec` peel `2<=i` into `i = 2+k`, then a `k`-indexed
  strict induction: base (`k=0`) via `factorial_lt_of_lt`+`factorial_le`
  (`factorial 2 ≡ 2` by pure `δ/ι`)+`mul_le_mul_left`; step reuses the `<=`
  proof's own step function verbatim, since `Lt a b` is definitionally
  `Le (succ a) b` and lands the IH one `succ` ahead for free. New module
  `nat_prelude/add_factorial_lt.rs`.
- `Int.gcd_dvd_iff : gcd a b | n <-> exists x y, n = a*x+b*y` — both
  directions route through the already-checked Bezout identity at the
  NAMED witnesses `gcdA`/`gcdB` (`gcd_eq_gcd_ab_witnesses`), so only the
  fact's own quantifiers need elimination/introduction: a local
  `int_exists_elim` (the shared `int_prelude::ops::exists_elim` hardcodes
  the `Nat`-quantified case) for the reverse direction, `Nat.dvd`'s own
  witness scaling both Bezout coefficients for the forward direction. One
  real bug caught: `icongr` is Int-typed and cannot consume a `Nat`
  equality directly — needed `nat_eq_to_int` (cross-carrier lift), the
  exact trap CLAUDE.md documents. New module `int_prelude/gcd_dvd_iff.rs`.
- `Int.exists_gcd_one`/`Int.exists_gcd_one'` — dividing `m,n` by their own
  `gcd` leaves a coprime pair. Both reuse `gcd.rs`'s already-checked
  `gcd_div_gcd_div_gcd` for coprimality and rebuild that theorem's PRIVATE
  `exact` closure locally (`a = c*(a.ediv c)`, via
  `emod_eq_zero_iff_dvd`+`ediv_add_emod`) to get the quotient equations,
  commuted with `mul_comm` to the fact's stated order. The primed mirror
  reuses the identical construction at `g := gcd m n`, with the hypothesis
  itself doubling as the `0 < g` conjunct — no new arithmetic, one more
  `Exists.intro`/`And.intro` layer. New module `int_prelude/exists_gcd_one.rs`.
- `Nat.Coprime.mul_add_mul_ne_mul : Coprime m n -> a<>0 -> b<>0 -> a*m+b*n
  <> m*n` — the one genuinely non-trivial proof this session. A
  `cases_zero_succ` split on `m` then `n` (outer hypotheses folded into the
  per-branch motive, per that helper's own doc) handles the `m=0`/`n=0`
  degenerate cases (`m=0` forces `n=1` and collapses to `b=0`,
  contradicting `b<>0`; `n=0` is more direct — pure `δ/ι` on both sides).
  The `m,n>=1` case is Gauss's lemma run in both directions (`m|b`, `n|a`
  via `gauss_lemma`/`coprime_symmetric`) then `le_of_dvd` to get `m<=b`,
  `n<=a`, lifted via `mul_le_mul_left`+`mul_comm` to `X+X<=X` (`X:=m*n`,
  `X>=1` via `one_le_mul`), refuted by `lt_irrefl`. New module
  `nat_prelude/coprime_mul_add_mul_ne_mul.rs`.

Every declaration compiled and was kernel-accepted on its first or second
attempt (one Int/Nat carrier-mismatch bug, one missing `pi_fv`/`lam_fv`
wrap for a non-arity-bound variable, both caught by a temporary debug test
rendering the `TypeMismatch` operands via `Kernel::render_lean` rather than
guessing). All six facts flipped to `proved` with kernel-term +
axiom-footprint evidence (checker commands verified to actually match
before writing them into the JSON — including the `theorem_axiom_footprint`
substring-match trap on `Int.exists_gcd_one'`, and the
lowercase-vs-Mathlib-namespace trap on `Nat.coprime_mul_add_mul_ne_mul`),
`depends_on` derived via `check-fact-depends-derived.py --fix`, statements
pinned via `check-settled-fact-statements.py --write` each time (the first
`--write` backfilled `kernel_theorem`/`history` for the WHOLE ledger, since
the committed pins file predated those fields for many facts other lanes
had already added `formal.kernel_theorem` to — a large but deterministic
diff, not scope creep).

**Full `nat_prelude::`/`int_prelude::` sweeps after every change: nat 257
passed 0 failed throughout (256 baseline, +1 for the strict-factorial pair
declared together, +0 more until the coprime fact, then 257); int 52
passed 0 failed throughout (51 baseline +1 for `gcd_dvd_iff`, then +2 for
the `exists_gcd_one` pair — pin recounted 219→220→222 across the two
int_prelude landings).** No regressions at any step. `bash
scripts/lane-prepush-fmt.sh` run before the final commit (reformatted this
lane's own `add_factorial_lt.rs`, which had never been run through
`rustfmt` before its first commit — whitespace only, re-verified green).

Holdout isolation: `python3 scripts/check-autogenesis-holdout-isolation.py`
→ `PASS`, `held_out=146`, measured before this lane's first edit and again
after every subsequent flip — unchanged throughout.
`artifacts/autogenesis/` was never touched.

**4 declined without attempting, all for measured DIFFICULTY, matching the
brief's own sizing and re-verified against the live frontier before
stopping:** `Nat.size_bit`/`Nat.size_le_size` (`Nat.size` is fuel-indexed on
the first argument, needing the same fuel-sufficiency machinery `land`/`lor`
required — not attempted); `Nat.Squarefree.ext_iff` (needs unique
factorization, which `nat_prelude/factorization.rs`'s own module doc says
this kernel cannot express — no `List`/`Finset`); `Nat.fermat_primefactors_one_lt`
(needs multiplicative-order theory plus a quadratic-reciprocity supplementary
law; a sibling lane sized and declined this same target the same session).

**Hardest thing this session:** the `Int.gcd_dvd_iff` `TypeMismatch{expected:
Int, got: AxNat}` from passing a `Nat`-typed equality (`heq : Eq Nat n
(mul g q)`, from `Nat.dvd`'s witness) directly into `icongr`, the Int-typed
congruence combinator — a carrier mismatch that compiles fine (both are
`ExprId`) and only fails at kernel-check time, with an error naming neither
side by name. The fix (`nat_eq_to_int`, the cross-carrier lift
`int_prelude::ops` already provides for exactly this) was findable only by
grepping for how `sign.rs`'s `mul_assoc` proof handles the same
Nat-equation-lifted-to-Int shape in its `(OfNat,OfNat,OfNat)` branch.

<!-- plan-section: landed-changes -->

| 2026-08-31 | `1bfe38739` | feat: `Nat.add_factorial_lt_factorial_add` + succ corollary, with tests (nat 257 pass) |
| 2026-08-31 | `1faff5f53` | facts: flip both strict-factorial-inequality facts to proved |
| 2026-08-31 | `ddb2e44b0` | feat: `Int.gcd_dvd_iff` (int 52 pass) |
| 2026-08-31 | `34d932896` | facts: flip `Int.gcd_dvd_iff` to proved |
| 2026-08-31 | `7a0de986c` | feat: `Int.exists_gcd_one` + `Int.exists_gcd_one'` (int 52 pass) |
| 2026-08-31 | `c7d5bdb19` | facts: flip both `exists_gcd_one` facts to proved |
| 2026-08-31 | `0b488679f` | feat: `Nat.Coprime.mul_add_mul_ne_mul` (nat 257 pass); rustfmt catch-up |
| 2026-08-31 | `4c8a81d76` | facts: flip `Nat.coprime_mul_add_mul_ne_mul` to proved |
