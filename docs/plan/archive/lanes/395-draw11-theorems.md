# Lane: draw11-theorems — proving theorems from the refilled dispatch queue (ADR-0925 draw 11)

<!-- plan-section: lane-status -->

**Done (`DONE`, draw11-theorems, 2026-08-30).** The frontier at start of this
session (`python3 scripts/check-dispatchable-frontier.py`) showed only **3**
dispatchable mirrors, not the 23 the brief described — draw 11's queue had
already been drawn down by other lanes before this one started. Closed both
bitwise ones axiom-free on the first kernel attempt:

- `Nat.and_or_distrib_left`/`Nat.and_or_distrib_right`
  (`F:ml430-nat-and-or-distrib-left-fe131f64`,
  `F:ml430-nat-and-or-distrib-right-0daaa284`) — bitwise AND distributes over
  bitwise OR, both sides. New module `crates/axeyum-lean-kernel/src/nat_prelude/
  and_or_distrib.rs`. Route: `Nat.eq_of_testBit_eq` extensionality
  (`xor_algebra.rs`'s recipe) + `Nat.testBit_land`/`Nat.testBit_lor` twice per
  side, reduced to the bit-level identity `mul a (max b c) = max (mul a b)
  (mul a c)`, closed by a new helper `cases_le_one` (the value-bounded twin of
  `ops::cases_mod_two`) doing a nested `{0,1}` case split — 8 leaves per
  theorem, each `refl`, confirmed against a Python truth table before writing
  any Rust. Both admitted first try; `axiom_footprint: []` for both (read from
  `nat_axiom_inventory --require-axiom-free nat`, exit 0). Discriminating
  concrete instances `(6,3,5)` / `(3,5,6)` plus symbolic instantiation, each
  with two negative controls (inner-operator swap, outer-operator swap), added
  to `nat_prelude_tests.rs` and to `theorem_names` (the environment-derived
  coverage assertion caught the omission on first run, as designed). Both
  facts flipped to `proved` with evidence (kernel-term / concrete-instance /
  axiom-footprint) and `depends_on` derived via
  `check-fact-depends-derived.py --fix`.

**Third dispatchable target sized and declined — `F:ml430-nat-fermat-
primefactors-one-lt-58343c6f` (Lucas 1878: every prime factor `p` of the
Fermat number `F_n = 2^(2^n)+1`, `n > 1`, satisfies `p = k·2^(n+2)+1`).**
This is a genuine, provable-in-principle classical result — NOT a mirror-flip
divergence like the 11 rows the frontier already marks structurally blocked —
but it needs infrastructure this prelude does not have at all:

1. The multiplicative order of `2` mod `p` (order divides any exponent `m`
   with `2^m ≡ 1`, and divides `p-1` via Fermat's little theorem, which DOES
   exist here — `nat_prelude/fermat.rs`'s `declare_fermat`/
   `pow_prime_modeq_self`). Buildable, moderate effort.
2. The second supplementary law of quadratic reciprocity (`2` is a QR mod `p`
   iff `p ≡ ±1 (mod 8)`), needed for the `2^(n+2)` refinement (vs. the easier
   `2^(n+1)` bound from order theory alone). `int_prelude/euler.rs` has only
   `IsQuadraticResidue`'s definition and closure under multiplication — its
   own module doc says the sign criterion "needs" more, and nothing resembling
   Gauss's lemma or either supplementary law exists anywhere in `nat_prelude/`
   or `int_prelude/` (checked: no `order_of`, no `quadratic` hit beyond
   `euler.rs`/`euler_totient.rs`'s trivial definitions).

Both pieces are real number theory, not machinery this lane could stand up in
one session without crowding out correctness. Left `open`; the next lane
should budget it as a multi-step build (order theory first, landing local
facts, before attempting the QR supplement) rather than a single dispatch.

Holdout isolation: `python3 scripts/check-autogenesis-holdout-isolation.py`
→ `PASS` (`held_out=136`), run after landing; `artifacts/autogenesis/` was
never touched (confirmed via `git status`/`git diff` — zero files under that
path in this lane's changes).

Hardest thing hit: none of the kernel machinery was the hard part this time —
`Nat.testBit_land`/`Nat.testBit_lor`/`Nat.eq_of_testBit_eq` were already
landed and the per-bit case split transported cleanly on the first attempt.
The actual work was recognizing that the bit-level identity did not need
`Nat.le_total`'s general order-theoretic proof (which would need extra care
at the `b = c` boundary of `max`'s two branches) — restricting to `{0,1}` via
`Nat.testBit_le_one` and a fresh `cases_le_one` split made both proofs
8-leaf-`refl` trivial instead.

<!-- plan-section: landed-changes -->

| 2026-08-30 | draw11-theorems | `bb96b6a44` `Nat.and_or_distrib_left`/`_right` kernel theorems, axiom-free, new module `and_or_distrib.rs` |
| 2026-08-30 | draw11-theorems | `8822d5033` flip both facts to `proved`, evidence + depends_on attached, ledger validates clean |
