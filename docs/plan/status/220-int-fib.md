# Lane: int-fib — build `Int.fib`, then close what it unblocks

<!-- plan-section: lane-status -->

**Your lane's block (`DONE this pass`, int-fib, 2026-08-28).** Confirmed
yesterday's `fib-backlog` finding with a fresh positive control (own
`int_theorem_inventory`/`shape_search`-style read of the tree, not a stale
binary): `Int.fib : ℤ → ℤ` genuinely did not exist — `int_prelude/fibonacci.rs`
only ever built `ofNat (Nat.fib n)` terms for `Int.fib_cassini`, never a
function taking a real `Int` argument.

Built `Int.fib` (`int_prelude/fibonacci.rs::declare_fib`): the standard sign
extension `fib(-n) = (-1)^(n+1) fib(n)`, as ONE `Int.rec` case split with no
new recursion device — closer to `Nat.bit` than to `Nat.log`'s fuel device,
exactly as the brief predicted, confirmed rather than assumed (`Int.pow` is
already total/structural on its `Nat` exponent, so no parity case-split is
needed inside the definition itself):

- `fib (ofNat n)   := ofNat (Nat.fib n)`
- `fib (negSucc m) := pow (neg one) m * ofNat (Nat.fib (succ m))`

Closed one fact: `F:ml430-int-fib-two-mul-add-one-pos-8977f65f`
(`∀ n : ℤ, 0 < Int.fib (2*n+1)`), landed as
`Int.fib_two_mul_add_one_pos` — positivity at every ODD index in EITHER
direction of `ℤ`. Case split on `n`; in both branches `2*n+1` reduces PURELY
(no named lemma for the arithmetic itself — `Int.mul`/`Int.add` on
`ofNat`/`ofNat` and `ofNat`/`negSucc` pairs, and `Int.subNatNat`'s own
`Nat.sub`-based case split, are all structural, `defs.rs`'s own module doc)
down to a clean `Nat`-side shape. The `ofNat` branch closes directly from
`Nat.fib_pos_of_pos` + `Nat.zero_lt_succ` via the kernel's own defeq (`Int.lt`
on `ofNat`/`ofNat` reduces to `Nat.lt`, already documented elsewhere in this
codebase). The `negSucc j` branch needed exactly one non-structural fact,
`(-1)^(2j) = 1` (new private helper `pow_neg_one_two_mul`, induction on `j`
reusing `pow_neg_one_succ` + `neg_neg` — both already built for
`fib_cassini`), then an `Int`-level `itransport` moves the resulting
`Nat`-side positivity fact across `Eq Int (fib (negSucc (2j))) (ofNat
(Nat.fib (2j+1)))`.

**`Int.fib` is independently checked by evaluation, not only by this
theorem's type-check** — `fib_computes_the_sign_extended_sequence`
(`int_prelude_tests.rs`) reduces `fib` at six concrete indices (both signs:
`fib(3)=2, fib(2)=1, fib(-1)=1, fib(-2)=-1, fib(-3)=2, fib(-4)=-3`) against
the hand-computed sequence, with a negative control at `fib(-2)` (`fib(-2)`
must NOT compute to `1`) guarding against a definition that silently dropped
the sign.

Measured `axiom_footprint`: **empty** for both `Int.fib` and
`Int.fib_two_mul_add_one_pos` (`theorem_axiom_footprint`, `integer` row: `610
theorems, 610 axiom-free`, environment carries 0 trusted declarations in the
`integer` prelude). `int_prelude::` full sweep: **37 -> 38 tests, all green**
(added `fib_computes_the_sign_extended_sequence`); no test removed, no
regression. `cargo fmt --check` and `cargo clippy --all-targets -D warnings`
both clean on the touched files.

**No target carried a HELD-OUT or MUTATION marker.** Checked
`scripts/fact-frontier.py` directly: the sixth "open `integer-fibonacci`"
fact, `F:ml430-mutation-aabb80b1f89f0c5847364692`, carries
`⛔ MUTATION (boundary-widening-biconditional)` — skipped, not attempted, as
instructed.

**Kernel rejected nothing on the landed declarations** — both `declare_fib`
and `declare_fib_two_mul_add_one_pos` kernel-checked on the first attempt
after compiling. (Two ordinary `cargo check` compile-error rounds first, both
missing imports — `BinderInfo`/`Declaration`/`ReducibilityHint`/`Shape`/
`case_split` — fixed before any kernel run.)

**Not attempted** (left for the next lane): the other three open
`integer-fibonacci` facts —
`F:ml430-int-fib-add-181b6a2c` (`Int.fib_add`, the general addition formula
`fib(m+n) = fib(m-1)fib(n) + fib(m)fib(n+1)` for arbitrary `m, n : ℤ` — needs
genuine two-sided induction over `ℤ`, substantially larger than this lane's
scope), `F:ml430-int-fib-of-odd-66560495` (needs an `Int.Odd`/`Int.Even`
predicate pair, which does not exist in this kernel at all — only `Nat.Odd`/
`Nat.Even` are declared), and `F:ml430-int-fib-two-mul-0e70f3dd` plus
`F:ml430-int-fib-two-mul-add-two-0ba4a948` (both `needs first:
F:ml430-int-fib-add-181b6a2c`, blocked on the addition formula above).

<!-- plan-section: landed-changes -->

| 2026-08-28 | int-fib | `Int.fib : ℤ → ℤ` landed (`int_prelude/fibonacci.rs::declare_fib`), the sign-extended Fibonacci sequence, one `Int.rec` case split, axiom-free, evaluated at six concrete indices with a sign-drop negative control |
| 2026-08-28 | int-fib | `Int.fib_two_mul_add_one_pos` landed and kernel-checked, axiom-free; closed `F:ml430-int-fib-two-mul-add-one-pos-8977f65f` |
