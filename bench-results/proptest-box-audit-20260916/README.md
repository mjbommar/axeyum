# Property-test box audit, 2026-09-16 (lane ax-proptest, ADR-2141)

Improvement-list item 5: the ADR-2134 `sign_at` incident generalized. A
float-oracle property test was green over a wrong sign because its coefficient
box had no integer solution for the shape that exposed the defect. Question:
which property tests and differential fuzzes in `axeyum-ir`, `axeyum-arith`,
`axeyum-cas`, `axeyum-bv`, `axeyum-cnf` and `axeyum-solver` sample from a fixed
box such that a known class of counterexample to the property's negation is
unreachable by construction?

`inventory.tsv` is the whole answer, one row per (test × generator box): the
literal ranges, the property, the counterexample class, one concrete instance,
`reachable`, the reason, the METHOD (`read` a branch / `derived` a constraint /
`ran hits=N/M seed=S` a replica of the generator for its configured run), and a
`disposition` column added after the controls landed.

## The table

| | count |
| --- | ---: |
| rows (tests × boxes) | **599** |
| reachable = yes | 244 |
| reachable = **no** (findings) | **328** |
| not-applicable | 27 |
| `no` rows closed by a generator fix (`fixed-lcg-mix`) | 48, in 24 generator files + the production faithfulness sampler |
| `no` rows closed by a seed class (`fixed-seed-class`) | 5 (`wide.rs` ×3, `inprocess_proof_path.rs` ×2) |
| `no` rows already covered before this lane | 1 (`sign_at`, ADR-2134's family test) |
| `no` rows that are a **STOP finding** (defect in the subject) | 1 (`lia_online.rs` push/pop fuzz — below) |
| `no` rows left open as structural box gaps (`structural-open`) | 273 (ir 11, arith 1, cas 23, cnf 40, solver 198), each with its excluding literal in the row |
| mutation controls registered | 33 suites, 38 mutations; every one measured `killed` (table below) |
| oracle sweeps re-run on the changed populations | 24 suites, 0 disagreements (list below) |

Rows by crate: ir 32, arith 6, bv 15, cas 63, cnf 74, solver 409. No
`proptest!` or `quickcheck` exists in these crates; every generator is a
hand-rolled LCG, an exhaustive literal sweep, or a seed list.

## The mechanism behind most of the 328

Every fuzz generator in the six crates is the MMIX LCG
`state ← state·6364136223846793005 + 1442695040888963407 (mod 2^64)`, and 81
files repository-wide returned the STATE itself from `next_u64`. Bit `k` of an LCG modulo 2^64
with odd multiplier and increment has period `2^(k+1)`: bit 0 alternates on
every draw, so `flip()` / `& 1` / `below(2)` at a fixed draw offset from the
seed is a CONSTANT, two consecutive `below(2)` draws are anti-correlated with
certainty, and `below(4)` / `below(8)` cycle with period 4 / 8. When a corner's
seeds are congruent modulo an even number (`seed % 12`), the constant is the
same for every seed of the corner.

What that did, measured by replicating each generator for its configured run
(the class column; the old count; the count after the fix, from the probe):

| generator | class the fuzz could not emit | old | new |
| --- | --- | ---: | ---: |
| `qf_lia_differential_fuzz` | `DivByConstZero` asserted POSITIVELY — the satisfiable `(div p 0) = c` shape, the a946f925 defect's own | 0/80 | 44/80 |
| same | `DivZeroCongruence` with `a == b` (the documented "companion sat pair") | 0/80 | 38/80 |
| same | `ExtremeConstant` at `i64::MIN` / `i32::MIN` / `i32::MAX` | 0/80 | 22 / 15 / 16 |
| same | `StrictTightening` positive, or `>` | 0/80 | 35 / 44 |
| `quantified_bv_differential_fuzz` | a body that mentions a bound variable | 0/600 | 552/600 |
| same, nested sweep | `Shape::NotForall` | 0/400 | 98/400 |
| `nia_differential_fuzz` | a `mod` op; a negative divisor | 0/2500 | 401 / 364 |
| `qf_lra_differential_fuzz` | `=`, `<`, `>` asserted positively | 0/5280 atoms | 421 / 407 / 409 |
| `qf_nia_divmod_const_differential_fuzz` | `div` by a positive constant; `mod` by a negative one; other nesting orders; the double-zero chain | 0/4156 terms | 1073 / 699 / 429+451+457 / 249 |
| `qf_uf_differential_fuzz` | `x = y` between variables; `f(f(t))`; a congruence pair in one instance | 0/1500 | 74 / 558 / 5 |
| `qf_uflra_differential_fuzz` | an equality applied on both sides; any positive equality | 0/1500 | 515 / 914 |
| `qf_ufnra_differential_fuzz` | `x·y` with distinct variables; a three-variable monomial | 0/700 | 258 / 84 |
| `qf_dt_differential_fuzz` | a positive `v0 = v1`; a negated tester | 0/1500 | 948 / 950 |
| `abv_differential_fuzz` | a nested store in an array atom | 0/2500 | 611/2500 |
| `quantified_uf_fmf_differential_fuzz` | a compound quantifier body; a nested quantifier | 0/150 | 41 / 8 |
| `interpolant_fuzz` | EUF `t != t`; disjoint A/B vocabulary; an odd BV constant | 0/800, 0/800, 0/300 | 244 / 13 / 197 |
| `word_equation`, `qf_s_online`, `online_string_front_door` | a literal with a repeated adjacent letter (`aa`) | 0/600, 0/1500, 0/1500 | 563 / 1473 / 1474 |
| `vivify` (5 tests), `cdclt.rs`, `cdclt_{lia,lra}_online` | a clause with both polarities | 0 of 2800+ / 0/7019 / 0/3488 | ~2400 per seed / 2020 / 1885 |
| `gf2.rs` reason-subset fuzz | two distinct rows in one system | 3 distinct systems in 4000 | 3395/4000 |
| `lia_online.rs` push/pop fuzz | an explicit pop (case 1 of the schedule) | 0/7200 steps | 1662/7200 |
| `bounded_completeness_fuzz` | a bound exactly one past the cap | 0/500 | 3/500 (19 of 20 distinct bounds, was 5) |
| `wide.rs` (3 tests) | any operand pair but one at widths 1 and 2 | `(0,0)` 200/200, `(2,0)` 200/200 | all 4 / all 16 pairs |
| `check_qf_bv_faithfulness` (**production**, its seed is in the certificate) | a symbol with low bit 1; a zero divisor at width 6 | never, at every seed | both, every seed |

## What was done about it

1. **The generator fix** — one line per file: the state update is kept (seeds
   stay seeds), the OUTPUT passes through SplitMix64's finalizer. Applied to 24
   generator files and the production sampler (`git show --stat` of the
   lane's commits lists them).
2. **A reachability probe per fixed file** — `the_generator_reaches_<class>`
   regenerates the configured population by CALLING the fuzz's own generator
   (a probe over a replica stays green while the shipped generator regresses;
   the faithfulness probe was first written that way and rewritten), counts the
   previously-dead classes, and asserts a floor of about a quarter of the new
   count. No solver call, so it runs in every feature configuration.
3. **A mutation control per probe** — reverting the finalizer must kill
   exactly the probe. Two subject mutants were added where a class-specific
   defect exists: a bit-0-only carry defect in the bv adder (invisible to the
   old faithfulness sampler; killed 2, both faithfulness integration tests) and
   `bvsdiv` by zero of a negative dividend (killed 1).
4. **Seed classes** where the gap was the box, not the LCG, and the class is
   one CLAUDE.md's hard rule names: `wide.rs` now emits `(0,0)`, `(1,1)`,
   `(ones,ones)`, `(INT_MIN, -1)`, `(INT_MIN, 0)`, `(x, 0)` ahead of the random
   draws in every width, plus the full-width extract and the extension that
   lands exactly on 128 bits; `inprocess_proof_path.rs`'s corpus gains the empty
   input clause its doc had claimed for the corpus's whole life, and a probe
   derives the degenerate shapes from the corpus rather than a name list.
5. **A ratchet** — `scripts/check-lcg-raw-state.py` pins the remaining
   raw-state return sites (56 files / 64 sites after this lane; 81 files / 89
   sites at `main`, measured with the same checker) in `scripts/lcg-raw-state-baseline.txt`; a new site, a grown count, or a
   stale entry fails it. Registered in the pre-push L0 block, `check.sh` and
   `just check`; five guards, each a mutation control that kills exactly one
   of its seven unit tests.
6. **ADR-2141** records the decision.

## Two things the widened boxes found on the SUBJECT side

**A defect in a test's own reference.** The `(INT_MIN, INT_MIN)` pair at width
128 made `extended_ops_match_u128_reference` panic in its REFERENCE (`sb.abs()`
at `i128::MIN`); `WideUint::smod` was right. The reference is now total over
magnitudes. A class that was never formed was never checked on either side.

**STOP finding — `LiaTheory` loses a shadowed assertion on pop.** With the
schedule now reaching explicit pops and opposite-polarity re-asserts,
`tests/lia_online.rs::differential_fuzz_push_pop_assert_sequences_agree` fails
deterministically:

```
DISAGREEMENT seed 9: theory reported no conflict but the live set is
offline-UNSAT (live=[(0, true), (1, false), (2, false), (3, true)])
```

Reproduced directly against the theory (temporary probe, not kept):

```
x >= 10 (atom 0), x <= 0 (atom 1)
push; assert(0, true)        -> Ok      (x >= 10 live)
push; assert(0, false)       -> Ok      (silent overwrite, no conflict reported)
pop
assert(1, true)              -> Ok      (x <= 0 accepted: the outer x >= 10 is gone)
```

`LiaTheory::assert` (`crates/axeyum-solver/src/lia_online.rs`, the
`TheorySolver` impl) overwrites an opposite-polarity live assignment in place
and logs only the atom INDEX; `pop` then sets the atom to `None` instead of
restoring the shadowed outer value. `LraTheory` (`lra_online.rs`) has the
identical `assigned_log`-of-indices shape; its fuzz did not reach the sequence
(its schedule locks to a different cycle and checks only the SAT direction —
inventory rows for `tests/lra_online.rs`). Whether the shipped CDCL(T) driver
can ever issue that sequence is not established here (a SAT trail never holds
both polarities, so probably not), but the trait contract — "assertions
accumulate until the next pop; pop undoes every assertion back to the most
recent push" — is violated by a `pub` implementor. Per the brief the subject is
untouched and the suite is left red on the branch; the fix belongs to the
theory's owner (restore the shadowed value on pop, or reject the
opposite-polarity re-assert as a conflict).

## Mutation controls

| suite | mutations | result |
| --- | ---: | --- |
| `proptest-box-faithfulness-sampler` | 1 | killed 1 (the probe) |
| `proptest-box-faithfulness-lsb-defect` (subject: bv adder bit 0) | 1 | killed 2 (both faithfulness integration tests) |
| `proptest-box-wide-generator` | 2 | killed 1, killed 1 |
| `proptest-box-inprocess-empty-clause` | 1 | killed 1 |
| `lcg-raw-state` (the ratchet's own guards) | 5 | killed 1 ×5 |
| `proptest-box-*` helper suites (24, one finalizer revert each) | 24 | 24 baselines green (1 test each), every revert killed exactly its probe (`mut-helpers.log`) |

`python3 scripts/tests/mutation_controls.py --check-anchors`: stale=0.

## Oracle sweeps re-run on the changed populations

Every fixed suite was rebuilt with `--features z3` and run from the binary
(wall times from the helper reports): qf_lia 960/0 disagree 31.8 s; nia
2500/0 54.1 s; qf_lra 1500/0 25.2 s; divmod_const 788 jointly/0 9.2 s;
divmod_var 1157 jointly/0 910.6 s; quantified_bv 600+400/0 4.5 s; qf_uf
1500+1500/0 54.6 s; qf_uflra 1500/0 30.7 s; qf_ufnra 667 agree, 33 unknown, 0
disagree 110.4 s; quantified_uf_fmf 150/0 1.4 s; interpolant_fuzz 5 tests/0
Craig failures 1.0 s; qf_dt 1500/0 2.7 s; abv 2493 jointly/0 158.5 s;
word_equation 570 jointly/0 390.8 s; qf_s_online 504 jointly/0 429.4 s;
online_string_front_door 1393 jointly/0 490.0 s; bounded_completeness 3
tests; cdclt_lia_online 2418 agree/0 0.8 s; cdclt_lra_online 2439 agree/0
0.4 s; cdclt termination 20000 runs/0 wrong; vivify lib 11 tests/0
disagreements; vivify suite 5/0; gf2 24 tests; faithfulness 4 tests (1500
samples agree); wide 15 tests; inprocess_proof_path 11 tests (60 refutations
checked and elaborated, was 54); lia_online 7 of 8 — the STOP finding.

Two populations now carry more `unknown`s than before (divmod_const 712/1500,
qf_s_online 996/1500 declined by axeyum): the new shapes reach routes that
decline. Capability, not soundness; both suites' own decided-count floors hold.

## What was NOT done, by name

* The 273 `structural-open` rows: width lists stopping at 8, divisor magnitudes
  `2..=4`, factor caps of 2, `{a,b}` alphabets with no `\u{…}` escape or code
  point above 0xFF (the ba0d9149 class CLAUDE.md's rule names — every string
  generator in the six crates), all-UNSAT instance lists, all-positive planted
  literals, RUP-only solver proofs (no checker's RAT path is fuzzed), CAS
  sweeps that stop below the i128 overflow point. Each row names the excluding
  literal; widening is a per-row decision and was not made silently here.
* The 56 files still returning a raw state (pinned in the baseline), 17 of
  them outside the six audited crates (`axeyum-fp`, `axeyum-strings`,
  `axeyum-lean-kernel`, `axeyum-rewrite`, `axeyum-cas`).
* `LraTheory`'s twin of the STOP finding was read, not fuzzed.

## Method notes

* Every `ran` row replicated the generator in Python or Rust (`rustc`, no
  cargo) for its configured seed range and instance count; the replicas live
  in the session scratchpad, not the repository. The two largest (qf_lia, nia)
  were cross-checked by an independent Rust replica with identical counts.
* Slices were inventoried by five helpers and fixed by four, each on a
  disjoint file set; every `no` row that led to a change was re-verified by
  the lane (the parity locks in `wide.rs`, `faithfulness.rs`,
  `quantified_bv_differential_fuzz.rs` and `qf_lia_differential_fuzz.rs` were
  re-derived and re-run by hand before any edit).
