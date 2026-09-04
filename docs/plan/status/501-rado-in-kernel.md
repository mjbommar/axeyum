# Lane: rado-in-kernel — W1-1: define Rado numbers in-kernel and close the computed→proved gap

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, rado-in-kernel, 2026-09-04).** Roadmap item W1-1,
the C2 convergence (07.1, 11.1, 12.4). `Nat.Rado` now defines the object the
ledger's two `computed` four-colour Rado numbers are values of, and
`R_2(x = y + z) = 5` is closed end to end from search. ADR-1596.

**Seventeen declarations, every one admitted on the first attempt with an empty
`Kernel::axiom_footprint`.** Definitions: `Sol a b x y z := a*x = a*y + b*z`
(subtraction-free — see below), `IsColouring`, `MonoSol`, `Arrows`,
`IsRadoNumber`, `ofFinset`, `schurSet`. Theorems: `Nat.boolSelect_lt`,
`isColouring_ofFinset`, `inRange_of_le`, `isColouring_of_le`, `monoSol_of_le`,
`arrows_of_le`, `isRadoNumber_of_succ`, `schur_arrows_five`,
`schur_not_arrows_four`, `schur_two`.

**The finding, and it reverses the assumption the roadmap carried in.** W1-1's
note says "unary numerals, so the constant 625 cannot be *formed*". Measured:
`Nat.Rado.IsRadoNumber 5 3 4 625` **type-checks**, in the same test fixture and
the same budget as everything else in `rado_tests.rs` (16 tests, 1.62 s total).
The superlinear cost this repository documents is a cost of REDUCTION — that is
why `decide`'s `MAX_MAGNITUDE` is 30 — and a `Prop` that merely mentions a
numeral neither reduces it nor unfolds anything. So the ledger's two results are
stateable in this kernel today, verbatim. **The residue is the proof term, and
it is combinatorial, not numeric:** `Arrows 5 3 4 625` needs a term ranging over
`4^625` colourings, and colourings are *functions*, so they are not enumerable
in-kernel at all — the `Nat.lt_two_cases` tree that works at `k = 2` has `k^n`
leaves. The lower half at 624 is the reachable frontier: the same
`Nat.Finset.allBelow` reflection route, `2.4e8` triples, polynomial.

**What a future certificate has to hand over is named exactly.**
`isRadoNumber_of_succ : Arrows a b k (succ m) → (Arrows a b k m → False) →
IsRadoNumber a b k (succ m)`, with `m` a variable throughout. Those two
hypotheses are the two halves a Rado search already produces.

**The next increment, unblocked and cheap:** Chang–De Loera–Wesley's Lemma 4.1
(`R_k ≥ a^k` by the `a`-adic valuation colouring, for `gcd(a,b) = 1`) is a
*parameterized* statement whose proof forms no constant at all, and it would
back the lower half of `F:rado-r4-a5-b3` as a theorem rather than a replay.

**Gates, each with its count.**

| gate | result |
|---|---|
| `cargo test --release -p axeyum-lean-kernel --lib nat_prelude::` | 460 passed / 0 failed (was 441 before the finset-pigeonhole merge) |
| `… --lib nat_prelude::rado` | 16 passed / 0 failed, 1.62 s |
| `cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D warnings` | exit 0 |
| `cargo check --workspace --all-targets` | exit 0 (a prelude-struct change is not a kernel-local change; `axeyum-py`'s generated `prelude_fields.rs` is regenerated) |
| `python3 scripts/gen-py-prelude-fields.py --check` | `nat=1212`, OK up to date |
| `python3 scripts/validate-facts.py` | 2759 facts, **0 errors** |
| `kernel_declaration_projection`, before vs after | **153 rows added, 0 removed, 0 added rows that are not this lane's** (17 declarations × 9 prelude groups), every footprint column `0` |
| `rustfmt --edition 2024` on both new files | clean |
| `scripts/check-merge-hygiene.sh` | ran; the three generated artifacts it named stale are regenerated in this lane's last commit |

**Build cost, measured PAIRED rather than before-and-after.** The unpaired
figures were badly misleading: `shape_search`'s `build=` read 4.6–5.6 s before
the module and 8.0–18.5 s after, which looks like a 3x prelude regression and is
not one. Two binaries (with and without `declare_rado_all`) run **interleaved**,
six rounds each, load 13–18: min 5.4 s WITHOUT, min 5.4 s WITH. The module's
cost is not resolvable above this box's noise floor. This is the
frontier-ratchet reference-frame lesson applied to a build time.

**Mutation controls** (`scripts/tests/mutation_controls.py rado-in-kernel`, six
mutations, all `killed N`, no survivors and nothing unmeasured):

| mutation | killed |
|---|---|
| `ofFinset` is the indicator and not its swap | 13 |
| `Sol` reads the `b` coefficient | 2 |
| `Sol` reads the `a` coefficient on the middle term | 2 |
| the search's own solution predicate reads `b` | **1** |
| the `schurSet` membership chain is not branch-swapped | 13 |
| `boolSelect_lt` hands `Bool.rec` its minors in (false, true) order | 13 |

The killed-sets have **two shapes, and that is the reading**. A corrupted
DEFINITION still type-checks — the prelude builds, the footprint stays empty,
and only the specific test that evaluates it dies (rows 2, 3, 4). A corrupted
CERTIFICATE is refused by `Kernel::add_declaration`, `build_nat_prelude` fails,
and all 13 tests that construct a kernel die at once (rows 1, 5, 6); the 3 that
survive are exactly the pure-search tests, which build no kernel. So the guard
on the certificate is the trusted gate itself and it fires before any assertion
does.

Two rows share a killed-set (`Sol`'s `a` and `b` coefficients kill the same two
tests), so the pair is load-bearing but does not separate *which* coefficient
was dropped. Recorded rather than papered over.

**Owned files:** `crates/axeyum-lean-kernel/src/nat_prelude/rado.rs`,
`rado_tests.rs`, the `Nat.Rado` block of `nat_prelude.rs`,
`artifacts/facts/F-rado-r2-schur-two.json`, ADR-1596, and the
`rado-in-kernel` suite in `scripts/tests/mutation_controls.py`.

**Did not run:** `just check` / `./scripts/check.sh` in full, and the workspace
test sweep. `nat_prelude::` is the suite this lane's change can break and it is
green at 460; the workspace `check --all-targets` covers the generated-consumer
hazard a prelude-struct change carries.

<!-- plan-section: landed-changes -->

| 2026-09-04 | rado-in-kernel | `Nat.Rado`: 17 axiom-free declarations defining Rado numbers; `schur_two : IsRadoNumber 1 1 2 5` reconstructed from search on both halves; ADR-1596 |
| 2026-09-04 | rado-in-kernel | measured: `IsRadoNumber 5 3 4 625` type-checks — the residue against the ledger's `computed` rows is the PROOF term, not the unary numeral |
| 2026-09-04 | rado-in-kernel | new fact `F:rado-r2-schur-two` (`proved`, `kernel-lean`, empty footprint); `F:rado-r4-a5-b3`/`-b4` stay `computed` with the residue recorded |
