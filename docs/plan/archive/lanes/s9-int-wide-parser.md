# Lane: s9-int-wide-parser — integer literals wider than `i128` reach the solver

<!-- plan-section: lane-status -->

**ADR-1702 slice 2 landed: the SMT-LIB front door admits an integer literal
outside `i128`, and every route that meets one declines with a named reason**
(`WIP`, s9-int-wide-parser, 2026-09-06, ADR-1702, ADR-0376). All 26 QF_UFLIA
files that carried EVM `uint256` bounds now parse and dispatch instead of being
refused at the parser. `TermNode::WideIntConst(WideInt)` and
`Value::WideInt(WideInt)` are sibling variants of the `i128` ones, exactly as
`WideBvConst`/`WideBv` already split at 128 bits.

**The parity plan's "+6 measured against cvc5" for row S9 is not supported, and
the measurement that says so was run before any code was written.** ADR-0376
deferred this widening in August on an ablation, not on cost: with every
out-of-range literal removed from the problem, the six files cvc5 decides were
*still* `unknown`, because the binding constraint is the decision procedure
(`MAX_INT_BLAST_WIDTH = 64`, and a measured magnitude cliff between `2^24` and
`2^32`) and not the literal type. That is a claim about a tree a month old, so
both arms were re-run on today's HEAD at 24 s, `taskset -c 0-7`: rescaling every
wide numeral to a distinct `2^60 + i` gives **6/6 `unknown`**, and deleting every
assert that mentions one (50–1,314 per file, matching ADR-0376's counts exactly)
gives **6/6 `unknown`**. The runner is not vacuous — it reports 2 `sat` and
2 `unsat` on four QF_UFLIA files we do decide. So the +6 is the count cvc5
decides, not a measured axeyum gain, and the honest expected yield of slice 2 on
QF_UFLIA is **0 decided files**.

**The census: 26 of 200, and it agrees with the parser in both directions.**
Two magnitude classes — 19 files with a 258-bit (78-digit) `uint256` bound and 7
with a 512-bit (155-digit) product bound — all declaring `:status unknown`. The
largest literal is always a comparison bound (enclosing head `>` in 16 files,
unary `-` in 7, `<` in 3), never a coefficient. Wide literals are dense: 170 at
the lightest, median 1,054, 11,005 in the heaviest. Because the census is a scan
and not the parser, it was cross-checked against the front door over the **whole
200-file population** rather than its own hits: `explain_corpus` classifies
exactly 26 as `kind: wide-integer-literal`, zero difference either way.

**The design deviates from the brief, deliberately, toward the one ADR-0376
already recorded.** The brief asked for `Value::Int` to take the shape ADR-1702
gave `Rational` — a payload with a fast and a promoted path. That worked for
`Rational` because it is a `struct` consumed by value in ~5,500 places, so
keeping the layout kept the consumers. `Value::Int` is an enum *variant*, and
the analogous move for a variant is a SIBLING variant: changing the payload
breaks all ~390 `Value::Int` and ~210 `IntConst` sites and, per ADR-0376, turns
every `arena.int_const(0)` on the hot LIA path into a heap allocation. With the
sibling those sites are *stronger* than "panic rather than truncate" — they
cannot observe a wide value at all. `WideInt::to_i128` still panics rather than
truncating, and `Value::as_int` returns `None`.

**The real defect found was a panic on user input, in the evaluator.**
`int_bin`/`int_cmp` and eleven siblings read operands with
`as_int().expect("builder guaranteed Int operand")`, and `as_int` is `None` for
a wide value — so a parsed `2^256` would have panicked on the one path every
`sat` is replayed through. `eval` now takes a wide-integer detour mirroring the
wide-BV one beside it. Promotion is decided **per node, from the operand
values**: two narrow operands keep the pre-ADR-1702 checked path and still
report `ArithmeticOverflow` on `(+ i128::MAX 1)` even inside a query carrying
`2^256` elsewhere, while any wide operand makes that application exact and the
result demotes when it fits. The fuzz's first run corrected the lane's own
assumption here, on seed 7.

**The audit was compile-driven, which is the point of the sibling design.**
Adding the two variants broke 62 `match` sites across 13 crates; the compiler
enumerated the audit instead of a grep guessing at it. Every site resolved as a
decline or an exact rule, never a narrowing — notably `IntInterval` bound
extraction returns `None`, because saturating a `2^256` bound into an `i128`
interval would be a *wrong* bound rather than a coarse one.

**Nothing has opted in, and `Features::has_wide_int` is where a route says so.**
`wide_int_admission` declines at the dispatch boundary with a named `unknown`.
It changes no verdict — every route already fails closed, and
`ArithAbstractor::ensure_supported_atom` re-runs the linearizer before an atom
becomes a Boolean proposition, so a wide-bearing atom cannot become an opaque
literal the CDCL(T) loop satisfies vacuously. What it changes is cost and
explanation: without it a 15 MB Certora file walks the whole ladder and burns the
full 24 s budget before every rung declines for the same reason (measured on
`3106_1c933134166dbad31f79_38`). Opting the LIA route in is out of scope and the
ablation says why — it would decide nothing here, and `IntCollector::linearize`
is on every LIA query's path.

**A defect in the shared mutation harness, found and fixed.** A
`#[should_panic]` test prints `test NAME - should panic ... FAILED`, and
`_CARGO_DEATH` was `^test (\S+) \.\.\. FAILED$`, so the harness could not NAME
the dying test and reported `INCONSISTENT` instead of a result. It therefore
could not measure a panic contract at all, for any suite, and this repository has
many. One regex plus the matching self-table anchor.

**NOT DONE, and the lane stops here on a wrap-up instruction.**

- **The 26-file before/after measurement did not run.** Both arms are built and
  confirmed different by `sha256sum` (`before` from `lane-snapshot.sh` at the
  merge-base `0f305782c`), the interleaved runner and both populations are
  committed, and the run is ~20–25 min. So there is no reach-the-solver count,
  no decided count, no PAR-2 and no verdict-change check from this lane, and
  none is claimed. The sidecar population is ready too: the 58 reference-only
  QF_UFLIA files from the S3 loss census, of which only 6 are the wide-integer
  class (the other 20 of our 26 are absent because cvc5 does not decide them
  either).
- **Gates not run:** the WASM build, `cargo deny check`, the frontier ratchet,
  and the aggregate gate. Everything else in the brief's list ran; counts below.
- The `mutation-controls` self-suite cannot run end to end because its baseline
  control module is red on main for reasons that predate this lane (three
  ambiguous anchors in `cas-summation-and-gaussian`, one missing subject in
  `creal-migrate-consumers`), verified identical on a snapshot of the merge-base.

**Gates that ran, with counts.** `axeyum-ir` 169 (54+6+83+13+7+2+2+2) green;
`axeyum-smtlib` 342 (90+5+246+1) green; `axeyum-solver --lib --features full`
**1456** green; `--features full --test corpus_regression` 1 green; the three z3
differential fuzzes **5 / 1 / 1** green; `axeyum-cas --lib` **2081** passed,
0 failed, 9 ignored — well clear of the 1228 floor, which is the point, since
that crate is the one global promotion broke; `check --workspace --all-targets
--all-features` clean; `clippy -p axeyum-ir -p axeyum-smtlib -p axeyum-solver
--all-targets --all-features -- -D warnings` clean; `cargo fmt --all --check`
clean; `check-links.sh` all ok; `check-merge-hygiene.sh` PASS.
`check-parity-docs.py` exits 1 with **81 errors before and 81 after**, the same
set except an examples-inventory count that moved 233→238 in the merged main —
pre-existing and not this lane's.

**Mutation controls: five mutations, each killing exactly one test.**
`to_i128` truncating and `to_i128` saturating each kill
`to_i128_panics_rather_than_truncating_a_wide_value`; wide `mod` returning the
quotient, wide `div`-by-zero returning the dividend, and the wide path not
demoting each kill
`integer_evaluation_matches_a_bigint_reference_across_the_i128_boundary`.

<!-- plan-section: landed-changes -->

| 2026-09-06 | `af8a1d550` | The census of the 26 QF_UFLIA files (largest literal's bit length, digit count, occurrence count, syntactic position), cross-checked against the real front door over the WHOLE 200-file population in both directions with zero difference; plus ADR-0376's two ablation arms re-run on today's HEAD, both reproducing 6/6 `unknown`. |
| 2026-09-06 | `c04442c28` | `TermNode::WideIntConst(WideInt)` and `Value::WideInt(WideInt)` with the canonicality invariant enforced by demoting constructors, `WideInt::to_i128` panicking rather than truncating, and evaluator/renderer/stats support. |
| 2026-09-06 | `f19800cdb` | The 62-site compile-driven audit: exact `BigInt` evaluation for the operators that have one and `IrError::Unsupported` for the rest, closing a panic-on-user-input in `eval`; `IntBlastError::WideConstantOutOfRange`; a decline at every other route boundary rather than a narrowing. |
| 2026-09-06 | `2395a0518` | The parser admits the literal through `int_const_big`; `Features::has_wide_int` plus `wide_int_admission` decline at the dispatch boundary by name; `explain_corpus`'s now-unfireable wide-integer classifier deleted and its test replaced by one asserting the opposite contract; ADR-1702 gains a "Slice 2" section. |
| 2026-09-06 | `22417ec99` | A seeded differential fuzz for integer evaluation across the `i128` boundary against an independent `BigInt` reference, including `div`/`mod` by constant zero at wide magnitude; its first run corrected the lane's own model of the per-node promotion rule. Plus the interleaved before/after runner and the sidecar population. |
| 2026-09-06 | `417475af5` | Two mutation suites (five mutations, each killing exactly one test) and the `#[should_panic]` name the mutation harness could not read. |
| 2026-09-06 | `d9454e28e` | Clippy-clean across the three crates at `-D warnings`, including removing an error channel from `apply_wide_int` that nothing could put anything into. |
