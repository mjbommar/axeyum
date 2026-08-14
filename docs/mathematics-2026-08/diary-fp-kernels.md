# Diary — certified floating-point kernel equivalence (lane `fp-kernels`), 2026-08-14

A new domain in the fact ledger: **does an optimized or quantized kernel agree
with its reference on all inputs?** The industry answers that by sampling. At
fp8, bfloat16 and binary16 the input space is small enough to answer it
*exhaustively*, and `crates/axeyum-fp` is generic over `(exp_bits, sig_bits)`
per ADR-0023, so those widths come free.

Seven facts landed: four `proved`, two `refuted` with pinned witnesses, and one
deliberately left `open` as a measured parity target. Every *settled* one is
established by **two routes that share no code**: axeyum's SMT front door
(`fp.*` → fpa2bv → CNF → DRAT) and an exhaustive enumeration against
`rustc_apfloat` — LLVM's own `APFloat`, already admitted by ADR-0028 as the
dev-only reference oracle.

| fact | status | route | scope |
| --- | --- | --- | --- |
| `F:fp16-doubling-add-equals-mul-two` | proved | `smt-clausal` | exhaustive at binary16 (2^16), all 5 modes |
| `F:fp32-doubling-add-equals-mul-two` | proved | `smt-clausal` | exhaustive at binary32 (2^32) **and** symbolic |
| `F:fp16-fp32-roundtrip-identity` | proved | `smt-clausal` | exhaustive at binary16 (2^16) |
| `F:fp8-add-monotone-rne` | proved | `smt-clausal` | exhaustive at fp8 E5M2 (2^24 triples, all 5 modes) **and** symbolic |
| `F:fp8-add-not-associative` | refuted | `search-certificate` | exhaustive at fp8 E5M2 (2^24 triples), all 5 modes |
| `F:fp16-bf16-roundtrip-not-identity` | refuted | `search-certificate` | exhaustive at binary16 (2^16) |
| `F:fp16-add-monotone-rne` | **open** | — | neither exhaustive nor symbolic here; both oracles prove it |

---

## The finding: at the width where brute force works, the oracles don't

The whole premise of this lane is that fp8 is small enough to settle a claim
completely. It turns out that is exactly the width where the two industrial FP
solvers a practitioner would reach for both decline — for two *different*
reasons, neither of which is a timeout:

```sh
$ z3 -smt2 artifacts/facts/smt2/fp8-add-not-associative.smt2
unknown
(:reason-unknown "addition/subtract with ebits > sbits not supported")

$ references/smtcomp-solvers/bitwuzla artifacts/facts/smt2/fp8-add-not-associative.smt2
[error] Unsupported experimental floating-point format
        (non-experimental: Float16, Float32, Float64, Float128),
        enable experimental FP formats with build configuration option --fpexp.
```

* **z3 4.13.3** refuses every fp8 E5M2 *addition* query, because E5M2 is
  `(_ FloatingPoint 5 3)` and 5 > 3. Its fpa2bv tactic has no path for
  `ebits > sbits`. This is not specific to associativity — it hit the doubling
  claim and the monotonicity claim identically.
* **bitwuzla 0.9.1** refuses the *format*. The `--fpexp` escape named in its own
  error message is a **build** option, not a runtime flag; passing it to the
  binary gets `[error] invalid option '--fpexp'`, so this build cannot be talked
  into it. (Worth reading that message carefully: it names a flag you cannot
  use.)

axeyum decides every fp8 E5M2 query this lane wrote, and the LLVM-APFloat
enumeration confirms each answer:

| fp8 E5M2 query | axeyum | z3 4.13.3 | bitwuzla 0.9.1 | APFloat |
| --- | --- | --- | --- | --- |
| `x+x = 2*x` | `unsat`, certified, 12 ms | `unknown` | format refused | 256/256 agree |
| `(a+b)+c = a+(b+c)` | `sat` + model, 27 ms | `unknown` | format refused | 427 036 of 2^24 fail |
| monotonicity | `unsat-drat`, recheck ok, 25m46s | `unknown` | format refused | 7 843 500 guarded, 0 fail |

So on this axis the pure-Rust stack is not at parity with z3 — it is *ahead of*
z3 and bitwuzla, and the reason is the ADR-0023 decision to make the FP builders
generic over `(exp_bits, sig_bits)` instead of enumerating the standard
interchange formats. It is also the axis where a wrong answer would be hardest
to catch, which is why every fp8 row above has the enumeration beside it.

The gap runs the other way too, and it is worth recording because it is *us*
being conservative rather than them:

```
$ smtcomp_cli --evidence <(_ FloatingPoint 4 4) file>   → unknown
  Ir(Unsupported("fp.add: unvalidated format"))
```

fp8 **E4M3** is `(_ FloatingPoint 4 4)`. z3 accepts it happily; axeyum refuses,
because `FloatFormat::is_ieee` excludes it — E4M3 has no infinities and encodes
NaN as all-ones, so IEEE-754 arithmetic is simply not its semantics. Every claim
in this batch therefore uses **E5M2**, the IEEE-conformant 8-bit layout. An fp8
claim that does not say which fp8 is not a claim.

---

## The counterexample worth having

`F:fp8-add-not-associative` is refuted, and the witness is a double tie:

```
a = b = 0x01   the E5M2 subnormal 2^-16
c     = 0x08   the normal 2^-13

a+b       = 2^-15                    exact
(a+b)+c   = 2^-13 · 1.25   = 0x09    exact
b+c       = 2^-13 · 1.125  → tie, RNE breaks to even → 0x08
a+(b+c)   = 2^-13 · 1.125  → tie again                → 0x08
```

Two ties resolving the same way is what separates the bracketings. It is pinned
as a **ground** SMT-LIB file (`fp8-add-not-associative-witness.smt2`, no free
symbols), so a `sat` verdict there is direct evaluation rather than a search,
and the fact cannot drift from the solver. z3 *can* settle that ground instance
even though it returns `unknown` on the search — its refusal lives in the
symbolic fpa2bv tactic, and a closed term is constant-folded before that tactic
is reached. That is not a contradiction, and it is the only cross-check on that
witness that exists.

What the exhaustive sweep adds that folklore does not is the **density**, per
rounding mode, over all 16 777 216 triples:

| mode | failing triples | share |
| --- | --- | --- |
| RNE | 427 036 | 2.5% |
| RNA | 419 652 | 2.5% |
| RTP | 4 825 040 | 28.8% |
| RTN | 4 825 040 | 28.8% |
| RTZ | 5 375 600 | 32.0% |

The directed modes are an order of magnitude worse, and RTP/RTN failing equally
often is the sign symmetry of the format. "Floating-point addition is not
associative" is an aphorism; *nearly a third of fp8 triples under
round-toward-zero* is a number a kernel author can act on.

---

## The pair that makes the round-trip question a question

These two facts have the same shape and opposite answers, and that is the point:

* `F:fp16-fp32-roundtrip-identity` — **proved**, 0 failures of 65 536. binary32
  dominates binary16 on *both* axes (24 significand bits against 11, and a
  strictly containing exponent range), so the trip is exact.
* `F:fp16-bf16-roundtrip-not-identity` — **refuted**, **54 784 of 65 536 =
  83.59%** do not come back. Smallest witness: `0x0101`, the binary16 subnormal
  257·2^-24, which needs 9 significand bits where bfloat16 keeps 8, returning as
  `0x0100`.

Note *why* the bfloat16 trip fails. bfloat16's exponent field is binary32's, so
it contains binary16's range entirely — nothing overflows to infinity, nothing
flushes to zero. Every one of the 54 784 failures is pure significand loss.
bfloat16 is not the worse format; range is simply not what a round trip needs.
Five values in six is not a corner case, and a pipeline that stages binary16
activations through a bfloat16 buffer is wrong about most of them.

---

## Arity, not width, is what makes brute force available

The brief anticipated "exhaustive at fp8/bf16 and symbolic-only at fp32" as the
honest distinction. Measured, the line falls somewhere else.

`F:fp32-doubling-add-equals-mul-two` is settled **both** ways:

```sh
# symbolic: bit-blast a miter of the two circuits and refute it
$ smtcomp_cli --evidence artifacts/facts/smt2/neg-fp32-doubling-add-equals-mul-two.smt2
; evidence kind=unsat-drat certified=1 recheck=ok arena=ok ms=116653
unsat                                                    # 3m22.7s

# brute force: every one of the 2^32 encodings
$ cargo run --release -q -p axeyum-fp --example kernel_equivalence -- doubling-fp32
  AGREES  fp32 (8,24) RNE, exhaustive 2^32  examined=4294967296 failures=0   # 51.4s
```

A *unary* claim at binary32 is 4.3 billion points and brute force wins on wall
clock. What is out of reach is the *ternary* claims: 2^24 triples at fp8 is
seconds, 2^48 at binary16 is not, and 2^96 at binary32 never will be. So the
honest scope statement is per-fact and turns on arity, and every fact in this
batch states which.

That same run is also the least flattering measurement here: on the symbolic
route, **axeyum 202s versus z3 0.1s and bitwuzla 0.1s** on the identical file.
A 2000x gap to the specialised FP solvers, recorded in the fact rather than
elsewhere.

---

## One fact is `open` on purpose, and that is the parity number

Monotonicity of rounded addition — `a ≤ b ⇒ a+c ≤ b+c`, guarded so no result is
NaN — is the property that licenses interval and bound propagation through a
kernel. At fp8 E5M2 it is settled here **twice**: 7 843 500 of the 16 777 216
triples pass the guard and none violates the consequent, under all five rounding
modes, in about three seconds — and independently by bit-blasting the guarded
miter, `unsat-drat certified=1 recheck=ok`, in 25m46s. Neither oracle can read
that query at all, so this is a claim axeyum proves and z3 and bitwuzla cannot
state.

**I nearly wrote the opposite.** At the 25-minute mark that solve was still
going and I had already drafted the fact, the target file and this diary around
"axeyum does not decide it". It landed at 25m46. Everything in this section is
the corrected version, and the correction only happened because the run was left
to finish rather than summarised from its first twenty minutes. *Prefer a
measurement over a message* includes messages you wrote yourself.

At binary16 the same claim is where the gap actually is:

```sh
$ z3 -smt2      artifacts/facts/smt2/neg-fp16-add-monotone-rne.smt2   # unsat, 30.6s
$ bitwuzla      artifacts/facts/smt2/neg-fp16-add-monotone-rne.smt2   # unsat,  8.3s
$ smtcomp_cli --evidence artifacts/facts/smt2/neg-fp16-add-monotone-rne.smt2
                                                                      # AXEYUM-FP16-RESULT
```

2^48 triples puts brute force out of reach, so binary16 has only the symbolic
route, and there the two specialised solvers finish in seconds. So
`F:fp16-add-monotone-rne` is recorded with `epistemic_status: open`,
`external_status: proved`, an **empty evidence array**, and the two oracle
timings under `provenance.prior_art` rather than as evidence. Filling in
evidence rows would make the ledger claim axeyum did work it did not do.

That is the shape of an honest parity entry: a proposition, a reproducible file,
a competitor's wall-clock number, and no evidence of our own. Nothing about the
mathematics is in question — the entire gap is throughput on a multi-operand
comparison miter.

---

## Two routes, and what each one actually rests on

The `axiom_footprint` of every `proved` fact in this batch names axeyum-fp's
`add` and `mul` bit-blasters as **validated, not proven**, because that is what
`crates/axeyum-fp/src/lib.rs` says about itself:

> This is a validated — not formally proven — bit-blaster: differentially
> validated against native `f32`/`f64` addition and `rustc_apfloat`'s quad
> (ADR-0028) in tests.

An SMT verdict on an FP query is worth exactly that lowering. Which is precisely
why every settled fact carries a second evidence row that evaluates the *same*
proposition without going through the lowering at all —
`crates/axeyum-fp/examples/kernel_equivalence.rs`, decoding each encoding with
LLVM's APFloat. Two routes agreeing is the evidence; one route asserting is not.

Three details in that enumerator are load-bearing and easy to get wrong:

1. **Equality is SMT-LIB `=`, not `fp.eq` and not bit equality.** The
   `FloatingPoint` sort has exactly one NaN, and `+0`/`-0` are distinct values.
   Comparing raw APFloat bits would report spurious failures on NaN payloads in
   the round-trip facts; comparing with `fp.eq` would make a false claim look
   true, since `fp.eq NaN NaN` is `false`.
2. **The rounding mode is in every statement.** `--all-modes` re-runs the
   applicable claims under all five. Doubling and monotonicity hold under all
   five; associativity fails under all five with the densities above.
3. **A run that enumerates nothing is a failure.** The binary exits 2 on an
   unrecognised claim name and 1 on any disagreement — this repository has
   shipped several gates that exited 0 over zero work.

---

## The checker commands assert the verdict

The existing ledger convention is a bare invocation:

```json
"checker_command": "cargo run -q -p axeyum-bench --example smtcomp_cli -- --evidence <file>"
```

`smtcomp_cli` exits **0 on any decided verdict**, so that command passes whether
the answer is `sat`, `unsat`, or the opposite of what the fact records.
`scripts/check-fact-evidence-replay.sh` gates on the exit status, so it was
checking that the binary ran, not that the ledger was right. This batch wraps
each one:

```json
"checker_command": "test \"$(cargo run --release -q … --evidence <file> | tail -1)\" = unsat"
```

Controls, both required to be non-zero, both measured:

```sh
$ test "$(… --evidence fp8-add-not-associative.smt2 | tail -1)" = unsat   ; echo $?   # 1
$ test "$(… --evidence neg-fp16-doubling-…smt2     | tail -1)" = sat     ; echo $?   # 1
$ kernel_equivalence bogus-claim                                          ; echo $?   # 2
```

All 12 checker commands across the six settled facts run green from the
repository root, the most expensive in 34s. The whole gate:

```
fact-evidence-replay: 57 settled fact(s), 99 checker run(s), 0 failed, 0 uncovered, 251.8s
  route cas-certificate 8/8   kernel-lean 23/23   search-certificate 7/7
  route smt-clausal     4/4   smt-term-level 15/15
```

An earlier run of that same gate reported **1 failed** and took **747.7s**. The
difference was not the ledger: I was rebuilding the `kernel_equivalence` example
while it ran, and every `cargo run` checker blocks on the build lock. One of my
own checkers had already been measured at 1m49s of pure lock wait against the
gate's 180s per-checker budget. So this gate is **contention-sensitive, and its
failure mode is a timeout that looks exactly like a broken fact** — worth knowing
before anyone bisects one. Re-run with nothing else touching cargo: 251.8s, zero
failures, and identifying which fact failed required re-running it, because the
FAIL line is printed inline and a `| tail -40` on a 57-fact run drops it. Two evidence rows deliberately carry
*no* `checker_command` — the binary32 symbolic refutation (3m22s) and the fp8
monotonicity refutation (25m46s) — because a checker that blows the gate's
budget converts a pass into a timeout; each names the command to re-derive it by
hand, and each fact stays covered by a cheap row. The pre-existing facts are
another lane's to fix, but the hole is general and worth knowing about.

---

## Where this goes next

0. **Close `F:fp16-add-monotone-rne`.** It is the best-specified task this lane
   produced: the file is committed, two oracles settle it in seconds, and
   nothing about the mathematics is in question.
1. **Compensated summation.** A Kahan step versus naive addition over a bounded
   input set is the claim that would actually certify a reduction kernel, and it
   is the natural next one at fp8: the ternary domain is already known to be
   enumerable in seconds.
2. **The E4M3 gap.** axeyum refuses E4M3 for a correct reason, but E4M3 is the
   format most fp8 inference actually uses. Giving `axeyum-fp` non-IEEE
   `NonfiniteBehavior` (APFloat already models it) would open the more
   commercially relevant half of fp8 — and it is a format neither oracle can
   check us on, so the enumeration route stops being a cross-check and becomes
   the only check.
3. **The 2000x.** Symbolic FP is where this stack is furthest from parity. The
   binary32 doubling file is a small, reproducible, self-contained instance of
   it.
