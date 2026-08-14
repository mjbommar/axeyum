# Lane: fp-kernels — certified floating-point kernel equivalence

<!-- plan-section: lane-status -->

**A new fact-ledger domain: FP kernel equivalence, settled exhaustively where
the width permits (`WIP`, fp-kernels, 2026-08-14).** Landed seven facts — four
`proved`, two `refuted` with pinned witnesses, one deliberately `open` —
answering the question compilers, GPU kernels and quantized ML pipelines
currently answer by sampling: *does the rewrite agree with its reference on ALL
inputs?* `F:fp16-doubling-add-equals-mul-two`,
`F:fp32-doubling-add-equals-mul-two`, `F:fp16-fp32-roundtrip-identity` (proved),
`F:fp8-add-monotone-rne` (proved, exhaustively and symbolically), `F:fp8-add-not-associative`
and `F:fp16-bf16-roundtrip-not-identity` (refuted), and
`F:fp16-add-monotone-rne` (`open`, see below). Every settled one carries two
evidence routes that share no code: axeyum's SMT front door (`fp.*` → fpa2bv →
CNF → re-checked DRAT) and `crates/axeyum-fp/examples/kernel_equivalence.rs`,
an exhaustive enumeration against `rustc_apfloat` (LLVM's APFloat, ADR-0028).
These are the ledger's first `smt-clausal` facts.

`F:fp16-add-monotone-rne` is `open` with `external_status: proved` and an
**empty evidence array**, on purpose: z3 4.13.3 proves it in 30.6s and bitwuzla
0.9.1 in 8.3s, and 2^48 triples rules out brute force, so binary16 has only the
symbolic route. For calibration, axeyum DOES settle the fp8 analogue — which
neither oracle can read — in 25m46s. This is a measured parity gap written down
as a target rather than dressed as a result;
`artifacts/facts/smt2/neg-fp16-add-monotone-rne.smt2` is the reproducible file.

Three measurements worth carrying forward. **(1)** At exactly the width where a
claim can be brute-forced, both industrial oracles decline: z3 4.13.3 returns
`unknown` on every fp8 E5M2 *addition* query (`ebits > sbits not supported` —
E5M2 is `(_ FloatingPoint 5 3)`), and bitwuzla 0.9.1 rejects the format as
experimental, its own suggested `--fpexp` escape being a build option the binary
refuses as a runtime flag. axeyum decides both, because ADR-0023 made the FP
builders generic over `(exp_bits, sig_bits)`. The gap runs the other way for
E4M3, which axeyum correctly refuses as non-IEEE and z3 accepts. **(2)** Arity,
not width, decides whether exhaustive settlement is available: all 2^32 binary32
values enumerate in 51s, while the ternary fp8 claims are exhaustive at 2^24 and
would be 2^48 at binary16. **(3)** On the symbolic route this stack is 2000x off
the specialised FP solvers — binary32 doubling: axeyum 202s, z3 0.1s, bitwuzla
0.1s on the identical file.

Also found, and general rather than FP-specific: the ledger's existing
`checker_command` convention is a bare `smtcomp_cli --evidence <file>`, which
exits **0 on any decided verdict**, so `scripts/check-fact-evidence-replay.sh`
was gating on "the binary ran", not on the recorded verdict. This lane's eleven
checkers wrap the verdict in a `test "$(… | tail -1)" = unsat`, with both
wrong-verdict controls measured non-zero. Pre-existing facts are other lanes' to
repair; the hole is worth knowing about.

Next, in priority order: (1) close `F:fp16-add-monotone-rne` — it is the
best-specified task here, nothing about the mathematics is in question and the
whole gap is throughput on a multi-operand FP comparison miter; (2) a Kahan
compensated-summation step versus naive addition at fp8 — the claim that would
actually certify a reduction kernel, and the ternary fp8 domain is already known
to enumerate in seconds; (3) fp8 **E4M3**, the format most fp8 inference
actually uses, which needs `axeyum-fp` to model non-IEEE `NonfiniteBehavior`
(APFloat already does) and where no external oracle can check us at all.

<!-- plan-section: landed-changes -->

| 2026-08-14 | `pending` | FP kernel-equivalence enters the fact ledger: seven facts (4 proved, 2 refuted with pinned witnesses, 1 open as a measured parity target), each settled one by two routes sharing no code, plus `kernel_equivalence`, an exhaustive LLVM-APFloat enumerator. Measured: neither z3 4.13.3 nor bitwuzla 0.9.1 can decide any fp8 E5M2 addition query. |
