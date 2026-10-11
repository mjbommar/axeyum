# Signed CAS powers — implementation evidence

This isolated lane starts at 97359c332. The parent CAS gates (59537) remain pinned
to e7b58fc86; the Boolean proof gates (84285) retain 446aae38b. Signed-power work
does not alter their sources. ADR-3000 defines partial domains and signed limits.
Validation is in progress; no completed gate or kernel admission is claimed.

Commit 511642747 introduces the signed Rust/Python path and mandatory controls.
Rust integration handle 36691 completed exit 0: four tests passed, zero failures
(0.22 seconds after compilation). It checks reciprocal AST shape, existing positive
shape, exact nonzero rational values with witness replay/tamper, zero and missing
bindings, undefined-base exponent zero, and signed magnitude extremes. Zero
reciprocal equality production correctly declines rather than certifying it.
Fresh Python build/stub generation/focused lint runner 73272 is still live at
the isolated target `target/cas-negative-powers`; no terminal results credited.

Extended Rust boundary validation found the old narrow evaluator's linear
exponent loop unsuitable for neutral bases at u32::MAX. Replaced it with checked
squaring while preserving base evaluation at exponent zero. Initial extended
run: three pass/one fail, because checked_mul(1,i128::MIN) declines despite the
identity result. The power-one path now returns the evaluated base directly.
Revalidation and a private-snapshot domain-guard mutation remain pending.

Handle 37315 revalidated the squaring/power-one repair: four Rust tests pass,
zero failures (0.01 seconds). Accepted neutral-base magnitude extremes now
evaluate promptly; i128::MIN at exponent one is preserved.

The initial signed Python build (first phase of 73272, before the narrow-evaluator
revision) exited 0. Isolated package `/var/tmp/axeyum-signed-power-python-jupwq9tu`
loaded native SHA-256
`94df2023be057ccbca67d6fbc7ece5f5d0885fb44728394263f71dae94bc03dd`.
222 Python tests passed (222 collected), including signed powers, prior wide
transport and the original CAS suite. This validates the Python signed syntax
and bounded evaluator, not the subsequent narrow Rust evaluator revision.
The new amortization example exited 0, independently matched Fraction, reported
2859/2849-bit components and zero-rate result 2500/3.
Stubs regenerated with 645 items/27 modules; focused lint remains live in 73272.

Parent wide-CAS full library run is terminal red: 2139 pass, one failure, eleven
ignored, 1314.04 seconds. Sole failure is untouched matgroup test
psl2_f7_isomorphic_to_gl3_f2 at 6.095 seconds against its five-second debug budget.
No threshold was changed. Its workspace phase remains live (59537); this is not
a completed aggregate gate. Parent or quiet rerun investigation remains required.

Revised-core validation recovered and rechecked: isolated extension at
`/var/tmp/axeyum-signed-power-revised-python-ts0v0k0h`, SHA-256
`6872f5415d1edb745d5b4eb6187dc6c123353bb6ea8688adcce18e8518495dee`,
passes 223 Python tests (223 collected; repeated 0.50 seconds). The new seeded
Fraction differential test includes guaranteed zero-negative and undefined-base
cases. Build/stub/lint runner 76704 completed successfully: 645 stub items in
27 modules and focused clippy with warnings denied. Docstrings now quote Python
exception names and generate without trailing whitespace; diff check passes.

Private snapshot domain-guard mutation logs are retained at
`/var/tmp/axeyum-signed-domain-mutation-3kappfdc`: baseline four pass, mutant
three pass/one fail. Replacing required base evaluation with a zero fallback
kills exactly `zero_and_missing_bases_do_not_acquire_reciprocal_values`.
No mutation was made in the shared checkout. These focused results do not close
workspace gates, conditional trace certification, kernel admission or integration.
