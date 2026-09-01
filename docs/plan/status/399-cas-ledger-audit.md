# Lane: cas-ledger-audit — audit every `axeyum-cas` certificate against the fact ledger

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this pass`, cas-ledger-audit, 2026-09-01).**
Audited all 55 modules of `crates/axeyum-cas/src/` against the fact ledger,
answering the deficiency
[`2026-09-01-the-cas-certifies-far-more-than-the-ledger-records.md`](../../research/11-design-review/2026-09-01-the-cas-certifies-far-more-than-the-ledger-records.md).
Full audit:
[`2026-09-01-cas-certificate-reconstruction-audit.md`](../../research/11-design-review/2026-09-01-cas-certificate-reconstruction-audit.md);
decision: [ADR-1400](../../research/09-decisions/adr-1400-a-certificate-must-record-every-distinction-its-acceptance-depends-on.md).

**Both of the deficiency's headline numbers are wrong, in opposite directions,
and the errors nearly cancelled.** `40 of 53` is an unmasked grep counting
doc-comment prose (masked: **27 of 55**; a second declaration-shaped query: 23).
`19` counts the `^F-cas-` **filename** convention against a real
`proof_route: cas-certificate` count of **48**, so nine telescoping facts existed
for a subsystem the deficiency reported as having none. Joined per module, the
gap is **13 certificate-carrying modules with no naming fact**, not 34.

**Verdicts:** 9 RECONSTRUCT TODAY (every one *partial* — the kernel re-checks a
strictly weaker claim than the certificate makes; residues named per row),
8 COULD RECONSTRUCT with the specific missing piece named, the rest
`cas-internal` with a reason.

**The output that mattered: eleven certificates that cannot express a distinction
their producer makes.** Ranked in the audit. Sharpest four — `gosper.rs:153` has
three acceptance modes recorded nowhere, and mode C returns when the full
zero-test did **not** certify (and does not separate `Unknown` from a positively
decided disagreement); `gf2_shard.rs:245` accepts `ShardStatus::Exhausted`, a
real negative theorem, by incrementing a counter, with `--require-all-found`
opt-in; telescoping computes a pole count, **uses** it to skip pointwise checks,
and does not serialize it, so a certificate whose pointwise layer ran zero times
is byte-identical to one confirmed at all 75 grid points; `normalforms.rs:399`
verifies the factorization and never the normal form, so `(I, A)` passes as a
Hermite form and the invariant-factor chain is checked nowhere outside a unit
test.

**Two in-tree models where the distinction IS carried, and they are different
fixes:** `check_cas_ideal_certificate` *rebuilds* `lower`/`real_strict` rather
than storing them (a field can be forged, a re-derivation cannot), and the SOS
format expresses strictness as a numeric margin with a committed zero-margin
control. ADR-1400 makes re-derivation the preferred route and recording-plus-a-
control the fallback.

**One good-news finding, recorded because the opposite was expected:** there is
no floating point anywhere in the SOS subtree — exact rational LDL^T, overflow is
a *decline* rather than a `NotPsd` verdict, and a decimal literal is a hard parse
error with a committed control fixture. The rounded-versus-exact ambiguity is
structurally impossible there, not merely absent.

**Six facts landed**, `cas-certificate` route 48 → 54,
`scripts/validate-facts.py` green at 2529 facts / 0 errors. Three SOS
(`F:cas-sos-motzkin-psd-not-sos`, `F:cas-sos-damped-rotation-lyapunov`,
`F:cas-sos-energy-barrier-unreachability`) — `scripts/check-sos-negative-controls.sh`
opens by asserting "every fact in the sos family cites this script" and
**measured 2026-09-01, zero facts did**; the gate was built for facts nobody
wrote. Plus `F:cas-gf2-degree-400-trinomial-irreducible` (dual checkers with
disjoint arithmetic), `F:cas-ratint-horowitz-x-over-x-minus-one-squared` (two
surgical single-guard fixtures), `F:cas-smith-normal-form-two-six-twelve`.

**Every checker was verified to fail, in both directions.** The shape is
`cargo test … -- --exact 2>/dev/null | grep -cE '^test <path> \.\.\. ok$'` —
`grep -c` consumes the pipe so it cannot SIGPIPE, and the count is tested.
Measured: five real tests `count=1 exit=0`; a deliberately absent test
`count=0 exit=1`. That last line is the point — a bare `cargo test` with a filter
matching nothing prints `0 filtered out` and exits 0. For the SOS facts,
`sos_certify --expect-checks N` on the **unchanged** honest artifact with a wrong
`N` exits 1, and `--expect-rate 1/25` against the true `1/26` exits 1 (the rate
pin is the stronger one: it fails a certificate that discharges every obligation
but proves a weaker bound).

**Next, and this is a hypothesis about one route rather than a property of the
target.** Seven certificate-carrying modules still have no naming fact
(`boolean_circuit`, `geometry_json`, `gf2_artifact`, `gf2_search`, `gf2_shard`,
`gf2_tensor`, `gosper`, `lib`, `telescoping_json`, `groebner_cert`). Two are one
fact away — `boolean_circuit` and `gf2_tensor` both replay exhaustively and both
name a counterexample. `boolean_circuit` looks like the cheapest new kernel
bridge in the crate (`rat_prelude` has `decidable.rs` and `boolean.rs`; the
missing piece is a bridge test importing the CAS type) — that is a sizing from
reading the two crates, **not** from trying it. And several `COULD RECONSTRUCT`
modules need a certificate *repair* before a bridge is worth building, since
reconstructing a certificate that already lost a distinction reconstructs the
loss.

**Did not run:** `scripts/check-fact-evidence-replay.sh` (it executes every
settled fact's `checker_command` verbatim — the full battery), and no workspace
`cargo test` (nothing in this lane touched Rust source). Each of the six new
checker commands was verified individually, which is the part the aggregate
cannot substitute for.

<!-- plan-section: landed-changes -->

| 2026-09-01 | cas-ledger-audit | audited all 55 `axeyum-cas` modules against the fact ledger; corrected both of the deficiency's headline numbers (certificate surface 41→**27 of 55** masked; CAS facts 19 filename-matches→**48** by route; real gap **13 modules**, not 34); 9 reconstruct-today / 8 could-reconstruct / rest `cas-internal` with reasons; found **eleven certificates that cannot express a distinction their producer makes**, sharpest being `gosper.rs`'s three unrecorded acceptance modes and `gf2_shard`'s exhaustion theorem accepted by incrementing a counter; landed 6 facts (route 48→54) each with a checker verified to fail in both directions; ADR-1400 |
