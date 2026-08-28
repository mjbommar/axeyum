# ADR-0613: `unsat` is certified by FOLLOWING hints, not by searching for them

Status: accepted
Date: 2026-08-28
Index-summary: The evidence path called the forward reference DRAT checker at every site, so certifying a refutation cost ~3 orders of magnitude more than deciding it (`F:fp16-add-monotone-rne`: decide 11.09 s, check ~2.4 h extrapolated, never observed to finish). The route now elaborates the proof's core to LRAT with the backward engine as an UNTRUSTED producer and has `check_lrat` — small, search-free, linear — verify the hints. The trusted base does not move: `check_drat_backward` appears only in rejecting position, and the forward reference remains the accepting authority whenever the LRAT route declines. Measured: fp8 evidence 25m46s to 5.0 s, and fp16 from never-observed-to-finish to 125 s end to end with `certified=1 recheck=ok`.
Index-status: accepted

## Context

[ADR-0011](adr-0011-drat-unsat-proof-checking.md) built `check_drat`, the
forward reference checker that discharges `unsat`. It walks a DRAT proof
front to back and verifies that every added clause is RUP or RAT against the
clause set accumulated so far. It is a few dozen lines, and a person can read
it, which is the whole basis of the trust story.

[ADR-0382](adr-0382-backward-drat-checking.md) measured that it does not
scale in time — 470-670x slower than *solving* on the motivating instance —
and added `check_drat_backward`, the standard DRAT-trim technique, at 66x.
That ADR was written to be **additive**: "`check_drat` must not change,
because it is the reference; the new checker must be additive". Its item 9
explicitly deferred re-basing the LRAT elaborator on the new engine as "an
obvious follow-on ... deliberately not in this slice".

**The follow-on was never taken, and the evidence path never moved.** Measured
2026-08-28 on `main`: the backward engine is used throughout the campaign
tooling, `cube.rs`, `weighted.rs` and half a dozen examples, and **nowhere in
`axeyum-solver`'s certificate route**. Every accepting call there is the
forward checker, and `git log -L` dates those call sites to **2026-06-13**,
two months before the fast engine existed. There is no ADR, comment or test
pinning the choice. It is precedence, not a decision.

The cost is not theoretical. `F:fp16-add-monotone-rne` — IEEE binary16
add-monotonicity, the one genuinely open decidable fact in the ledger —
measured against its own pinned negation file:

| stage | cost |
| --- | --- |
| decide only | **`unsat` in 11.09 s** |
| search + emit proof | 424,601 conflicts, 24-27 s, **827,048 steps**, ~193 MB |
| `check_drat` | **~95 steps/sec** -> extrapolated **~2.4 h**, never observed to finish |
| `elaborate_drat_to_lrat` | never reached |

The workspace's identity sentence is *"untrusted fast search, trusted small
checking."* On this fact it was inverted by roughly three orders of magnitude,
and the fact could not be settled — not because the solver cannot decide it,
but because we could not check the answer.

The naive fix — swap `check_drat` for `check_drat_backward` at the accepting
call sites — is the one thing ADR-0382 declined to do, and for a good reason:
it moves the trusted base from a few dozen readable lines to ~2,700 lines of
watched literals, clause arenas, lifetime intervals and trail reuse. Speed
bought with assurance is not a trade this repository makes.

## Decision

**The fast engine becomes a producer, not a checker.** Certification runs the
composition the identity sentence already describes, applied to proof checking
itself:

1. **`certify_unsat_via_lrat(formula, drat)`** (new, `axeyum-cnf/src/lrat.rs`)
   runs `elaborate_drat_to_lrat_backward` — the backward core-first engine —
   to emit the proof's *core* as LRAT with explicit antecedent hints. That
   engine is **not trusted**. Its only job is to guess hints.
2. `check_lrat` then verifies those hints against `formula` directly. It seeds
   its active set from `formula`'s own clauses, follows each addition's chain
   with **no search of any kind**, and reports `Ok(true)` only if the empty
   clause is derived. It is smaller than `check_drat` and strictly simpler,
   because it does not have to search for a refutation — it is handed one.

A bug anywhere in step 1 produces hints step 2 rejects, so the outcome is a
decline rather than a wrong `unsat`. **`Certified` is discharged by
`check_lrat` alone.** The trusted base does not grow; it shrinks, from a
checker that searches to a checker that follows.

Four consequences of that framing, each load-bearing:

1. **A decline is a statement about the ROUTE, not about the proof.**
   `LratCertifyOutcome::Declined` claims nothing about `formula` and nothing
   about `drat`. A perfectly good proof using a RAT lemma declines here,
   because `LratStep` cannot express a pivot and negative hint blocks
   (ADR-0382). The producer therefore falls through to the **unchanged**
   forward reference route, which does have an opinion. Falling through is
   not "ask until one says yes": only one route has spoken.

2. **`check_drat_backward` may appear only in REJECTING position.**
   `UnsatProof::recheck` accepts iff `check_lrat` accepts **and**
   `check_drat_backward` accepts the published DRAT text. The second conjunct
   can turn an accept into a reject and never the reverse, so however wrong
   the backward engine might be it cannot make `recheck` accept anything
   `check_lrat` did not. The conjunct is not decoration: it is what catches a
   certificate whose LRAT is intact and whose published DRAT — the artifact an
   external `drat-trim` reads — has been tampered with. That disagreement
   between our answer and an outside checker's is the one this project cannot
   afford.

3. **The backward stage is whole-or-nothing, so the budget gates it.**
   Backward checking walks the proof in reverse and cannot stop half way and
   report partial progress the way the forward checkers can. So
   `budget_admits_backward_certify` refuses it on an already-expired
   `deadline` and on a `max_steps` smaller than the proof; both cases reach
   the bounded forward route and report `Inconclusive`. This is what keeps
   *a timeout is not a pass* literally true. A live deadline admits the stage,
   which can then overshoot it by at most that stage's cost — a strict
   improvement on the route it replaces, which is equally uninterruptible and
   measured at ~66x the work. An overshoot that certifies is a real
   verification, never a timeout promoted to a pass.

4. **The consumer path is one implementation, not two.**
   `Evidence::recheck_certificate` re-parsed the same text and ran the forward
   checker independently of `UnsatProof::recheck`. It now delegates. That
   duplication is *how* the consumer path silently kept the superlinear
   checker; there is no reason for a certificate to have two re-validators.

`check_drat` is untouched, remains the reference, and remains the accepting
authority for any certificate with no LRAT.

### Observability

`CheckingProgress` gains a `BackwardLratCertify` variant. The backward stage
is not step-interruptible, so it reports exactly twice — opening and closing —
carrying `steps_total`, elapsed, `finished` and `certified`. Two samples is not
a progress bar. It is the whole difference between "which stage is running" and
silence, which is the question the 2026-08 fp16 incident could not answer: a
24 s search followed by hours of unattributed checking.

## Evidence

### Soundness

The technique that finds a missing guard is not mutation, which can only
delete guards that exist. It is an adversarial fixture over a **satisfiable**
query where every other guard passes — on an unsatisfiable formula every
accepted proof is sound vacuously, so a composition that had quietly stopped
checking would look perfect there.

`never_certifies_a_satisfiable_formula` generates random satisfiable CNFs
(counter asserted `>= 20`, so the sweep cannot degenerate to zero cases) and
attacks each with four proof shapes:

- a **borrowed** refutation, valid for a different formula;
- a proof **truncated** before its empty clause;
- a **bare unjustified empty clause** — the shape that kills a missing
  `check_lrat` gate, because `elaborate_drat_to_lrat_backward` answers
  `Ok(vec![])` when there is no refutation and an empty LRAT proof is
  `Ok(false)` to the trusted checker, *not* an error. A composition returning
  `Certified` on elaboration success alone would certify a satisfiable formula
  from an empty proof;
- **random garbage** terminated by an empty clause.

None may certify. Mutation-verified: deleting the `check_lrat` gate makes this
test report `Certified` for a satisfiable formula.

Beside it: `certifies_exactly_what_the_reference_checker_verifies` (differential
against `check_drat` over solver-produced proofs, counter asserted),
`a_missing_refutation_declines_with_the_no_empty_clause_reason` and
`a_refutation_stripped_of_its_empty_clause_is_never_certified` (the decline
*reason* stays precise, so a caller cannot confuse "this format cannot express
your proof" with "your proof is broken"), and on the solver side
`an_intact_lrat_does_not_rescue_a_gutted_drat` and
`a_valid_drat_does_not_rescue_a_forged_lrat`.

The gutted-DRAT test asserts `recheck_lrat() == Some(true)` *before* asserting
`recheck()` rejects — without that line the test would pass even if the LRAT
half were what rejected, and it would not be exercising the conjunct at all.

### Mutation results

| guard deleted | tests that died |
| --- | --- |
| the `check_lrat` gate in `certify_unsat_via_lrat` | `never_certifies_a_satisfiable_formula`, `a_missing_refutation_declines_with_the_no_empty_clause_reason`, `a_refutation_stripped_of_its_empty_clause_is_never_certified` |
| the `check_drat_backward` conjunct in `recheck` | `an_intact_lrat_does_not_rescue_a_gutted_drat`, `unsat_proof_rechecks_and_detects_tampering` |
| the whole budget gate | `an_expired_check_deadline_yields_inconclusive_never_proved`, `a_zero_check_step_budget_yields_inconclusive_never_proved`, `the_reference_route_still_reports_both_of_its_sub_stages` |
| the deadline half of the budget gate only | `an_expired_check_deadline_yields_inconclusive_never_proved` — exactly one |

Stated precisely rather than rounded to the "exactly one" the standing rule
asks for: the first two mutants kill more than one test because the guard
carries more than one claim (soundness *and* the precision of the decline
reason; the conjunct *and* the older tamper test). The deadline half is the
one guard carrying exactly one claim, and exactly one test dies for it.

### Speed

Measured on `neg-fp8-add-monotone-rne.smt2`, the binary8 sibling of the fact
that motivated this work, `smtcomp_cli --evidence --progress`, release, on a
contended host (load ~9.4):

```
; progress conflicts=36770 ... proof_steps=67214 proof_bytes=8898263 elapsed_ms=1344
; checking stage=backward_lrat_certify steps=0     total=67214 finished=false certified=false elapsed_ms=0
; checking stage=backward_lrat_certify steps=67214 total=67214 finished=true  certified=true  elapsed_ms=2555
; evidence kind=unsat-drat certified=1 recheck=ok arena=ok ms=5028
unsat
```

**5.028 s end to end, of which 2.555 s is checking.** The fact ledger records
the same query at **25m46s with evidence** before this change: roughly 300x on
the certificate stage. `recheck=ok` on the same line is the consumer-side
re-validation, which also now runs through the new route.

And the binary16 query this ADR was written for — the one the ledger recorded
as never observed to finish — on the same host and the same pinned file:

```
; progress conflicts=424601 ... proof_steps=827048 proof_bytes=193214020 elapsed_ms=27748
; checking stage=backward_lrat_certify steps=0      total=827048 finished=false certified=false elapsed_ms=0
; checking stage=backward_lrat_certify steps=827048 total=827048 finished=true  certified=true  elapsed_ms=82302 steps_per_sec=10048.8
; evidence kind=unsat-drat certified=1 recheck=ok arena=ok ms=125098
unsat
```

**125.098 s end to end, of which 82.302 s is checking.** Against the measured
`check_drat` rate on this exact proof — ~95 steps/sec, extrapolating to ~8,700 s
for the DRAT check *alone* before elaboration even started — the checking stage
is ~106x faster and the certificate now exists.

One run on a contended host is a data point, not a benchmark; but the claim it
supports is qualitative and does not need a benchmark. The stage went from
"never observed to terminate" to "terminates in under ninety seconds", and
`certified=1 recheck=ok` says the trusted checker accepted it.

Note the shape of the numbers, which is the general lesson: the search is
*unchanged* (27.7 s, the same 424,601 conflicts and 827,048 steps as every
previous run), and the whole difference is in the stage that reads the proof
back. The inversion this ADR fixes was never about the solver.

## Alternatives

- **Swap `check_drat` for `check_drat_backward` at the accepting sites.** The
  obvious fix, and the one ADR-0382 refused. It buys the same speed by moving
  the trusted base to ~2,700 lines with no small reference in accepting
  position. Rejected: this ADR gets the speed without the trade, because the
  hint-following checker is *smaller* than the one it replaces.
- **Keep the forward checker and label the fast route's output as
  second-class evidence** the validator prints separately (the ADR-0601 §3
  shape). Rejected as unnecessary here: a `check_lrat`-verified refutation is
  not weaker evidence than a `check_drat`-verified one. It is the same claim
  established by a checker that does less. Grading it would misinform.
- **Run the fast route by default and the reference as a differential oracle
  on every instance small enough for both.** Attractive, and largely what the
  test suite already does (`certifies_exactly_what_the_reference_checker_verifies`
  is exactly this sweep). Rejected as a *runtime* policy: on the instances
  where it would run, checking is not the bottleneck, and on the instances
  where it is, the reference cannot run at all. It belongs in the test suite,
  where it is.
- **Cube-and-conquer decomposition** (ADR-0543) so many small proofs replace
  one large one. Complementary and still wanted: it addresses proofs too large
  to hold, which is the memory axis ADR-0426 measures. It is not a substitute
  for checking one proof cheaply.

## Consequences

- A refutation that could be produced but not checked can now be certified.
  fp8 moves from 25m46s to 5.0 s; **fp16 moves from never-observed-to-finish to
  125 s**, which closes the measured obstruction on
  `F:fp16-add-monotone-rne`. That fact is nonetheless still recorded `open`,
  because `epistemic_status` is a claim about what this ledger can *show* and
  showing it needs an evidence row with a `checker_command` that fails when the
  claim is false. The obstruction being gone and the evidence existing are
  different claims; only the first is established.
- **The published DRAT is now normally verified by the backward engine rather
  than the forward one.** These agree on every proof the reference accepts;
  the backward one additionally tolerates unjustified dead weight *outside*
  the refutation's core, which is `drat-trim`'s own contract since 2014. So a
  certificate from either route is externally checkable, and
  `UnsatProof::recheck`'s DRAT conjunct enforces exactly that. Anyone using a
  checker as a **proof linter** — "is every line of this proof justified?" —
  still needs `check_drat`, as ADR-0382 already says.
- The `LratStep` RAT gap is now on the hot path rather than a footnote. Our own
  CDCL core emits RUP-only proofs, so the fallback is rare in practice, but a
  future RAT-emitting technique (blocked-clause addition, symmetry breaking)
  would silently drop every such proof back onto the superlinear route. The
  next thing to build, if that happens, is an LRAT step that carries a pivot
  and negative hint blocks — not another checker.
- `CheckingProgress` gained a variant, so any exhaustive match on it needs an
  arm. `smtcomp_cli` is updated; there was exactly one other consumer.
- **Four accepting `check_drat` call sites remain, deliberately unconverted in
  this slice**, and they are named here so the next lane does not have to
  re-derive the audit: `sat_bv_backend.rs:1961` (native CDCL inline proof
  check), `:1489` (the pure-Gauss XOR certificate), `:2049`
  (`verify_unsat_proof`, the `prove_unsat` re-derivation gate), and
  `bitblast_miter.rs:152` (the faithfulness miter). All four are
  *verdict-only* — three discard the proof entirely and the fourth publishes
  `dimacs`/`drat` with no LRAT field — so each converts to the same shape as
  the exporter: try `certify_unsat_via_lrat`, and on a decline fall back to
  `check_drat`, whose `Ok`/`Err` contract each already depends on. The only
  behavioural difference to think about is the documented ADR-0382 divergence:
  a proof carrying unjustified dead weight *outside* the core is `Ok(false)` to
  the reference and `Certified` here. That is sound, and at three of these sites
  it cannot arise at all because the proof was produced by our own core in the
  same call. They were left alone to keep this diff small enough to hold in
  one head, not because there is a reason not to convert them.
