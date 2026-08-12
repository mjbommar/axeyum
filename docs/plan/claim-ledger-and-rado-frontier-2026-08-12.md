# Claim ledger and the R_4(2(x−y)=3z) frontier campaign — 2026-08-12

Session result note. Design rationale:
[ADR-0379](../research/09-decisions/adr-0379-claim-ledger.md). Artifacts:
[`artifacts/claims/`](../../artifacts/claims/README.md).

## What landed

1. **Claim ledger** — a first-class artifact class joining the knowledge
   graph (math-education concepts + this repo's curriculum) to
   machine-checked evidence. Schema
   `artifacts/ontology/claim.schema.json`; gates
   `scripts/validate-claims.py`, `scripts/check-claim-certificates.py`
   (independent semantic replay, fails closed on unknown families),
   `scripts/check-claim-negative-fixtures.py` (three committed invalid
   fixtures, exact diagnostics); dashboard generator
   `scripts/gen-claims-dashboard.py`; `just claims` recipe (deliberately
   outside `just check`).
2. **34 replication claims** for every exact value of
   `R_3(a(x−y)=bz)` (1 ≤ a,b ≤ 5) and `R_4(a(x−y)=bz)` published in
   Chang–De Loera–Wesley (ISSAC 2022, arXiv:2210.03262, Tables 1 and 10).
   Every claim carries (i) a witness colouring at `R−1` replayed by an
   independent third-implementation enumerator and (ii) a
   drat-trim-verified DRAT certificate for `F_R` whose CNF must
   regenerate byte-identically from the claim parameters
   (`scripts/gen-rado-instance.py`). Zero mismatches against the
   published tables. Proofs stored gzipped (~64 MiB total).
3. **One frontier claim** — `rado-r4-a2-b3-frontier`: the only non-exact
   entry in the paper's 4-colour table (`R_4(2(x−y)=3z) > 225`),
   verified still open against the 2026 Ahmed–Zaman–Bright follow-up.
   Carries the published bound as an explicitly non-checked
   `bound-citation`, a locally machine-verified `R_4 > 222` witness, a
   structural analysis (colour classes without evens are solution-free;
   the equation is self-similar under doubling), a recorded negative
   result (the local-search witness family probably cannot extend: its
   1..100 prefix is UNSAT at n = 226), and a concrete settling
   condition.
4. **The reverse edge** — the ledger's pending `C:rado-number` ref drove
   authoring `graph/concepts/rado-number.md` in the sibling
   math-education repo (its validator passes: 0 errors, 1 deliberate
   pending ref). The ledger refs stay `pending` until that repo commits,
   exactly per the tri-state resolution policy.

## Campaign result: R_4(2(x−y)=3z) = 226 — the open entry is settled

- **Upper bound:** kissat 4.0.4 proved `F_226` UNSAT (~50 min), emitting a
  2,394,664,316-byte DRAT certificate
  (sha256 `d0b26e78…`); drat-trim verification with trimmed-proof and
  LRAT extraction is the final gate before the claim's certificate row
  reads `checked`.
- **Lower bound:** a 4-colouring of `[225]` with no monochromatic
  solution, verified by four independent implementations. Found in
  under 10 ms by the session-built PAWS SLS (kissat needed ~100 min for
  an equivalent model).
- Both artifacts live in the settled claim
  `artifacts/claims/rado/rado-r4-a2-b3/`; the interim frontier claim was
  removed before first commit (this note is its history).
- **Independent corroboration:** (i) the SLS explored 78,943 distinct
  colour-permutation-canonical near-miss states at 226, and 623/623
  depth-6 radius-complete DFS refutations completed untruncated;
  (ii) every structural template family (all-odd top classes, cleaned
  intervals, all-even classes, periodic, geometric) was SAT at
  n ≤ 210 and UNSAT at 226.
- **Structure found en route** (verified computationally, recorded in the
  claim): a colour class is solution-free iff for each even `e` in it,
  `3e/2` is not a difference within it; cleaned intervals
  (interval minus small evens) are the extremal-witness building block;
  the `a = 1` family fits closed forms
  (`R_k(x−y=2z) = (2·4^k+1)/3` matches all known values) while
  `(a,b) = (2,3)` admits no constant-coefficient recurrence
  (`R_1..R_4 = 4, 13, 61, 226`), so 226 sits in a formula-free band
  together with the `a = b±1` cases 56 and 103.

## Product findings from the axeyum-only recomputation

The doctrine correction (external solvers demoted to the ADR-0002 oracle
role; axeyum's own stack must produce the product evidence) turned the
recomputation into a genuine stress test. Findings, each reproducible:

1. **`Evidence::check` returns `Ok(true)` for `Evidence::Unsat(None)` and
   `Evidence::Unknown(_)`** (`crates/axeyum-solver/src/evidence.rs:890`).
   A bare, uncertified UNSAT "passes the check" with zero checking — the
   exact green-gate failure class CLAUDE.md catalogues. Front-door
   consumers must inspect the variant before trusting the bool.
2. **`produce_qf_bv_evidence` ignores the caller's deadline for proof
   production**: it calls `export_qf_bv_unsat_proof` (uncapped) although
   `export_qf_bv_unsat_proof_within` exists. The configured timeout
   bounds only the decision phase; a hard UNSAT re-derives the entire
   search with no budget.
3. **`produce_evidence_smtlib` drops the arena**, so a consumer cannot
   run `Evidence::check` on the result without re-parsing and relying on
   parse determinism for `SymbolId` alignment.
4. **The native proof core retains its entire DRAT proof in memory
   during search**: on `F_226` the single-run driver was OOM-killed at
   27.6 GiB RSS after ~2.5 h (server5, kernel log retained). Reference
   solvers stream proofs to disk. Until the core can stream, search-scale
   single-run proofs need either a large-memory host or the cube
   decomposition (whose workers free each per-cube proof after checking
   and hold ~1 GiB flat).
5. **`check_drat` does not scale to search-sized proofs**: a 1,674-step
   proof checks in 2.3 s, but a 1.2M-step proof (F_103's native
   refutation, solved in 20.9 s) runs for tens of minutes. The trusted
   checker is small and correct but forward-checking; search-scale
   certificates need backward/core-first checking or decomposition.
   Consequence: cube-and-conquer is not merely parallelism here — many
   small per-cube proofs keep every certificate inside the checker's
   practical range, which is the honest path to axeyum-checked results
   at this instance scale.

The full product front door otherwise held: SMT-LIB parse → Bool route →
BatSat decision → native proof-CDCL certificate → in-tree
`check_drat`/`check_lrat`, validated on known boundary pairs with tamper
tests (truncated/edited certificates are rejected; intact ones pass).
Measured highlights: the product front door decided `F_225` **SAT in
352 s** (the kissat oracle needed ~100 min for the same side) with the
model replayed against all 35,548 original assertions; the native proof
core matched the oracle on `F_171` (49.8 s vs ~60 s).

## Certified cube-and-conquer on the native core (new harness)

A session-built harness (agent lane, external crate over `axeyum-cnf`
only) decomposes an instance by branching on the colours of chosen
integers and refutes each cube with the native proof core, then produces
**one composed DRAT proof of the original formula** that axeyum's own
`check_drat` accepts. Composition rule: every `Add(C)` in a cube's proof
is re-emitted as `Add(C ∨ D_c)` where `D_c` is the cube's negation
clause (sound because the native core emits only RUP steps, and RUP is
monotone), deletions are dropped, and the branch tree is collapsed
deepest-first through the formula's own at-least-one clauses. Validated:
composed proofs accepted at branch depths 1–4 on `F_56` and on `F_103`
(64/64 cubes, 64/64 per-cube checks); a forged cube proof is rejected at
the exact step; a SAT sibling instance yields a verified model, never a
fabricated UNSAT; composed output is byte-identical across three
machines. Where the composed proof exceeds the checker's practical
range, the fallback discipline is per-cube `check_drat` on the augmented
formulas plus a machine-verified exhaustive-cover bitmap, with only the
composition lemma as meta-argument. This is the checking-scale answer:
per-cube certificates stay inside the small checker's range by
construction.

## The decisive measurement: search 153 s, certification the whole problem

`F_226` was covered **completely** — 4096/4096 cells refuted over the full
product `[1..4]^6`, exhaustiveness and zero duplicates re-derived
independently — in **152.9 seconds** on 14 workers, with inline checking
disabled and all 4096 per-cell DRAT proofs written to disk (5.8 GiB).

At the same moment, two covers of the *same instance* with inline checking
had been running **5.5 hours** and stood at 42% and 47%. The difference is
about **460×** in time-to-cover, and the covers with checking never finished
at all.

This is the paper's thesis measured on the paper's own blocker. Search and
certification are not one job; treating them as one is what made full
verification look like a 300-core-hour wall. Separated, the search is
minutes and the certification becomes a *separately schedulable* job that
can wait for a checker fast enough to afford it — which is exactly what the
backward-checking work is for. The retained proofs make that check possible
without re-running any search.

## Measured: checking dominates solving by two to three orders of magnitude

Per-cube data from the depth-7 `F_226` decomposition, the cleanest
measurement of the asymmetry this work is built around:

| cube | refuted in | proof steps | `check_drat` |
|---|---:|---:|---:|
| 4499 | 0.3 s | 38,015 | 200.6 s (**670×**) |
| 4447 | 2.2 s | 145,836 | 1031.6 s (**470×**) |

Forward checking costs roughly 5 ms per step at this formula size. Two
consequences: proof *checking*, not search, sets the reachable frontier;
and cube proof sizes are highly variable at fixed depth, so deeper
decomposition does not uniformly shrink them — depth 6 beat depth 7 in
total wall clock despite four times fewer cells.

## Capability increment landed: streaming DRAT proofs (ADR-0380, proposed)

Finding 4 was closed the same day: `axeyum-cnf` now has a `DratSink`
trait threaded through the proof-producing core (monomorphized;
existing APIs unchanged via `VecProofSink`), a `TextProofSink` proven
byte-identical to `write_drat`, a `solve_with_drat_proof_streaming`
entry with identical search trajectory, and a bounded-memory
`check_drat_streaming` + `DratTextReader`. 18 new tests (crate suite
325, was 307); clippy/rustfmt/rustdoc clean; workspace check clean.
Uncommitted, pending review. A streaming-mode `F_226` run now
accompanies the in-memory run on the large-RAM host: same trajectory,
no memory ceiling, proof on disk for offline streaming check.

## The construction, and the point where it stops

Mining the SAT-found extremal colourings revealed they are **a-adic
valuation strata**, not magnitude intervals (the interval hypothesis was
refuted on all 78 witnesses tested). Generalising the k=3
valuation-plus-shells colouring of Chang–De Loera–Wesley to a nested
two-ended shell construction gives, for `b = a-1`,

```
R_k( a(x-y) = (a-1)z )  >  a^k + a^(k-1) - 2a + 1 - 1
```

whose excess over `a^k` is `a^(k-1) - 2a + 1` — equal to `(a-1)^2` exactly
when k = 3, which is why the published k=3 law looked like `a^3 + (a-1)^2`.
At k = 4, a = 4 the excess is **57**, matching our `R_4 = 313`.

Verified by building the colouring and checking it with an independent
enumerator, **11 of 11 attempted**: it reproduces the published k=3 values
31, 73, 141, 241, 379 and the published `R_4(3,2) = 103`, and independently
reproduces our `R_4(4,3) = 313`. New verified bounds follow without search:
`R_4(5,4) > 740` (search gave 684), `R_4(6,5) > 1500` (search gave 1300),
`R_5(4,3) > 1272`.

**Where it stops.** The construction predicted `R_5(3,2) = 319`. A SAT
search found a 5-colouring of [319] in 14.8 s — verified by axeyum's model
self-check and an independent enumerator over all 22,472 solution triples —
so `R_5(3,2) > 319` and the bound is **not tight at k = 5**, though it is
attained at every k = 3 and k = 4 point tested. Every tightness claim is
therefore scoped to k ≤ 4. Li (SSRN 6814341) reports the analogous k=5
failure in a different column, independently.

The general-k proof is asserted in the construction source and has **not**
been independently verified here; the bound is reported as verified at
every tested point, with the general proof deferred.

**Range condition, found by testing and confirmed as a bug.** The
construction is valid only for `b < a`. Two independent sweeps agree: for
`b < a` it is solution-free at every parameter triple tried (67 and 11
respectively, zero failures); for `b > a` it fails at **every** triple —
19 of 19 in our own sweep, with the explicit counterexample
`(a,b,k) = (3,4,3)`, `N = 60`, triple `(49,1,36)` (since
`3·48 = 144 = 4·36`, and all three receive colour 2). The helper
`predicted_lower_bound` returned values in that regime regardless, which
would have been **unsound** if quoted; it now refuses and falls back to the
`a^k` branch, which is valid for every `b`. No published or recorded bound
of ours ever used it — the `b > a` rows keep their search-derived
witnesses — but the guard is in place and the counterexample is recorded
with it.

Among `b < a`, the construction beats `a^k` **exactly when `b = a-1`**:
it improves on the published bound precisely in the regime where the
three-colour theory already separates.

## One problem, six layers — and what each was worth

The same question was attacked through six of axeyum's layers. Four
independent encodings (propositional, integer-variable LIA, `Int`-valued
UF, uninterpreted-sort EUF) **never disagreed on a single value**, and
every undecided case stayed `unknown`.

1. **Propositional + proof CDCL + in-tree DRAT/LRAT** — 18 values, each
   with a re-checked refutation and a source-replayed witness.
2. **Integer arithmetic certifies the propositional encoder.** For 18
   (equation, box) pairs the LIA layer proves the emitted clause set is
   *exactly* the solution set of `a(x-y)=bz` over `[1,n]^3` — completeness
   as a single UNSAT query, `|T|` up to 435, including a non-coprime case.
   Ten negative controls pass: delete one triple and the solver returns
   exactly that triple. **This closes the gap the paper names** — a
   certificate proves some CNF is unsatisfiable, not that the CNF says what
   the paper says; now a different theory layer checks that too. The
   solution-form lemma is separately machine-proved, bounded and unbounded
   over ℤ.
3. **Uninterpreted colour sort (EUF)** — colours in an uninterpreted sort
   are structurally interchangeable: 8/8 agreement, 1.7×–27× faster than
   `Int`-valued UF, decides an instance the `Int` encoding cannot, and
   costs only ~1.5–2× with hand-written symmetry breaking **removed
   entirely**. The measured answer to the symmetry question.
4. **`#[axeyum::verify]` on the trusted checker** — 8/8: four bounded
   claims about the witness replayer verified for all inputs, four
   deliberately broken controls refuted with witnesses that replay in real
   Rust. The trusted base is itself machine-checked.
5. **CAS** — 30 certified identities past Gosper, including the
   integrality theorem `(m-1) | m^k(m-2)+1`; and a SAT → CAS → SAT round
   trip where interpolation predicted `R_2(1,5)=41` and `R_3(1,5)=286`,
   both confirmed. For `a ≥ 2` the polynomial ansatz fails (90 vs 91,
   54 vs 57, 374 vs 428) — a real negative about the family.
6. **Unsat cores** — `R_2(4(x-y)=3z)=16` is forced by only 6 of its 34
   solution triples.

**Honest failures.** Quantified UFLIA does not work: nested `∀` returns
`Unsupported("quantifier over non-enumerable domain Int")` because the
guarded expansion fires once on top-level assertion quantifiers and never
to a fixed point. A 32×32 multiplier-equivalence miter got no verdict in
940 s.

### Two product defects found, worth their own work

- **Ground `IntDiv`/`IntMod` are not constant-folded before dispatch.** On
  semantically identical quantifier-free queries this costs up to **49×**
  measured and converts two solved instances into timeouts (>168× lower
  bound), isolated by a probe that varies only the spelling of an integer.
  It is the direct cause of the quantified layer's failure; a folding pass
  would likely unblock it.
- **`expand_guarded_int_universals` does not iterate to a fixed point**, so
  `∀x. G(x) ⇒ ∀y. H(x,y) ⇒ …` is refused even though every layer is
  individually in the supported guarded shape.

## Follow-ups

- Flip the `upper-drat` evidence row to `checked` when drat-trim
  reports VERIFIED; store the trimmed proof (gzipped) beside the claim.
- Wire `just claims` into CI once the ledger design survives review
  (ADR-0379 is `proposed`).
- Flip `C:rado-number` refs to resolved after math-education commits.
- Candidate next claims: the agent-conjectured closed forms
  (`R_2(1,b) = u²+u−1`, `R_3(1,b) = u³+2u²−2`, u = b+1) as
  `conjectured` ledger entries with their finite verification ranges.
