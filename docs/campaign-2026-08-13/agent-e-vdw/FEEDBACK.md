# agent-e feedback — roadmap items from the van der Waerden lane

Ordered by what cost this lane the most. Every item is cited by file and line
and backed by a measurement taken in this session.

## 1. There is no streaming DRAT checker, and that is the wall on this family

`axeyum_cnf::solve_with_drat_proof_streaming`
(`crates/axeyum-cnf/src/proof_sat.rs:222`) streams a proof to a `DratSink`, so
production has a fixed memory footprint. Checking has none:
`check_drat_backward(&formula, &steps)` takes a **slice of parsed steps**, so
`parse_drat` must materialise the entire proof first.

Measured on `w(2;3,13)` at `n = 160` — 7,628 clauses, 320 variables:

| stage | result |
|---|---|
| solve | unsat, ~22 min, **6,015,016,742 bytes** of text DRAT written |
| parse + check | **OOM-killed** on a 26 GiB host |

The verdict was produced and is unusable. The row below it, `w(2;3,12)` at
`n = 135`, is 623 MB and checks in 110 s, so the wall is between 0.6 and 6 GB
and it is memory, not time.

Two asks, in order of value:

* **a backward checker that consumes a `Read` stream**, or at least a
  two-pass form that indexes the proof file and holds only the core. The
  backward checker already only verifies the core (ADR-0382); it just cannot get
  there without holding everything first.
* **a proof-size budget in the producing API.** `solve_with_drat_proof_streaming`
  takes a deadline and a conflict cap. It should also take a byte cap, because
  a run that will produce a proof nobody can check should stop and say so
  rather than spend twenty minutes writing one.

Related: an OOM kill exits 137 and prints nothing, which from outside is
indistinguishable from a clean run that produced no output. My driver's
`PROOF_PARSE_LIMIT` guard turns that into a printed
`verdict=unsat-UNCHECKED reason=proof-exceeds-parse-limit`. That policy belongs
in the library, not in each lane's driver.

## 2. Engine selection is folklore, and the folklore inverted between two lanes

This is the item I most want the framework to own, because two lanes on the same
day measured opposite things and both were right.

* **agent-a, off-diagonal Schur:** `min_conflicts` took 83.8 s on `S(3;4,5,5)`
  at `n = 68` where the CDCL core took 0.00 s. Its diary concluded the crate's
  documentation ("local search finds colourings orders of magnitude faster than
  the CDCL core") is backwards.
* **agent-e, van der Waerden:** on `W(4,3)` at `n = 75` — a *satisfiable*
  instance, 6,224 clauses, 300 variables — the CDCL core exhausted its default
  conflict budget in 44 s, 14 lanes of `min_conflicts` found nothing in 35
  minutes, and randomised backtracking burned 4,000,013,081 nodes in 265 s
  without a witness. Meanwhile the *refutation* side of instances five times
  that size returns in seconds.

The regimes are distinguishable in advance, and the distinguishing features are
already computable from the family:

| feature | CDCL wins | search-hard |
|---|---|---|
| verdict expected | unsat | sat |
| colours | 2–3 | 4+ |
| constraint arity | small sets, many of them, strong unit propagation | 3-element sets over a large domain |
| solution density | irrelevant | extremal colourings are rare and structured |

The concrete shape of the finding: **for a colouring family, the unsat side is a
propagation problem and the sat side is a search problem, and the gap widens
with the number of colours.** `w(2;3,t)` is 2-colour and CDCL finds both sides;
`W(4,3)` is 4-colour and CDCL finds neither side of `n = 75` in its default
budget while refuting `n = 76`-sized instances routinely.

What a `known_witness` / engine-selection hook would need:

1. **A `Decision` type the library owns**, with a `Sat` variant that *carries*
   the replayed witness (agent-a asked for this too). Today each driver
   re-invents it, and the interesting distinction — `UnsatChecked` versus
   `UnsatUnchecked` — exists only in my driver.
2. **A witness inlet.** `ColouringFamily::known_witness(n) -> Option<Witness>`,
   defaulted to `None`, so a family can supply a construction (Rabung's
   power-residue colourings are periodic modulo a prime and give `W(4,3) > 75`
   directly) or a caller can supply a colouring from the literature. It must be
   **untrusted**: the value of the hook is that the witness goes through
   `verify_witness` and the encoder view exactly like a CDCL model. My driver
   grew this as an optional argument to `value`; it should be a trait method.
3. **A declared regime.** `ColouringFamily::sat_side_engine() -> Engine`, with
   `Engine::{Cdcl, LocalSearch, Cover, KnownWitness}`, defaulted to `Cdcl`. The
   default is right for 2-colour instances and wrong for 4-colour ones, and the
   family is the only place that knows which it is.
4. **A restriction inlet for the sat side only.** Periodic and palindromic
   restrictions are sound for lower bounds (any colouring found is a genuine
   colouring) and unsound for upper bounds. Ahmed–Kullmann–Snevily's `w(2;3,t)`
   lower bounds are all palindromic. The type system should make it impossible
   to feed a restricted problem into the unsat side; today nothing stops it.

## 3. `CoverOptions` has every budget except the one that kills it

`harness.rs:77-106` offers `workers`, `cell_conflicts`, `cell_time`,
`total_time`, `check_step_cap`, `compose_step_cap`, `retain_proofs`. The cover
route died on **memory**, twice:

* `w(2;3,13)`, `n = 160`, depth 8, 14 workers: **247 of 256 cells refuted**,
  every one with its proof re-derived and recorded `passed` — 85,262,947 proof
  steps, 1,982.8 s of solving, 3,422.9 s of checking — then killed at **7.4 GB**
  of cell proofs on disk with one cell's proof at 282 MB. Nine cells short.
* `W(4,3)`, both `n = 75` and `n = 76`, depth 5, 14 workers: killed before any
  cell record.

Asks:

* `CoverOptions::cell_proof_bytes` and a whole-run byte budget, with the same
  "produced but not checked, reported as such" policy `check_step_cap` already
  has for steps.
* **Adaptive re-splitting on budget exhaustion.** The nine surviving cells of
  the `n = 160` run were indices 127, 191, 223, 239, 247, 251, 253, 254, 255 —
  the cells where the branch points take the long-progression colour, i.e. a
  structurally identifiable hard corner. `cube-tree-cover` already exists as an
  evidence kind for adaptive covers; the harness should split a cell that
  exhausts its budget rather than reporting the run incomplete.
* Workers default to 1 while `retain_proofs` defaults to `false`; with 14
  workers and proofs on disk, the pressure moved to the filesystem and the
  checker's transient allocation. A `workers`-aware memory estimate at run start
  would have refused the configuration instead of dying 96% of the way through.

## 4. The claim gate was red, and one error was hiding the other 228

Fixed in this lane, but the failure mode is worth recording.

`novelty` is written into claims by two lanes and enforced by
`scripts/check-claim-certificates.py::check_novelty` — the field that exists
because five values shipped labelled NEW after being published four months
earlier. It was **absent from `artifacts/ontology/claim.schema.json` and from
`validate-claims.py`'s `CLAIM_OPTIONAL`** (`scripts/validate-claims.py:78`), so
every claim carrying it failed with `unknown field 'novelty'` — and
`validate_claim` returns immediately after the field check
(`scripts/validate-claims.py:427`), so that single error masked everything
behind it. 62 claims, 62 errors, one message each.

Admitting the field exposed the real state: **229 errors**, 228 of them in
`offdiag-schur` claims (generator paths that name a method in parentheses, three
`graph_pin`-less resolved refs per claim, a malformed `produces_sha256`). Those
are not mine and are left for their owner, but they were invisible and are not
now.

Second bug in the same file: `classify_payload`
(`scripts/validate-claims.py:186`) sniffed `colouring-text` from `text.split()`
rather than from the comment-stripped `body`, so the `c ...` provenance header
that **every witness producer in this tree writes** made the artifact sniff as
`unknown` and fail its own format contract. 61 witness rows.

Third, milder: a row declaring `check_status: "not-checked"` was skipped by
`check-claim-certificates.py` **in silence**, so a claim with an unchecked row
printed exactly like one whose every row had been re-derived. It now reports
into the same `NOT re-checked here` summary that the regenerable rows use.

Ask: `just claims` is deliberately outside `just check` (justfile:274) because
it needs `drat-trim` and takes minutes. The **first two** commands in that
recipe need neither — `validate-claims.py` and
`check-claim-negative-fixtures.py` are seconds of pure Python — and the recipe's
own comment says so. They should be in the default gate. A structural claim
gate that nothing runs is how 62 claims came to be failing at once.

## 5. `ColouringFamily::constraints` should not be the primary method

`family.rs:47` requires an off-diagonal family to return the sets forbidden in
**every** colour, as a relaxation. For van der Waerden that intersection is
**empty** (a length-`k1` progression has `k1` points; for `k1 != k2` no set is
forbidden in both colours), and a `ColouringProblem` built from an empty
constraint list encodes a formula satisfiable for every `n` — a vacuous `sat`
indistinguishable from a real one. `offdiag.rs:569` carries the same hazard with
the same warning comment.

Two families in, both of which had to document their way around it: make
`constraints_for_colour` the primary method and derive the colour-agnostic view,
or return `Option<Vec<Vec<usize>>>` so "there is no useful uniform view" is a
value rather than a dangerous default. Until then, every consumer needs the
`assert!(!problem.forbidden().is_empty())` that my driver carries.

## 6. Smaller items

* **`min_conflicts` has no progress reporting.** 35 minutes on 14 threads
  produced one line at the end. A restart counter and a best-violation-count
  would have told me in 30 seconds that it was not converging; I added the
  restart counter to my driver.
* **`family.branch_points(depth)` defaults to `2, 4, 6, …`** (`family.rs:98`),
  chosen for the Rado runs. For a progression family the informative branch
  points are not evenly spaced small integers — the cells that survived the
  `n = 160` cover are exactly the ones that colour those points alike. A family
  that knows its own structure should be able to say so, and `branch_points` is
  already the hook; nothing but Rado uses it.
* **The `published_value` reference table is in the family** (`vdw.rs`) and is
  documented as "a reference, never evidence". That pattern (agent-a's
  `conjectured_value` too) now exists twice and should probably be a trait
  method with a doc contract, so that a lane cannot accidentally consult it in a
  decision path.
* **Non-interactive `ssh` does not put `~/.cargo/bin` on `PATH`.** Not an axeyum
  bug, but it produced this session's instance of the house failure mode: a
  build that never ran, a `| tail -2` that swallowed the error, and a lane that
  printed `LANE-DIAGONAL-COMPLETE made=0 of 4 requested`. The count is the only
  reason it was caught in seconds. Campaign rule 3 ("measure, do not trust a
  message") should be extended with: *a remote build is a measurement too —
  verify the binary's mtime or hash, not the exit status of the pipeline that
  built it.*
