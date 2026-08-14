# agent-e diary — van der Waerden numbers

Append-only. Newest entry at the bottom.

## 2026-08-13, entry 1 — orientation, and what I inherited

Target: van der Waerden numbers. `w(r; k_1, …, k_r)` is the least `N` such that
every `r`-colouring of `[1,N]` has a monochromatic arithmetic progression of
length `k_c` in some colour `c`. Diagonal (`W(r,k)`, every colour the same `k`)
and off-diagonal (`w(2;3,t)`: colour 1 avoids 3-APs, colour 2 avoids `t`-APs).

Read agent-a's `RESULT.md`, `DIARY.md`, `FRAGMENTATION.md` and the code it
landed at `c0403d000` before writing a line. Three things carry over exactly:

1. `ColouringFamily::{constraints_for_colour, colour_dependent, symmetry_blocks}`
   plus `ColouringProblem::per_colour` — the whole per-colour machinery. I did
   not touch it.
2. **`symmetry_blocks` is soundness-critical.** For `w(2;3,t)` with `t != 3` the
   two colours forbid different progression lengths and are *not*
   interchangeable, so the stock whole-palette break would produce a wrong
   `unsat`. For the *diagonal* `W(r,k)` the colours genuinely are
   interchangeable and the full break is sound and valuable.
3. The subsumption-minimal antichain, which is why agent-a passed the published
   frontier. My prediction before measuring: **it does nothing here** — every
   length-`k` progression is a set of exactly `k` points, so no two nest.

## 2026-08-13, entry 2 — the design decision that is not incidental

`VanDerWaerden::colour_dependent()` returns `!is_diagonal()`. That one line is
the whole distinction the brief asked to be explicit:

* diagonal → the *uniform* path, `ColouringProblem::new`, whole-palette
  symmetry breaking, which is the byte-identical stock encoder and is sound
  because the colours really are interchangeable;
* off-diagonal → `per_colour` with blocks grouped by progression length, which
  for `w(2;3,t)`, `t != 3`, is `{1}` and `{2}`: no colour symmetry at all.

The degenerate case `w(2;3,3)` is the diagonal `W(2,3)`, and the family reports
it as such — `label()` prints `W(2,3)`, `colour_dependent()` is false. A family
that answered "off-diagonal" there would be leaving a sound and free symmetry
break on the table for no reason.

## 2026-08-13, entry 3 — subsumption measured, and the answer is zero

The reduction that gave agent-a a factor of 1,402 gives **exactly nothing**
here, and it is worth writing down why rather than just reporting the ratio.

`clause(S)` subsumes `clause(S')` when `S ⊆ S'`. For generalized Schur, solution
sets have wildly different sizes — `{a, (k−1)a}` has two elements and swallows
whole families of larger ones. Every length-`k` arithmetic progression, by
contrast, is a set of **exactly `k` distinct points**, so `S ⊆ S'` forces
`S = S'`; and a progression is determined by its set (least two elements give
`a` and `d`), so there are no duplicates either. The forbidden list of one
colour is *already* the subsumption-minimal antichain.

This is in the code as a measurement, not a claim: `VanDerWaerden::subsumed_pair`
searches for a containing pair and `progressions_are_already_an_antichain` runs
it over `k = 3..6` and `n ∈ {10, 25, 40}` — 12 configurations, all clean, plus a
duplicate check. Ratio 1.000, measured.

The consequence is the interesting half. agent-a's wall was *enumeration*: 164 s
to generate 633M multisets and keep 451k clauses. Here the clause count is
`Σ_d (n − (k−1)d) = O(n²/k)` and every instance builds in under 10 ms. **This
family is solver-bound.** Same framework, opposite bottleneck — which is a
better test of the framework than a second instance of the same shape would
have been.

## 2026-08-13, entry 4 — the first eleven values, in under thirty seconds

`crates/axeyum-search/src/vdw.rs` (~560 lines with docs and 12 unit tests) plus
a spec in `parse_family`. Driver `vdw_frontier.rs` adapted from agent-a's
`offdiag_frontier.rs`, kept outside the repository per the ownership map.

Both sides of every cell: `n = N−1` sat with the colouring replayed by
`first_violation`, `n = N` unsat with the DRAT proof re-derived by
`check_drat_backward`. First run, in order:

| cell | N | clauses @N | proof steps | wall |
|---|---:|---:|---:|---:|
| w(2;3,3) = W(2,3) | 9 | 59 | 5 | 0.0 s |
| w(2;3,4) | 18 | 153 | 29 | 0.0 s |
| w(2;3,5) | 22 | 204 | 100 | 0.0 s |
| w(2;3,6) | 32 | 391 | 302 | 0.0 s |
| w(2;3,7) | 46 | 752 | 937 | 0.0 s |
| w(2;3,8) | 58 | 1,140 | 4,158 | 0.1 s |
| w(2;3,9) | 77 | 1,931 | 19,592 | 0.3 s |
| w(2;3,10) | 97 | 2,973 | 164,912 | 2.7 s |
| w(2;3,11) | 114 | 4,014 | 1,017,863 | 22.5 s |

Every one agrees with the published value. Proof length is growing by ~6× per
step of `t` while the formula grows linearly — 4,014 clauses producing a
1.0M-step, 84 MB refutation. **Proof size, not clause count, is the wall in this
family**, and it will be the thing that stops the row.

## 2026-08-13, entry 5 — I reproduced the house failure mode within an hour

`ssh s5 '... cargo build ... | tail -2'` printed nothing alarming and my wrapper
reported `rc=0`. The build had not happened: non-interactive `ssh` does not put
`~/.cargo/bin` on `PATH`, `| tail -2` swallowed `cargo: command not found`, and
`rc=$?` was the exit status of `echo`. The lane then ran to completion against a
binary that did not exist and printed

```
timeout: failed to execute process: No such file or directory
LANE-DIAGONAL-COMPLETE made=0 of 4 requested
```

Two hours after reading agent-a's entry 9 about exactly this, with the fix it
recommends — **count what you made** — already in my script. The count is the
only reason I caught it in seconds instead of believing an empty log. Lane
scripts now also `test -x "$B" || exit 1` before the loop, and every remote
command exports `PATH=$HOME/.cargo/bin:$PATH`.

## 2026-08-13, entry 6 — the literature audit lands, and the brief's target 2 is not open

I ran a full-text audit of Ahmed–Kullmann–Snevily (arXiv:1102.5433) plus OEIS
and GitHub before claiming anything, per the campaign's lesson about five
"NEW" values that had been published four months earlier. Findings that change
the plan:

* **`w(2;3,20) = 389` is very probably not open.** Wikipedia's raw wikitext
  attributes it to Kouril, *Leveraging FPGA clusters for SAT computations*
  (ParaFPGA15, Advances in Parallel Computing 27, 2015), marked "verified"; that
  paper's abstract says it reports "four new off-diagonal van der Waerden
  numbers", and exactly four Wikipedia rows cite it. The body is paywalled and I
  have not read it, so the identification is inference from the citation pattern
  — but it is strong enough that claiming 389 as open would be wrong.
* **389 is already a certified lower bound.** AKS Appendix A.1 prints an
  explicit palindromic good partition of `[1,388]`. So the sat side at `n = 388`
  is a *reproduction*, not a discovery.
* The genuinely open row starts at **`t >= 21`** (AKS Table 2 gives conjectured
  exact lower bounds 416, 464, 516, …, none closed).
* **The real gap is certification, not values.** No classical van der Waerden
  number has ever carried a machine-checked UNSAT proof in the peer-reviewed
  record: Kouril–Paul, Kouril and AKS produced none, and AKS say so explicitly
  ("It would be highly desirable to be able to substantially compress the
  resolution proofs … so that a proof object would be obtained which could be
  verified by certified software"). Marijn Heule's `vdWaerden` repository holds
  44 certificates and every one of them is a *lower-bound colouring*. The only
  machine-checked vdW refutations anywhere are from 2026 and are Lean-based:
  PBLean (arXiv:2602.08692) covers `W(2,3)` and the upper half of `W(2,4)` via
  VeriPB, and an unreviewed repository claims `W(2,5) = 178` via cube-and-conquer
  with LRAT into Lean. Nothing pure-Rust exists.

So target 2 is re-scoped to an honest probe with a census, and the value of
target 1 goes **up**: the row `w(2;3,t)` for `t >= 4` has, as far as this audit
reached, never carried a machine-checked refutation in any system.

## 2026-08-13, entry 7 — W(2,5) = 178 in 43 seconds, and W(4,3)'s lower side is the hard half

The diagonal lane on s5: `W(3,3) = 27` and `W(2,4) = 35` instantly, then

```
W(2,5) = 178: n=177 sat (replayed), n=178 unsat,
              8,278 clauses, 2,153,837 proof steps, 139 MB,
              solve 20.0 s, check 22.2 s, 43.2 s end to end
```

That is the value the one unreviewed prior certification needed 3,627 cubes of
cube-and-conquer, per-cube LRAT and a Lean reflection pass to reach. Ours is one
process, one 20-second solve, and our own backward checker.

`W(4,3) = 76` did *not* fall, and the interesting part is which side failed: the
**lower** one. Finding a 4-colouring of `[1,75]` with no monochromatic 3-AP
exhausted the CDCL core's default conflict budget in 44 s, while the refutation
at `n = 76` is a different matter entirely. This is the mirror image of
agent-a's finding that CDCL beat the SLS everywhere: on a 4-colour instance with
1,369 short constraints the satisfiable side is a search problem and local
search is the right tool. Driver now takes a pre-computed colouring for the
lower side — untrusted, replayed by `first_violation` *and* by the encoder view
before it counts — so the two sides can use different engines.

## 2026-08-13, entry 8 — the row runs out of memory, not out of time

`w(2;3,12) = 135` landed on s6: 6,347,847 proof steps, a 623 MB DRAT, 82 s to
solve and 110 s to re-derive. Then `w(2;3,13)` at `n = 160` wrote a **6.0 GB**
proof in about 22 minutes and the process died with no `RESULT` line at all.

That is the OOM-reads-like-a-refutation hazard the brief warned about, and the
only reason it was legible is the lane's `made=N of M` count and the missing
`RESULT`. `check_drat_backward` takes a slice, so `parse_drat` has to
materialise the whole proof first; 6 GB of text does not fit alongside its
parsed form on a 26 GiB host. The formula is 7,628 clauses. **The wall in this
family is the proof, not the instance** — six times longer per step of `t` while
the formula grows linearly.

Lower sides for `t = 14` and `t = 15` came back `ResourceOut` from the CDCL
core's default conflict budget, so those rows have neither side.

## 2026-08-13, entry 9 — the cover route gets 247 of 256 cells and then dies too

The framework's own answer to a too-large proof is the cube cover, so I used it:
`harness::run_cover` on `n = 160`, depth 8, 14 workers. It refuted **247 of 256
cells**, re-deriving every single one of those proofs with the backward checker
— 85,262,947 steps, 1,982.8 s of solving and 3,422.9 s of checking — and was
then killed at 7.4 GB of retained cell proofs, one cell alone at 282 MB.

Nine cells short of a certified `w(2;3,13) = 160`. The survivors are indices
127, 191, 223, 239, 247, 251, 253, 254, 255 — the cells where the branch points
take the long-progression colour, i.e. a structurally identifiable hard corner
that an adaptive splitter should have split further. `CoverOptions` has budgets
for workers, conflicts, cell time, total time, proof steps and composition
steps, and none for memory.

Same story on `W(4,3)`: both the `n = 75` and `n = 76` cover runs were killed
before a single cell record.

## 2026-08-13, entry 10 — W(4,3)'s hard side is the satisfiable one

Worth stating plainly because it inverts agent-a's finding. Finding a
4-colouring of `[1,75]` with no monochromatic 3-term progression defeated, in
order: the CDCL core's default conflict budget (44 s), fourteen lanes of
`min_conflicts` (35 minutes), randomised-restart chronological backtracking
(4,000,013,081 nodes in 265 s), a periodicity-restricted variant of the same at
six different periods, and the cover route (OOM).

agent-a measured CDCL beating local search by three orders of magnitude and
wrote it down as a correction to the crate's documentation. Both measurements
are right: the unsat side of a colouring family is a propagation problem and the
sat side is a search problem, and the gap widens with the number of colours.
`w(2;3,t)` is 2-colour and CDCL finds both sides; `W(4,3)` is 4-colour and it
finds neither side of `n = 75`. That belongs in the framework as an
engine-selection hook, not in two diaries — FEEDBACK item 2.

## 2026-08-13, entry 11 — the claim gate was red and one message was hiding it

Packaging thirteen claims meant running `validate-claims.py`, which reported 62
errors, all of them `unknown field 'novelty'`. `novelty` is the field that
exists *because* five values shipped labelled NEW after being published four
months earlier — it is written into claims by two lanes and enforced by
`check-claim-certificates.py`, and it was in neither the schema nor the
validator's field list. `validate_claim` returns right after the field check, so
that one error per claim masked everything behind it.

Admitting the field exposed 369, then 229 after two more repairs. 228 of those
are pre-existing `offdiag-schur` errors that were invisible an hour ago. One was
mine and is fixed.

The second repair is the one I like: `classify_payload` sniffed `colouring-text`
from the whole file rather than from the comment-stripped body, so the `c ...`
provenance header **every witness producer in this tree writes** made the
artifact sniff as `unknown` and fail its own format contract — 61 witnesses,
including all of agent-a's. Two lanes had been writing witnesses that could not
pass the format gate, and the gate was never green enough for anyone to notice.

Third, milder: a row declaring `check_status: "not-checked"` was skipped in
silence, so a claim with an unchecked row printed exactly like a fully re-derived
one. It now reports into the `NOT re-checked here` summary.

## 2026-08-13, entry 12 — wind-down, and what is honestly unfinished

The coordinator redirected the campaign from new values to axeyum itself. I
killed the `w(2;3,20)` probes and the `w(2;3,14)` cover, took a bounded census
of the open cell, and packaged what has both sides.

**Thirteen values certified from both sides**, all reproductions, all with a
claim-ledger entry that validates and re-checks clean: `W(2,3) = 9`,
`W(3,3) = 27`, `W(2,4) = 35`, `W(2,5) = 178`, and `w(2;3,t)` for `t = 4..12`.

Unfinished, by side:

* `w(2;3,13) = 160`: lower side sat and replayed; upper side **not certified**
  (6.0 GB monolithic proof, checker OOM; cover 247/256 cells).
* `w(2;3,14)`, `w(2;3,15)`: **neither** side. The lower side hit the CDCL
  default conflict budget; the upper side was never attempted.
* `W(4,3) = 76`: **neither** side. The lower side defeated four different
  engines; the upper side was never reached.
* `W(3,4) = 293`, `W(2,6) = 1132`: not attempted.
* `w(2;3,20)`: no side established. Census: 64 cells at depth 6, 14 refuted, 9
  open at 90 s per cell, 41 never reached inside a 900 s cap — identical counts
  at `n = 388` and `n = 389`. And the cell is very probably not open at all
  (Kouril 2015); the brief's premise did not survive the literature check.

The last honest note is that the two most useful things this lane produced are
not numbers. One is the answer to the question it was set: agent-a's per-colour
extension carried to a second family in a different area of mathematics with 78
lines of additive change to existing library code, and my driver reached it
through `dyn ColouringFamily` rather than a concrete type. The other is that
three separate gates in this repository were reporting success over work they
were not doing, and all three are now fixed.

## 2026-08-13, entry 13 — housekeeping notes for whoever reads the log

* Two commits: `8dd2c0344` (the family, its tests and the spec) and `4c24ce204`
  (thirteen claim-ledger entries plus the two claim-gate repairs). The first
  predates campaign rule 10 and therefore carries **no `Agent: agent-e`
  trailer**; the second does. I did not rewrite history to add it — rule 4 —
  so this line is the attribution.
* Both were pathspec-only and verified with `git show --stat`. Nothing outside
  `crates/axeyum-search/{src/vdw.rs,src/family.rs,src/lib.rs,tests/vdw.rs}`,
  `artifacts/claims/vdw/`, `artifacts/ontology/claim.schema.json`,
  `scripts/check-claim-certificates.py` and `scripts/validate-claims.py` was
  touched. `cover.rs`, `harness.rs`, `certify.rs` and everything under
  `crates/axeyum-lean-kernel/` were used but never edited.
* The uniform encoding is byte-identical to pristine `HEAD`: 9,647,640 bytes of
  DIMACS across six Rado instances, `diff -r` clean.
* Final gate on the snapshot: 77 lib + 7 offdiag + 5 vdw + 1 doc test, all
  passing, clippy clean at `-D warnings`, rustfmt clean. 13 vdw claims validate
  with 0 errors and re-check with 0 errors.
* Hosts s5 and s6 are idle and their scratch trees are left in place
  (`~/scratch/agent-e/`), including the 7.4 GB of `w(2;3,13)` cell proofs and
  its 247-row cover ledger, in case anyone wants to finish those nine cells with
  a memory-bounded run.
