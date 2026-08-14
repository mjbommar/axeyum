# agent-a — roadmap feedback for axeyum

Written while doing the off-diagonal Schur work, not afterwards. Each item names
the file and line it came from.

## 1. `ColouringFamily` could not say "these colours are interchangeable" — and the encoder assumed they always were

**Severity: this would have shipped a wrong `unsat`.**

`crates/axeyum-search/src/colouring.rs:213` (`encode_symmetry_breaking`, before
my change) pinned point 1 to colour 1 and ordered every colour class by least
element, with the justification "sound because colour names are
interchangeable". Every family in the crate was uniform, so the assumption held
and there was no way to express its failure. The first colour-dependent family
falsifies it: in `S(3;4,5,6)` colour 1 forbids `x1+x2+x3=x4` and colour 3
forbids `x1+..+x5=x6`, and permuting them is not a symmetry of anything.

Had I built the family on the trait as it stood, the encoder would have silently
answered `unsat` for satisfiable instances and I would have "refuted" an
eleven-year-old conjecture with an encoder bug. The measured form of this is now
`crates/axeyum-search/tests/offdiag_schur.rs::whole_palette_symmetry_breaking_produces_a_wrong_unsat`:
`S(3;3,4,5)` at `n = 41` is satisfiable, and the unblocked encoding calls it
`unsat`.

**Roadmap item:** a *satisfiability-preserving* transformation (symmetry
breaking, and anything else in the same class) needs its precondition attached to
the interface, not to a doc comment. `ColouringFamily::symmetry_blocks` is the
minimal version of that. The general principle — every soundness-preserving-only
rewrite carries a machine-checkable side condition — belongs in the rewrite
manifest contracts too (`crates/axeyum-rewrite`).

**Second-order lesson worth writing down:** I first picked four other instances
for the negative control and *all four passed*, because the over-strong
constraint happened not to bite there. A control that cannot be shown to fire is
indistinguishable from no control. This is the same shape as the repo's own
"green gate over nothing" failures, one level up: not a gate that runs zero
tests, but a test that exercises zero of the behaviour it names.

## 2. The violation predicate existed in three places and only two of them were meant to

`crates/axeyum-search/src/search.rs:136` had a local `monochromatic` closure
re-deriving "every member of the set shares a colour". The crate's design is
explicit that `first_violation` must be an independent second derivation
(`family.rs:1-20`), and that separation is genuinely load-bearing. But the SLS
closure was a *third* copy that nobody had reasoned about, and generalizing the
family broke the invariant that all three agree: the closure had no notion of a
per-colour scope and would have reported a colour-1 monochromatic set as a
violation of a colour-2 constraint.

**Roadmap item:** when a codebase deliberately duplicates a definition for
independence, the deliberate copies should be *labelled* as such, so the
accidental ones stand out. I put that distinction in the doc comment at
`search.rs:136`. A `#[doc(alias = "independent-derivation")]` convention, or just
a naming rule, would make it mechanical.

## 3. Two parallel colouring encoders exist and only one has a parity gate

`crates/axeyum-cnf/src/colouring.rs` and `crates/axeyum-search/src/colouring.rs`
are two implementations of the same encoder, with the same variable convention,
the same four clause groups, and the same "byte-identical to
`scripts/gen-rado-instance.py`" claim. Only the `axeyum-cnf` one is covered by
`crates/axeyum-cnf/tests/colouring_encoding_parity.rs`.

Worse, `crates/axeyum-search/src/colouring.rs:10` says
"`tests/encoding_parity.rs` compares them directly" — and
`crates/axeyum-search/tests/` **did not exist** before this session. The doc
comment names a gate that is not there. I checked the encoding parity by hand
(built pristine `HEAD` and my tree, dumped `to_dimacs` for 29 Rado/Schur
instances, `diff -r`'d 556,911 bytes) because I could not run the gate the file
says exists.

Note that `axeyum-cnf`'s version is the more capable one: it already has
`EncodingOptions` for turning at-most-one and symmetry breaking off, which is
exactly the knob the off-diagonal work needed. The `axeyum-search` copy did not.
Two divergent copies of a soundness-critical encoder is the setup for a silent
mismatch, and one of them is the "generator of record" for a claim ledger.

**Roadmap item, in priority order:** (a) make `axeyum-search`'s doc comment name
a gate that exists or delete the claim; (b) fold one encoder into the other.

## 4. `min_conflicts` is documented as the fast path and is 100x slower here

`crates/axeyum-search/src/search.rs:1-9`: "a stochastic local search finds one
orders of magnitude faster than the CDCL core on the instances this crate was
built for". Measured on off-diagonal Schur instances, same host, same encoding:

| instance | `min_conflicts`, 14 lanes | `solve_with_drat_proof` |
|---|---:|---:|
| S(3;4,4,4), n=42 | 1.2 s | 0.00 s |
| S(3;4,4,5), n=53 | 9.1 s | 0.00 s |
| S(3;4,4,6), n=64 | 12.6 s | 0.00 s |
| S(3;4,5,5), n=68 | 83.8 s | 0.00 s |

I lost about twenty minutes building the sat side around the SLS on the strength
of that sentence. The claim is presumably true for the Rado instances it was
written about; it is stated as a property of the crate.

**Roadmap item:** qualify the claim with the family it was measured on, and give
the harness a "try CDCL first, fall back to SLS" default. The CDCL core is also
the only one of the two that produces a checkable artifact on the `unsat` side,
so preferring it costs nothing.

## 5. `SearchError` has no variant for "this cannot be represented", so I had to reuse one

`OffDiagonalSchur::minimal_solution_sets` refuses `points >= 256` because its
subsumption bitmaps are `[u64; 4]`. There is no `SearchError` variant meaning "an
internal representation limit", so it returns `PointOutOfRange { point, points }`
with `points` standing for the limit rather than the problem's size. That is
misleading in exactly the way `CLAUDE.md`'s gotchas warn about ("an error message
naming a node cap when the real cause was an i128 overflow").

What matters more than the variant: the *tempting* implementation returns an
empty `Vec` for an out-of-range `n`. An empty constraint list encodes a formula
that is satisfiable for every `n` and reads exactly like a genuine `sat`. I made
it fallible for that reason and said so in the doc comment. A general
`SearchError::RepresentationLimit { what, limit }` would let the next person do
the same thing without the misleading message.

## 6. `CnfFormula` is `Vec<CnfClause>` of `Vec<CnfLit>`, which is the wrong shape at this scale

`crates/axeyum-cnf/src/lib.rs:181-206`. `S(3;6,6,6)` at `n = 173` is 13.25M
clauses; at one heap allocation and a 24-byte header per clause that is ~1.5 GB
of overhead before any literals, and 13M individual `malloc`s. Peak RSS for that
instance was 2.3 GB for a formula whose literals are ~330 MB. It fit, but the
next row up would not, and the crate already has `compact.rs` proving the team
thinks about CNF representation.

**Roadmap item:** a flat `(literals: Vec<CnfLit>, starts: Vec<u32>)` clause arena
behind `CnfFormula`, the shape CaDiCaL uses and `references/` already has to read
from. This is a Track 1 performance item with a soundness dividend: the instances
that OOM are exactly the ones where a resource kill (exit 137) is
indistinguishable from a refutation.

## 7. Small: the crate's public surface hides its most useful entry point

`axeyum_search`'s prelude re-exports `ColouringFamily, Rado, Schur, parse_family`
but the thing a caller actually needs to decide an instance —
`solve_with_drat_proof` plus `decode_model` plus `verify_witness` — has to be
assembled by hand from two crates every time, and every consumer will assemble it
slightly differently. My driver, `crates/axeyum-search/examples/rado_sat_probe.rs`
and `examples/recertify_rado.rs` all contain a variant of the same twenty lines,
and mine initially forgot to write the witness to a file at all, so the first
23 lower-bound colourings existed only as stdout in a log.

**Roadmap item:** one `decide(family, n) -> Decision` in the crate, where
`Decision::Sat` *carries the replayed witness* and `Decision::Unsat` carries the
checked proof, so that "unchecked" is not a state a caller can construct by
forgetting a step.

## 8. A partial run must report its failure WHERE A READER LOOKS FOR THE SUCCESS

**This is the most transferable thing I found, and it is a requirement on how
runs report, not an anecdote about one cell.**

`S(3;3,3,15)` was OOM-killed. The bisection confirms both bracket ends before
bisecting, so the kill landed on the *upper* probe, and the raw transcript reads:

```
### S(3;3,3,15) bracket [100,150]
# bisecting S(3;3,3,15) over [100, 150]
  n=100: sat (48308 clauses), witness replayed
### S(3;3,4,8) bracket [50,90]          <- next cell starts
```

The brief warned that exit 137 "reads exactly like a refuted claim". What
actually happened is subtler and worse: it reads like **nothing at all**. There
is no wrong verdict to disbelieve — there is an *absence*, and an absence is
indistinguishable from a deliberate decision not to run the cell. Anyone
reconstructing the row from the `THRESHOLD` lines (which is the natural thing to
do, since that is the line that carries a result) sees `(3,3,14)` then
`(3,4,8)`, with `(3,3,15)` simply not there. Nothing in that view is false.
Nothing in it is true either.

The only thing that distinguishes "the machine ran out of memory" from "the lane
moved on" is one line my wrapper emitted:

```
  rc=137 -- see above, NOT a verdict
```

and that line is in the *log*, not in the result channel. **The negative has to
appear in the same place, and in the same shape, as the positive would have.**
A run that reports results as `THRESHOLD <cell> = <value>` must report failures
as `THRESHOLD <cell> = UNRESOLVED (reason)` on the same line format — not as a
gap plus a note somewhere upstream.

This generalises past this crate:

* **Every harness in this repo that emits per-item result rows should emit a row
  for items it could not decide**, carrying the reason (`timeout`, `oom`,
  `resource-limit`, `crashed`), rather than omitting them. `CoverOutcome` and
  the cover ledger already do this well — `CellVerdict` distinguishes refuted
  from not-checked and `certify_cover` refuses a cover with a missing cell. The
  ad-hoc campaign scripts do not, and neither did my `threshold` mode.
* **Aggregation must be able to tell "absent" from "not attempted".** A ledger
  with 14 rows where 15 cells were tried is not obviously wrong; a ledger with
  15 rows one of which says `unresolved: oom` is obviously incomplete, which is
  the state we want to be obvious.
* This is the same defect class as the repo's `--features full` history and as
  my own `bundle-lane2.sh` (exit 0, zero work done): **a green-looking absence.**
  The three failures have the same shape and want the same fix — every producer
  reports a row per requested item, and every consumer checks the count.

Concretely for this crate: `harness.rs`'s `PendingReason` is exactly the right
idea and should be the pattern for any new search mode. My `threshold` mode
should return a `Result<Threshold, Unresolved>` where `Unresolved` names the
probe that died and why, and print it on the `THRESHOLD` line.

## 9. The framework has no way to size an instance without building it

The measurement that redirected the whole campaign — "the subsumption-minimal
antichain is 0.005x the multiset count on `S(3;4,4,10)`" — was made in a
throwaway Rust program in a scratch directory, because there is no way to ask a
`ColouringFamily` "how many clauses would you emit at size `n`" without
materialising `Vec<Vec<usize>>`. That is exactly the thing you cannot afford to
do when the answer is 46 million.

`OffDiagonalSchur::visit_solution_sets` is the streaming form I ended up needing
and it is not in the trait. **Roadmap item:** a
`ColouringFamily::visit_constraints(colour, points, &mut dyn FnMut(&[usize]))`
with a counting default, so sizing an instance is a first-class question.

Related and more important: after the reduction, **enumeration is the
bottleneck, not solving**. `S(3;4,4,10)` at `n = 109` spends 110 s enumerating
46.3M solution multisets to keep 239,130 clauses, which the CDCL core then
refutes in 0.03 s. Every instance in this campaign solves in under 2.2 s. The
performance work with the highest leverage on this family is not in the solver
at all; it is generating the minimal antichain directly instead of generating
everything and discarding 99.5% of it.

## 10. I reproduced the house failure mode myself, two hours after quoting it

`bundle-lane2.sh` pointed at a binary built before the subcommand it invoked
existed. Every cell panicked. The loop had no `if`, so the script printed
`BUNDLE-LANE2-COMPLETE` and **exited 0** with three cells silently missing. I
found it only because the downstream claim generator refused to build claims
from incomplete bundles and printed `SKIP … : incomplete`.

The lesson is not "be careful with paths". It is that **the thing that caught it
was a consumer that counted what it received**, and the thing that failed was a
producer that counted nothing. The replacement reports `made=3 of 3 requested`.

**Roadmap item:** the campaign scripts in this repository (`scripts/*.sh`,
`justfile` recipes) should be audited for loops that cannot report a count. This
is the same defect class as `--features full` missing from a test command — a
green result over zero work — and it recurs because shell loops swallow failures
by default. `set -o pipefail` and an explicit tally are cheap.

## 11. Novelty is part of a claim's meaning and nothing checks it

Five claims went into `artifacts/claims/offdiag-schur/` labelled NEW that were
published four months earlier in arXiv:2604.11030 Table 3. The values agree
exactly, so nothing unsound shipped — but "NEW VALUE" was in the `notes` field
of a machine-checked ledger entry, and no part of the check touches it. It was
caught by a human-directed literature extraction, not by the tooling.

That is a real gap for a ledger whose purpose is to make claims trustworthy. A
`prior_art` array exists in the schema and is *narrative*; nothing requires it to
be complete or forces a claim to state its relationship to it. **Roadmap item:**
make novelty an explicit, reviewable field
(`novelty: new | reproduction | replication`) with `prior_art` required to be
non-empty when it is not `new`, and have `check-claim-certificates.py` at
minimum enforce that consistency. It cannot check the literature, but it can
stop a claim from being silent about it.

### Update on item 11 — implemented this session

`novelty` is now a first-class field on every off-diagonal claim (`new` /
`reproduction`), and `scripts/check-claim-certificates.py::check_novelty`
enforces three things: the value is one of the known labels; a `reproduction`
has a non-empty `provenance.prior_art`; and at least one cited row's
`establishes` states the same value the claim's title states, so a reproduction
cannot be justified by an adjacent-but-different citation. Claims predating the
field are not failed for lacking it — a claim that *has* it must have it right.

It still cannot check the literature. It can stop a claim from being silent
about it, which is the half that was missing when five claims shipped labelled
NEW.

## 12. Deploying a stale binary is indistinguishable from a working one until you count

Twice this session a lane ran against a binary that predated the subcommand it
invoked. The first time (`bundle-lane2.sh`) it exited 0 with three cells
missing. The second time (`package-lane.sh` on s5) it failed all fourteen with
`rc=101`, and I saw it in *seconds* because the lane printed
`made=0 failed=14 of 14 requested`.

Same defect, same host, forty minutes apart; the only difference was whether the
producer counted. That is about as clean a controlled experiment for the value
of a tally as one could ask for, and it is why item 8 above is stated as a
requirement rather than a suggestion.

**Roadmap item:** any script that ships a binary to a remote host should verify
the binary understands the subcommand before starting the run — a one-line
`"$BIN" --help | grep -q <subcommand>` precondition is cheaper than discovering
it fourteen failures later, and cheaper still than not discovering it.

## 13. Packaging a decided cell can cost more than deciding it — and I got the reason wrong first

**The finding, and the correction, because I published the wrong cause before
checking the numbers I already had.**

`S(3;4,4,13)` was decided without trouble. Re-running it to package the evidence
drove s5 to 10.6 GB RSS with 0 GB available on a 27 GB host and had to be
killed. My first write-up of this blamed `CnfFormula::to_dimacs()`, which builds
the whole DIMACS text as a `String` so a caller writing a CNF to disk holds the
formula *and* its full text rendering live at once. That is a real defect and it
is item 13a below — but it is **not** what made the packaging run fail, and I
asserted it without opening the log line that was already sitting in my run
directory:

```
# n=141: 558350 clauses, 423 vars, built in 686.0s   peakRSS=13956132kB
# n=142: 578773 clauses, 426 vars, built in 762.8s   peakRSS=15297660kB
```

**The decide run already peaked at 15.3 GB per side.** The cost is the
enumeration and subsumption pass — `L(13)` over `[1,142]` — not serialisation.
Deciding this cell was never comfortable; it fit because each side ran in its
own process on a 27 GB box with nothing else live. The `bundle` subcommand does
both sides *in one process* and then renders the text, so it needs roughly twice
the peak plus the string. It did not fail because packaging is expensive in
itself; it failed because I put two 15 GB phases in one address space.

Three separate lessons, and the third is the one I would keep:

* **13a.** `to_dimacs()` should be `write_dimacs(&self, w: &mut impl Write)`
  streaming clause by clause, with `to_dimacs()` implemented over it. Holding a
  ~500 MB `String` beside a multi-gigabyte formula is pure waste even when it
  fits. Pairs with item 6.
* **13b.** A tool that does several heavy phases should be able to do them one
  per invocation. `bundle` is convenient and unschedulable; `decide` was
  awkward and schedulable. Convenience that removes the operator's ability to
  bound peak memory is a false economy at this scale.
* **13c.** *I had the measurement and reasoned from a plausible story instead.*
  `peakRSS` was printed by my own harness, into my own log, for the exact cell I
  was theorising about. "Prefer a measurement over a message — including the
  ones you just wrote" is in `CLAUDE.md`, I quoted it earlier today, and I still
  published a wrong cause. The mechanism that caught it was writing the number
  down in RESULT.md, where it had to sit next to the claim and visibly disagree
  with it.


## 14. A lower bound written as a value — the campaign's recurring defect, now three times

I wrote, in the concept node I authored for `math-education`:

> Only five values are known — 5, 14, 45, 161, 538

Two errors in one clause. `538` is **not a known value**: for six colours the
literature gives a *lower bound* (`>= 537` in the least-`N` convention the file
itself uses, from an exhibited colouring). And the list had dropped `S(1) = 2`,
so a bound had been substituted for a genuine value while keeping the count at
five. That also silently falsified the next clause — "the fifth was settled in
2017" is Heule's `S(5) = 161`, not the six-colour case. The coordinator caught
it against Song–Mao's Table 1 and corrected it before committing.

I verified the correction rather than accepting it, and it holds: under the
file's own convention (`S(2) = 5`, established in its body by the `{1,4}/{2,3}`
colouring), `S(1) = 2` because `1+1=2` is the smallest forced solution; the five
known are `2, 5, 14, 45, 161`; and a colouring exhibited for six colours bounds
the least-`N` threshold from *below*, which is the direction stated.

**This is the third instance of one defect shape in this campaign, and they run
in both directions:**

* the coordinator briefed `w(2;3,20) = 389` as an open problem when 389 is a
  certified lower bound printed in AKS Appendix A.1 — a bound read as a value;
* the whole reason this family needs both sides is that
  `S >= s·t·u − t·u − u − 1` is a **theorem** and the equality is a
  **conjecture**; my brief's ten "open cells" each needed exactly one refutation
  because the bound was already had;
* and now my own prose did it inside a knowledge-graph node.

**Roadmap item, and I think it is a real one:** the ledger enforces this
distinction beautifully — `supports` on an evidence row says `S > 119` or
`S <= 120`, never `S = 120`, and a claim is a value only when both rows exist.
That discipline stops at the ledger boundary. The moment a number is written in
prose — a doc comment, a README, a concept node, a briefing message — the
relation collapses to `=` and nothing checks it.

Concretely: **a numeric claim in prose should carry its citation and its
relation adjacent to it**, the way an evidence row does. `S(6) >= 537 (exhibited
colouring, Song–Mao Table 1)` costs eight words more than `538` and cannot decay
into a false value. For this repository specifically, the places where published
numbers appear as bare integers in prose — `SEMANTICS.md` files, family doc
comments listing known values, `docs/research/` notes — are exactly where this
will happen again, and they are checkable: a small linter over `= <integer>` in
prose that wants a citation nearby would have caught all three of these.

The deeper point is that **the artifact-level rigour did not transfer to the
sentence level even when the same person wrote both, minutes apart.** I built a
gate that refuses to call a cell decided without a witness *and* a proof, and
then wrote a bound as a value in the next file I touched.
