# agent-j — misconception corpus as a negative-control suite

Append-only. Newest at the bottom.

---

## 2026-08-14 — setup

Read the frontier README (rules 7-10), CLAUDE.md, and
`coordinator/NEXT-MATH-STACK.md` item 5.

Snapshot per rule 7: `git archive HEAD | tar -x -C ~/.cache/axeyum-agent-j`,
HEAD = `eb94e8f9a7cdac160c08174855309a18ac5c2adc`. On disk, not `/tmp`.
`cargo build -p axeyum-scenarios -p axeyum-solver --all-features` → exit 0 in
36 s. So HEAD compiles; whatever agent-i is doing in the live tree is not my
problem and I never have to build there.

Corpus located: `/home/mjbommar/projects/personal/math-education`, branch
`main`, HEAD `ce3e2a5` ("graph: add C:schur-number" — the commit the
coordinator mentioned). `graph/misconceptions/` has exactly 148 `.md` files.

## 2026-08-14 — schema, and the first measured thing

Read `graph/AUTHORING.md`. The load-bearing field for me is not the prose body
but `distractor_forms[].text` — each misconception carries one to three
*concrete wrong statements*, which is exactly the negative-control payload. The
prose explains why a learner believes it; the `text` is the claim.

First measurement before counting anything (per the standing warning about
counts that were 10x low): `grep -h '^status:' *.md | sort | uniq -c` gives
**147 draft, 1 deprecated**. `accurate-test-means-positive-result-is-reliable`
carries `status: deprecated` and `replaced_by: M:base-rate-neglect-error`.
So the honest denominator for the census is **147**, not 148. The coordinator's
note says 148 and that is the file count, which is right, but it is not the
count of live misconceptions.

Dumped every file's frontmatter to `logs/corpus-frontmatter.txt` (168 KB) and
read all of it rather than sampling. That was the right call: several
classifications turn entirely on the exact wording of a distractor, and two
findings below would have been invisible from titles alone.

## 2026-08-14 — J1 census

Wrote `census.tsv` — one row per file, four columns, and computed the counts
from it with a script instead of asserting them.

Classes I settled on, and why the A split matters:

- **A1** — the distractor text *is itself* a false proposition in a fragment
  axeyum decides. No modelling choice. 49.
- **A2** — false after exactly one standard, uncontroversial formalisation
  (probability = counts / |Omega|; "best fit" = least squares; "rectangle" =
  four right angles). 37.
- **B** — a genuine proposition, out of every fragment we decide. 17.
- **C-*** — not a checkable proposition at all, sub-tagged by why. 44.
- **DEP** — the deprecated file. 1.

Splitting A1/A2 was not cosmetic. Reporting "86 of 147 are refutable" alone
would be the padded number the brief warned about; A1 = 49 is the number that
survives a hostile reading, and both are in RESULT.md.

The C bucket came out *smaller* than the coordinator predicted (44, ~30%), and
the reason is worth stating: this corpus is a school-mathematics corpus, so its
misconceptions are disproportionately about arithmetic and algebra, which is
exactly where our fragments live. A research-mathematics misconception corpus
would invert this.

Two corpus findings fell out of the reading, both recorded in FEEDBACK.md:

1. `fraction-is-two-numbers-not-one` has a distractor whose stated *conclusion
   is true*: "3/4 has to be bigger than 1/2, because 3 and 4 are both bigger
   than 1 and 2". 3/4 > 1/2 is correct. Only the *reasoning* is wrong. That
   makes it unusable as a negative control at face value — the refutable object
   is the extracted rule, not the sentence.
2. Eleven near-duplicate pairs, only one of which is marked deprecated.

## 2026-08-14 — J2 design, and the shape problem I did not expect

Read `crates/axeyum-scenarios/src/lib.rs` and `identities.rs`. The crate's
UNSAT evidence is exhaustive enumeration over *every declared symbol*
(`Scenario::check_unsat`), capped by `EXHAUSTIVE_BIT_LIMIT = 20`. And
`sort_bits` `unreachable!()`s on `Sort::Int` and `Sort::Real`. Consequence:
**every UNSAT scenario in this crate must live over BV/Bool symbols totalling
at most 20 bits** if I want a genuine finite proof rather than a sample. I want
exhaustive, so that is the budget. It is a real constraint and it cut several
QF_LRA candidates from the build (they stay in the census as A2, unbuilt).

Then the thing I had not thought through. The brief wants the suite's expected
verdict to be `unsat`, because an unsat-expecting suite cannot pass vacuously.
But a misconception is normally a **false universal**, and refuting a false
universal is a *satisfiability* question — you exhibit a counterexample. So
naively the whole suite would be SAT-expecting and would have exactly the
vacuity problem it exists to avoid.

The way out, and this is the design decision of the task: sort the
misconceptions into two shapes.

- **Shape U** — the misconception's rule is false at *every* point of a
  nondegenerate box. Then asserting the rule over the box is UNSAT, and the
  UNSAT is a real search, not a ground check. `(a+b)^2 = a^2+b^2` with
  `a,b >= 1` is Shape U. So is `1/(a+b) = 1/a + 1/b`, so is
  `x + x = 7` over the integers, so is the base-rate one.
- **Shape W** — the rule is false only somewhere. Then I pin the counterexample
  region **by properties, not by literals**, and assert the rule there. Example:
  "a non-square rectangle and a square with the same perimeter have the same
  area" — `a+b = c+d`, `c = d`, `a < b`, `a*b = c*d` — is UNSAT over the whole
  box (it is AM-GM), and it is a four-symbol search, not a ground instance.

Everything I build is one of those two, and each scenario records which. A
scenario that could only be made UNSAT by writing the counterexample in as
literals I did **not** build; it would be a one-case "search" and would give a
false impression of what the suite proves.

Overflow is the live soundness hazard here and I want it on the record. Over
`BV(w)` many false identities become *true* by wraparound: `(a+b)^2 = a^2+b^2`
holds whenever `2ab = 0 mod 2^w`, e.g. `w=8, a=16, b=8`. So every scenario
carries an explicit range constraint chosen so no intermediate value wraps, and
where the arithmetic needs more headroom than the enumeration budget allows I
declare narrow symbols and zero-extend (`concat` with a zero constant) before
computing. If I get a bound wrong, `self_check` finds a model and fails loudly —
the enumeration *is* the check, so this is a mechanical guard rather than a
comment.

## 2026-08-14 — implementation

Wrote `crates/axeyum-scenarios/src/misconception.rs` and added
`Family::Misconception`. Wired `misconception_catalog()` into `catalog()` — that
matters, because `crates/axeyum-solver/tests/scenarios.rs`,
`tests/incremental.rs` and `tests/incremental_bv.rs` all iterate `catalog()`.
Adding there puts every negative control through the real
lower-to-AIG-to-CNF-to-SAT path **without editing anything under
`crates/axeyum-solver/`**, which is off-limits to me (agent-i).

Anti-vacuity is enforced by four tests, not by a comment:

1. every scenario in the catalog is `Expectation::Unsat` except the two
   deliberate degenerate controls;
2. every UNSAT one self-checks to `UnsatEvidence::Exhaustive`, never `Sampled`
   — so each is a finite proof;
3. `MIN_REFUTATIONS` floor, so an emptied catalog fails;
4. the strongest one: **degenerate controls that must be SAT.**
   `(a+b)^2 = a^2+b^2` *does* hold at `a = 0`, and
   `(p -> q) <-> (q -> p)` *does* hold at `p = q`. If the encoder were emitting
   garbage that happened to be trivially unsatisfiable, these two would go UNSAT
   and the suite would go red. A count alone would not catch that; this does.

## 2026-08-14 — measurement

Ran the suite in the snapshot, not the live tree. Results in RESULT.md.

## 2026-08-14 — interrupted, resumed from the snapshot

A watchdog killed my stream at 600 s with no progress, right at "wire it into
lib.rs". Worth recording *why nothing was lost*: rule 7's snapshot discipline is
what saved it. Every edit lived in `~/.cache/axeyum-agent-j`, the live worktree
was untouched (its only dirty files belonged to the codex Lean lane and a bench
run), and on resume `cargo test -p axeyum-scenarios --lib misconception` in the
snapshot was still 6/6 green. If I had been editing the shared checkout the
recovery would have been a merge instead of a `ls`.

## 2026-08-14 — mutation-testing my own guards

Before trusting the suite I broke it three ways, restoring after each
(`logs/mutation.log`). Baseline 6/6 green.

1. Strip the no-wraparound range bounds from `binomial_square_spread` and widen
   the symbols to 8 bits → **FAILED**. `self_check` found the model. That is the
   overflow hazard from the design note, caught by enumeration rather than by my
   comment claiming the bound was right.
2. Empty `REFUTATIONS` → **FAILED**, three tests red, including "only 0
   refutations; the floor is 30".
3. Make a degenerate control unsatisfiable → **FAILED**, four tests red.

None of the three guards is removable with the suite still green. That was the
point.

## 2026-08-14 — the guard caught me, not a hypothetical

Measured the curriculum linkage before writing it up, and found
`divisibility-and-euclid` claiming `decidability = "computable"` and
`status = "covered"` with **zero** negative-control evidence — despite the corpus
being full of parity and divisibility errors. Rather than only report it I closed
it: `two_is_prime`, `one_has_two_distinct_divisors`, `odd_plus_odd_is_odd`,
`century_year_is_a_leap_year`.

Writing those is where the design paid for itself. My first encoding of
`one_has_two_distinct_divisors` put `d != e` in the **premises** and left the
claim a tautology (`0 == 0`). Four tests stayed green. The fifth,
`premises_alone_are_satisfiable`, failed:

> one_has_two_distinct_divisors: the premises alone are unsatisfiable, so its
> refutation proves nothing about the misconception

That is exactly the campaign's recurring bug — a control that does not fire —
and it was caught mechanically, on the first run, by a guard written before the
bug existed. Fixed by moving `d != e` from premise to claim, which is what the
misconception actually says.

Dead end worth recording: I tried and abandoned a control for
`relations-and-functions` (`x^2 + y^2 = 1` is not a function of `x`). Every
quantifier-free encoding either needed a witness — making it SAT-expecting, which
defeats the point — or collapsed into contradicting its own premise, which
`premises_alone_are_satisfiable` would have rejected anyway. Left as a gap and
reported as one. Same for `equal-shares-means-envy-free`: I had it censused as
refutable before noticing that for **two** agents proportional *is* envy-free, so
the misconception is only false at three or more. That one is a near-miss where I
would have shipped a wrong control if I had not worked the algebra.

## 2026-08-14 — measurement and landing

Solver measurement needed a binary that depends on both `axeyum-scenarios` and
`axeyum-solver`, and `crates/axeyum-solver/` is agent-k's. Built it as a
throwaway crate *outside* the workspace (`~/.cache/axeyum-agent-j-probe`), never
committed. Result: 32 refuted, 3 witnessed, 0 unknown, **0 wrong**, ~90 ms total.

Separately confirmed that `crates/axeyum-solver/tests/scenarios.rs` — unmodified,
picking my controls up through `catalog()` — passes: 1 test, 6.50 s.

Landed by diff, not by copy: generated a patch of `lib.rs` against
`git show HEAD:...`, `git apply --check`, then `git apply`. The new module file is
new so there was nothing to merge. Live `lib.rs` was byte-identical to HEAD at
apply time, so no drift, but the patch route is the one that would have caught it.

Cost control: measured per-scenario self-check time before committing and shrank
three domains. `matrix_product_entrywise` declared four symbols its assertion
never reads — 854 ms for nothing. Total went 2916 ms → ~700 ms.
