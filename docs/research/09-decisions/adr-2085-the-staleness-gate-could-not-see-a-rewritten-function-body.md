# ADR-2085: the staleness gate could not see a rewritten function body, so 11 stale rows were really 24, and the backlog becomes a ledger rather than a date bump

Status: accepted
Index-summary: `check-config-registry-staleness.py` exited 1 on `main` with **11** stale rows and was registered in `scripts/check.sh` and the `justfile` and in **no hook** — the third checker found rotting in that position in one week. Triaging all 11 against the DIFFS rather than the commit subjects found three false positives, one row red for the wrong reason, and a blind spot that makes the headline number wrong. **`git log -G<symbol>` matches commits whose patch text MENTIONS the symbol, and a function body does not repeat its own name**: `ee36e0421` gave `lra.rs::decide_within` a `deadline` parameter and took it from **163 lines to a 7-line wrapper**, and of the FIVE changed lines mentioning `decide_within`, **three are `///` doc comments and two are calls inside `#[cfg(test)]` code** — the gate reported that row for its comments and its tests and would have called it CLEAN had the commit been tidier. A definition-level comparison against the tree the measurement saw finds **16 rows the pickaxe cannot see across eight entries nobody knew were stale**, including `lra_theory.rs::MAX_ONLINE_LRA_ATOMS`, the founding example in the gate's own docstring. True count **24 rows across 14 entries, not 11**. Three separate false positives, all in the class `symbol_occurs_in_code` already exists to remove and all invisible to it because it is **per-line**: a mention on a continuation line of a six-line `format!` (`MAX_PRE_SAT_CNF_VARS`, the constant's ONLY two mentions in `a4642ce8d`), and mentions inside `#[cfg(test)]` items (`ac43d6031` changed 28 lines of `lra.rs`, **all 28** inside one test module, and made three rows stale). Clearing 24 needs fourteen corpus measurements, and the two ways to go green without them are both forbidden by the gate's own rule, so the backlog is **written down** in `artifacts/config-registry-accepted-staleness.tsv` with a REQUIRED reason per row; the gate fails on a stale row not in it **and** on a row in it that is no longer stale, so it can fail in **both** directions. Eight rows carry a line-by-line triage, sixteen are labelled `DETECTED` and honestly not triaged. The gate is now in the pre-push **L0** block, verified by simulating the loop — gate list parsed OUT of `hooks/pre-push`, clean arm passes all 11, stale arm rejected AT THIS GATE, ledger restored byte-for-byte. Its cost was **not** the "0.1-second-class" the brief assumed: measured **14.6 s** against an L0 block whose ten other gates total **4.4 s**, so it was made **3.5 s (4.1x)** first, report byte-identical, with a `--self-test` comparing the rewrite against the retained pickaxe over all **140** dependency pairs — that control caught **two** real bugs in the rewrite, both in the direction of MORE staleness. The **pre-existing** control suite was **already red on main**: step 4 asserts `MAX_TABLEAU_CELLS` is not reported and `FLOOD_ROUND_ADMISSION_CAP` is, and against main's own checker they appear **5** and **0** times. **79 % undated is a design, not a backlog** — `DATED_FLOOR` ratchets dates and deliberately not the share — and **359 of the 388** undated entries do carry a written doc-comment rationale, only **28** nothing at all. The gate **does share ADR-2080's blindness and more**: it never calls `config_registry_scan.py` at all (0 references, though that script's docstring names it as one of "two consumers that must agree"), and the coverage test that would backstop it governs **21 of 2222** workspace `.rs` files and matches only scalar/`Duration` `const`s.
Index-status: accepted
Date: 2026-09-15

## Context

`python3 scripts/check-config-registry-staleness.py` exited **1** on `main`:

    config registry: 488 entries, 100 dated, 388 undated (79%).
    STALE: 11 dated justification(s) predate a change to the code they protect.

It was registered at `scripts/check.sh:1688` and in the `justfile` and **in no
hook**, so only the ~10-minute aggregate gate lanes are steered away from could
find it. That is the third checker found rotting in exactly that position in one
week; `mutation-anchors-are-fresh` was the first and had been red for five days.

Branch base: `git merge-base main HEAD` is
`2e8582f89afb7fda0424cfab74e88ecd5934b2ec`, which **is** local `main`'s HEAD.

The rule the gate states, and which this ADR does not route around:

> Re-take the measurement, or narrow the entry's `rests_on` if the change cannot
> affect it. **Do NOT simply move the date.**

## Triage rules, pre-registered

Written after reading the checker and the gate's summary lines (entry names,
`rests_on` symbols, commit subjects) and **before opening a single diff**,
because deciding the rule per-entry after seeing the work is how "narrow it"
becomes the default.

- **A. RE-MEASURED** — required when the diff changes, in non-test code, the
  constant's value, a control-flow path whose traversal count the measurement
  quantifies, or the cost model it priced. Evidence is the measurement re-run,
  with the comparable denominator printed beside any zero.
- **B. `rests_on` NARROWED** — only when the named symbol is BROADER than the
  basis and every changed line mentioning it lies outside the basis, the
  narrowed dependency is still real, and the argument needs no "probably".
  Narrowing away the LAST dependency is forbidden: the gate's own docstring says
  a justification resting on nothing cannot go stale.
- **C. COVERED BY AN EXISTING MEASUREMENT** — citation must name division, row
  count and channel.
- **D. CHECKER UNDER-DISCRIMINATION** — a state the brief did not list. The
  `-G` proxy matches the symbol anywhere in the patch, including a test that
  merely CALLS it; `symbol_occurs_in_code` already filters strings and comments
  on exactly this reasoning. Claiming it requires every mentioning line to lie
  inside a `#[cfg(test)]` region **verified against the file AS OF THAT COMMIT**,
  no line inside the symbol's own definition changed, and the fix to go in the
  CHECKER because it is a class.
- **E. LEFT STALE, LABELLED** — the change is real and the re-measurement is not
  affordable. Recorded with the reason.

Standing rules: gate status read UNPIPED from a file, never `| tail`; the
denominator printed beside any zero; "only a test change" is a claim about a
diff, never inferred from a subject.

## Decision

### 1. The gate could not see the thing it exists to detect

`git log -G<symbol>` matches commits whose **patch text mentions the symbol**.
For a CONSTANT that is a fair proxy — uses spell its name. For a **function** it
is close to backwards: the behaviour lives in the body, and a body does not
repeat its own name.

Measured on this registry's own red rows. `ee36e0421` gave `lra.rs::decide_within`
a `deadline` parameter and per-stretch deadline polls, and the function went from
**163 lines to a 7-line wrapper** over `decide_within_with_options`. Every changed
line in that commit that mentions `decide_within`:

| line | kind |
|---|---|
| 132, 150, 160 | `///` doc comment |
| 181, 188 | call inside `#[cfg(test)]` |

So the gate reported `SIMPLEX_FIRST_AT_CONSTRAINTS` stale **for its comments and
its tests**, and would have reported it CLEAN had the commit been tidier — while
the measurement genuinely no longer describes the function. A red that carries no
information either way is the shape this repository calls a checker that cannot
fail.

`definition_changed` compares the symbol's definition at HEAD against the tree
the measurement saw (`git rev-list -1 --before=<measured_on> 23:59:59`), over
comment- and string-stripped text with brace-matched extent. It finds **16 rows
the pickaxe cannot see**, across eight entries nobody knew were stale —
`MAX_EXPAND_INSTANCES`, `DEFAULT_INT_LINEAR_PORTFOLIO_WORKERS`,
`UF_ARITH_LADDER_RESERVE_SHARE`, `UF_FMF_PROBE_SHARE`, `SKELETON_SOLVE_DEFAULT`,
`EUF_ONLINE_ABSTRACT_CEILING`, `EUF_ONLINE_ABSTRACT_SHARE`,
`DEFAULT_ONLINE_LRA_BUDGET_BYTES` and `MAX_ONLINE_LRA_ATOMS` — the last being the
**founding example in this gate's own module docstring**.

**True count: 24 rows across 14 entries, not 11.**

### 2. Three false positives, all in a class the filter already claimed

`symbol_occurs_in_code` exists to drop mentions inside strings and comments, and
its docstring says a gate that fires on a string literal "costs the gate its
authority". It is **per-line**, so two cases are invisible to it:

- **A multi-line string literal.** `dpll_lia.rs::MAX_PRE_SAT_CNF_VARS`'s only two
  mentions in `a4642ce8d` are continuation lines of a six-line `format!`:

      >{MAX_PRE_SAT_CNF_VARS}, moderate_envelope<={envelope_atoms}/\

  There is no quote character on that line, so the filter saw bare code.
- **A `#[cfg(test)]` item.** `ac43d6031` changed **28 lines** of `lra.rs`, **all
  28** inside `mod give_up_reason_tests`, and made three rows stale. `0e7057f4f`
  added **799** lines, **773** in that same module and the other **26** a blank
  line plus a `///` block on it — zero production code. A test that CALLS a
  function cannot change what the function computes.

Both are now decided from the file **at that commit**, on the correct side of the
diff, and conservatively: an unparseable file falls back to the per-line filter,
and the test-region walk claims only regions it can brace-match.

`lra.rs` carries **seven** `#[cfg(test)]` attributes, not one, and they decorate
free functions and structs as well as modules — a "tail of the file" heuristic
returns the wrong answer, so the region is the decorated ITEM.

### 3. The backlog becomes a ledger, because the alternative is a rubber stamp

Clearing 24 rows means fourteen corpus measurements; the `MAX_TABLEAU_CELLS`
basis alone is the committed 200-file `QF_LRA` list at 24 s and 8 GiB per file.
The two ways to go green without them are both forbidden by the gate's own rule —
move the dates, or delete the `rests_on` entries, which is the same thing with
extra steps.

`artifacts/config-registry-accepted-staleness.tsv` records one row per accepted
staleness with a **required** reason. The gate fails on a stale row **not** in it
(a measurement newly gone stale) and on a row in it that is **no longer** stale (a
line that has stopped describing anything). It can fail in **both** directions,
which is what separates a ratchet from a suppression list; a row with an empty
reason exits 2.

The ratchet applies only to the in-tree registry: under `--registry <copy>` the
stale set differs by construction, which is what the copy is for.

### 4. Per-entry triage of the original 11

| entry → `rests_on` | state | evidence |
|---|---|---|
| `ABV_ONLINE_LADDER_RESERVE_SHARE` → `dispatch_abv_online` | **E**, labelled | `b47972ab9` changed the CALL SITE (`?` → `rung_or_decline`). Net-of-everything the definition differs by **4 non-comment lines, all inside the `Err(Unsupported)` arm** — `record_declined` gets `unsupported_decline(&message)` instead of a bare `DeclineReason::Unsupported`. Telemetry, same control flow. The basis is a TIMEOUT measurement; this touches only the error path. Not re-measured. |
| `ABV_ONLINE_LADDER_RESERVE_SHARE` → `dispatch_array_fast_paths` | **E**, labelled | Definition changed by **comment rewording only** — 40 → 42 lines, **0** non-comment lines. The call-site change makes this route MORE reachable: an `Unsupported` used to `?`-abort the dispatcher before the fast paths ran, so the basis's "the fast paths are still what runs after it" is *more* true than when measured. |
| `MAX_PRE_SAT_CNF_VARS` → self | **D**, closed | Only two mentions, both continuation lines of a `format!`. False positive of the per-line filter. |
| `MAX_MODERATE_PRE_SAT_ARITH_ATOMS` → self | **E**, labelled | Value **10_240 before and after**; predicate preserved verbatim (`\|\|` for the envelope, `&&` for the base trigger). Reads routed through `moderate_pre_sat_envelope()`, which returns the shipped pair unless `AXEYUM_GROUND_DECIDE_PRESAT_ENVELOPE` parses — fail-closed, pinned over unset plus **13** malformed spellings. Denotationally identical in the shipped configuration. |
| `MAX_MODERATE_PRE_SAT_CNF_VARS` → self | **E**, labelled | Same commit and argument; value **16_384 before and after**. |
| `SIMPLEX_FIRST_AT_CONSTRAINTS` → `decide_within` | **A required**, not run | Red for its comments and tests; **genuinely stale** — 163 → 7 lines. Needs the 22-file `QF_LRA` re-run. This row is why §1 exists. |
| `SIMPLEX_FIRST_AT_CONSTRAINTS` → `simplex_fallback` | **A required**, not run | **Genuinely stale.** 71 → 155 lines, 62 non-comment lines changed, across `ee36e0421`, `f6303ee7a`, `4abc994a0`. |
| `MAX_GROUND_TERMS` → `GroundBudget` | **D**, closed | `GroundBudget`'s definition is **byte-identical** (21 lines) to the measurement tree. Both commits' mentions are `///` doc comments plus one `GroundBudgetGuard::set(...)` line inside `#[cfg(test)]`. |
| `MAX_TABLEAU_CELLS` → self | **E**, labelled | Definition line **byte-identical** (`4_000_000`). Six mentions in `4abc994a0`: three `///`, two in a `#[cfg(test)]` assertion, one real new use behind the `AXEYUM_LRA_CELL_CAP=1` lever, default OFF. |
| `MAX_TABLEAU_CELLS` → `simplex_admission` | **E**, labelled | `simplex_admission`'s definition is **byte-identical** (16 lines). `f6303ee7a` moved the call site and folded the pre-existing `simplex_first(n)` test onto one line. The basis's stated dependency holds. |
| `MAX_TABLEAU_CELLS` → `simplex_fallback` | **A required**, not run | **Genuinely stale**, same 71 → 155 rewrite. The entry's basis is an explicit measurement OF this function (36 files reach it, 3,129 calls, seven build a tableau over the cap at 4.2–8.8 M cells). |

No constant turned out **not** to hold. Three values were checked directly and
are unchanged (`10_240`, `16_384`, `4_000_000`), and two dependency definitions
are byte-identical (`GroundBudget`, `simplex_admission`). What changed is the
confidence available for the rest: four rows are genuinely stale and need corpus
runs this lane did not perform.

**ADR-2060 does not cover these.** Its give-up split was measured verdict-neutral
on four channels (0 gains, 0 losses, 0 flips of 159, 0 of 200 changed exit class,
0 of 185 soundness disagreements). Those are VERDICT channels;
`SIMPLEX_FIRST_AT_CONSTRAINTS` and `MAX_TABLEAU_CELLS` rest on **route-timing and
allocation-count** claims, which no verdict-neutrality result establishes.

**A separate finding, independent of any date:** the `MAX_TABLEAU_CELLS` note says
the `feasible` cell-bound gap was "NOT ADDED". `4abc994a0` added it as an
off-by-default lever. The note's *wording* is stale.

### 5. L0 registration, verified rather than asserted

The gate joins the pre-push L0 block — the mirror-image of the
`mutation_controls.py --check-anchors` argument: a justification goes stale when
RUST moves, but the repair is a Python/TSV edit, so a docs-only push must be
gated too, and L0 is the only block before the `shas_to_gate` early exit.

**Its cost was not free and was not assumed.** The brief calling for this
registration described the gate as "0.1-second-class". Measured: **14.6 s**
(median of 4, spread 14.52–14.63) against an L0 block whose ten other gates total
**4.4 s**. Registering it unchanged would have made L0 **4.3x** slower on every
push. `cProfile` found `introducing_commit` running **74** times for **7.08 s** of
an 11.08 s run with only **9** of those having a row to filter; the pickaxe
re-walked history once per SYMBOL (140 invocations) though the candidate COMMITS
depend only on (date, path) (**51** distinct pairs); and patches arrived in 51
logs plus 353 `git show`s. Now **3.5 s**, **4.1x**, report byte-identical.

The simulation parses the gate list **out of** `hooks/pre-push` — so a
registration that never landed fails here instead of being claimed — runs the
loop on the clean tree and on a tree with one accepted row deleted, and requires
the clean arm to pass all **11** gates and the stale arm to be rejected **at this
gate**. The ledger is restored and compared byte-for-byte afterwards.

### 6. The controls, including the one that was already red

`--self-test` runs the retained pre-rewrite pickaxe (`pickaxe_commits_after`) and
the new `commits_after` over **every** dependency the registry declares and
requires identical rows, printing the denominator beside the zero and exiting 2
if the population is empty. It earned its place twice:

- **64 of 140** pairs disagreed on the first run. `_commit_changes_symbol_in_code`
  ended in `return not saw_occurrence` — KEEP when the patch does not mention the
  symbol at all, which was conservative under the pickaxe and keeps *every
  unrelated commit* under full enumeration.
- **4** pairs disagreed on the second, all on one commit, `bec2cf65b`, a **merge**.
  `git log -G` generates no patch for a merge; `git show` does.

Both bugs produced a checker that fires MORE, which is the direction that looks
like diligence.

`scripts/tests/test-config-registry-ratchet.sh` requires the unmutated ledger to
pass, a deleted row to fail, a no-longer-stale row to fail, an empty reason to
exit 2, and `--self-test` to have compared a NONZERO number of pairs.

**The pre-existing control suite was already red on `main`.**
`test-config-registry-staleness-control.sh` step 4 asserts that
`MAX_TABLEAU_CELLS` is **not** reported and `FLOOD_ROUND_ADMISSION_CAP` **is**.
Run against main's own checker: `MAX_TABLEAU_CELLS` appears **5** times,
`FLOOD_ROUND_ADMISSION_CAP` **0**. Both halves had rotted — the first because
`MAX_TABLEAU_CELLS` acquired three genuine changes since 2026-09-10, the second
because its subject is no longer stale at all and so could not pass however well
the gate worked. Step 4 now uses two subjects from **one** commit (`a4642ce8d`),
one silenced and one kept, and runs with `--registry` so the ratchet does not
suppress the listing it greps — without which its first half passed **vacuously**.
Mutation-checked: removing the line-flags guard brings the string-only false
positive back and leaves the real-change half passing, so **exactly one** half
dies. Step 3's oracle moved from "the gate exits 0" to "this entry is not named";
those were the same thing only while no other entry was stale.

## The two structural facts the checker reveals

### 79 % undated is a design, and the undated are not unexamined

`DATED_FLOOR = 77` ratchets the number of DATED entries upward (currently 100)
and **deliberately does not ratchet the share** — its own doc comment says
ratcheting the share "would punish honest coverage work", because registering a
governing value nobody has measured is exactly what the module wants a lane to
do, and it moves the percentage the wrong way.

The 388 undated entries break down as:

| `undated(...)` location | count |
|---|---|
| `"doc comment"` | 359 |
| `"no written justification"` | 28 |
| `"doc comment + ADR-0119"` | 1 |

So **359 of 388 (93 %)** carry a written rationale; only **28** have nothing at
all. "Undated" here means *"a reason exists, no dated measurement backs it"*, not
*"nobody looked"*.

The consequence for this gate is exact: it can only police the **100 dated
entries and their 140 `rests_on` pairs**. An undated entry cannot go stale
because it never made a measurement claim — which is also why the well-formedness
rule requires a dated entry to name a dependency.

### Yes, the registry shares ADR-2080's blindness — and it is wider

ADR-2080 found that `config_registry_scan.py` derives its population from `const`
declarations, so a coverage checker over declarations is structurally blind to an
**absent** one. All of that applies here, plus:

1. **The staleness checker's population is the registered entries.** An
   unregistered constant is invisible to it outright.
2. **It never calls `config_registry_scan.py` at all** — 0 references — although
   that script's docstring opens "Shared by two consumers that must agree" and
   names this checker first. The documented coupling does not exist.
3. **The coverage test that would backstop registration governs 21 of 2222
   workspace `.rs` files.**
4. **Struct-valued constants are invisible to it**, documented in-tree twice and
   closed by neither: `ONLINE_QUANTIFIER_LIMITS` (2026-09-09, "the coverage
   scanner in this file matches only scalar and `Duration` types, so
   `every_governing_constant_is_registered` could never have named it") and the
   `RelevancePolicy` entry ("registered here because someone chose to, not
   because a gate would have caught its absence").
5. **Bare literals in struct-literal fields are invisible** — `cas_poly.rs`'s
   `ideal_limits()` sets `reduction_steps: 6_000`, `pair_iterations: 1_500`,
   `basis_size: 32`, `poly_terms: 256`, flagged in a note precisely because no
   tool can reach them.
6. **A new class this week's own work created: the governing value is a
   FUNCTION, not a `const`.** `moderate_pre_sat_envelope()` (`a4642ce8d`) and
   `sparse_simplex_rows_enabled()` (`4abc994a0`) read the environment and return
   the operative bound. `CONST_RE` cannot see either.

So an unregistered constant is invisible to both checkers at once, and the set of
things that can be governing-but-unregistrable is larger than "a `const` someone
forgot".

## Consequences

- The gate exits **0** and is in L0, with a 24-row backlog that is visible,
  reasoned, and can only shrink without a fight.
- **Four rows are genuinely stale and are recorded as such.** The measurements
  they need — the 22-file and 200-file `QF_LRA` runs — were **not** performed by
  this lane and are the obvious next task.
- The sixteen `DETECTED` rows are honest unknowns. Triaging them is a second
  task, and each is likely to be cheaper than it looks: two of the three
  definition-level comparisons done here came back byte-identical.
- **The recommendation this ADR does not implement:** 51 of the 100 dated
  entries already carry a `measured_at_commit`, and the checker parses that field
  and never uses it — the cutoff is the DATE, which cannot even see a commit
  landing later the same day. Using the recorded commit where it exists is
  strictly more precise and costs nothing.

## Alternatives rejected

- **Move the dates.** The rubber stamp the gate exists to prevent.
- **Narrow `rests_on` until it passes.** The same thing with extra steps, and for
  the self-resting constants there is nothing narrower than the constant.
- **Ship the `#[cfg(test)]` filter alone.** It was written first, and measuring it
  showed it would silently turn `SIMPLEX_FIRST_AT_CONSTRAINTS` → `decide_within`
  green while that entry is genuinely stale — the accidental red was the only
  thing covering the blind spot. Fixing one defect required fixing both.
- **Leave the gate red and out of L0.** Honest, but it leaves the structural hole
  the lane was asked to close, and a red gate nobody can act on is how this one
  sat red in the first place.
