# Lane: registry-stale — the staleness gate could not see a rewritten function body

<!-- plan-section: lane-status -->

**The 11 stale rows were really 24** (`DONE`, registry-stale, 2026-09-15,
[ADR-2085]). `check-config-registry-staleness.py` exited 1 on `main` with 11
rows and was registered in `scripts/check.sh` and the `justfile` and in **no
hook** — the third checker found rotting in that position in one week. Triaging
all 11 against the DIFFS rather than the commit subjects found three false
positives, one row red for the wrong reason, and a blind spot that makes the
headline number wrong.

**`git log -G<symbol>` cannot see a function body, because a body does not
repeat its own name.** `ee36e0421` gave `lra.rs::decide_within` a `deadline`
parameter and took it from **163 lines to a 7-line wrapper**; of the five changed
lines mentioning `decide_within`, **three are `///` doc comments and two are
calls inside `#[cfg(test)]`**. The gate reported that row for its comments and
its tests and would have called it CLEAN had the commit been tidier. Comparing
each symbol's DEFINITION against the tree its measurement saw finds **16 rows the
pickaxe cannot see, across eight entries nobody knew were stale** — including
`lra_theory.rs::MAX_ONLINE_LRA_ATOMS`, the founding example in the gate's own
docstring.

**Three false positives, all in the class the filter already claimed to remove,
all invisible because it is per-line.** `MAX_PRE_SAT_CNF_VARS`'s only two
mentions in `a4642ce8d` are continuation lines of a six-line `format!` (no quote
character on the line, so the filter saw bare code). `ac43d6031` changed 28 lines
of `lra.rs`, **all 28** inside one `#[cfg(test)]` module, and made three rows
stale; `0e7057f4f` added 799 lines, 773 in that module and the other 26 a blank
line plus a `///` block. `lra.rs` carries **seven** `#[cfg(test)]` attributes,
decorating free functions and structs as well as modules, so a "tail of the file"
heuristic is wrong.

**No constant turned out not to hold.** Three values were checked directly and
are unchanged (`10_240`, `16_384`, `4_000_000`); two dependency definitions are
byte-identical (`GroundBudget`, `simplex_admission`). **Four rows are genuinely
stale** — `SIMPLEX_FIRST_AT_CONSTRAINTS` and `MAX_TABLEAU_CELLS` against
`decide_within`/`simplex_fallback`, whose definition went 71 → 155 lines — and
the 22-file and 200-file `QF_LRA` re-runs they need **were not performed by this
lane**.

**The backlog is a ledger, not a date bump.**
`artifacts/config-registry-accepted-staleness.tsv` carries one row per accepted
staleness with a **required** reason; the gate fails on a stale row not in it AND
on a row in it that is no longer stale, so it fails in **both** directions. Eight
rows carry a line-by-line triage, sixteen are labelled `DETECTED` and honestly
not triaged.

**L0 registration, verified rather than asserted.** The simulation parses the
gate list OUT of `hooks/pre-push`, runs the loop clean and with one accepted row
deleted, and requires the clean arm to pass all 11 gates and the stale arm to be
rejected AT THIS GATE; the ledger is restored byte-for-byte. Its cost was **not**
the "0.1-second-class" the brief assumed — measured **14.6 s** against an L0
block whose ten other gates total **4.4 s** — so it was made **3.5 s (4.1x)**
first, report byte-identical, with `--self-test` comparing the rewrite against
the retained pickaxe over all **140** dependency pairs. That control caught
**two** real bugs in the rewrite (64 pairs, then 4), both in the direction of
MORE staleness.

**The pre-existing control suite was already red on `main`.** Step 4 asserts
`MAX_TABLEAU_CELLS` is not reported and `FLOOD_ROUND_ADMISSION_CAP` is; against
main's own checker they appear **5** and **0** times. Both halves had rotted. It
now uses two subjects from one commit, one silenced and one kept, runs with
`--registry` so the ratchet does not suppress the listing it greps (without which
its first half passed **vacuously**), and is mutation-checked to kill exactly one
half.

**79 % undated is a design, not a backlog.** `DATED_FLOOR` ratchets dates and
deliberately not the share, and **359 of the 388** undated entries do carry a
written doc-comment rationale — only **28** have nothing. The gate can only
police the 100 dated entries and their 140 dependency pairs.

**The registry shares ADR-2080's blindness and more.** The staleness checker
never calls `config_registry_scan.py` at all (0 references, though that script's
docstring names it as one of "two consumers that must agree"); the coverage test
that would backstop registration governs **21 of 2222** workspace `.rs` files and
matches only scalar/`Duration` `const`s; struct-valued constants and bare
struct-literal fields are invisible and documented as such in-tree; and this
week's own work added a new class — the governing value is a FUNCTION
(`moderate_pre_sat_envelope()`, `sparse_simplex_rows_enabled()`), which
`CONST_RE` cannot see.

**Next.** Re-measure the four genuinely-stale rows; triage the sixteen
`DETECTED` rows (two of three definition comparisons done here came back
byte-identical, so they are likely cheaper than they look); and use
`measured_at_commit` as the cutoff where it exists — 51 of 100 dated entries
already record it and the checker parses the field and never uses it.

| change | commit |
|---|---|
| gate 4.1x faster, report byte-identical, `--self-test` equivalence control | `40618c358` |
| definition-drift signal, per-line filter extended, accepted-staleness ratchet, L0 registration, controls repaired | `d6210e1e5` |
| [ADR-2085] and lane status | this commit |
