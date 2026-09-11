# Consolidating the Boolean and CDCL(T) engines — plan (DRAFT, 2026-09-10)

**Status:** iteration 2, 2026-09-10. Both research lanes have landed
([R-A migration inventory](../research/03-measurements/cdclt-native-migration-inventory-2026-09-10.md),
[R-B BatSat surface](../research/03-measurements/batsat-slice2-surface-2026-09-10.md))
and **both corrected iteration 1 on its central facts**. What changed is
recorded in §6 rather than silently overwritten, because the errors are the
useful part: one was mine, and the shape of it is a shape this repository keeps
paying for.

**Scope:** retire the duplicated Boolean/CDCL(T) machinery and close the
measured gap to the reference solvers. This is the plan the 2026-09-05
architecture review's D1 ("three Boolean search engines coexist") asked for and
[ADR-1703](../research/09-decisions/adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md)
began.

## 1. Where we actually are

Measured, not recalled.

### 1.1 BatSat is out of the default graph, and its cleanup is not done

`cargo tree -e normal -p axeyum-cnf` returns **zero** batsat, so ADR-1703's
point 4 holds. What ADR-1703 explicitly deferred is Slice 2: *"removes the
feature, the dependencies, and the ~70 historical documentation references. This
ADR does not do that sweep."* It has not run, and R-B measured the surface.

**Dependencies are clean.** All three crates optional, behind
`batsat-reference`, only `axeyum-cnf` owning the `dep:` edges.
`cargo tree -e normal --workspace` over all 27 members: zero hits (positive
control matches `axeyum-cnf` five times). Including dev and build edges: also
zero.

**Docs are 110 tracked files** — not the 104 I counted, not ADR-1703's ~70.
76 historical and keepable, 21 harmless, **13 live-and-wrong**, of which nine
are the same sentence copied nine times.

**Six live `.rs` files still SAY batsat while calling the native core.** The
worst emits a JSON key literally named `"batsat"` for native-core numbers, so
every artifact it has written since 2026-09-05 is mislabelled.

**Two trip-wires.** `scripts/check-parity-docs.py:1295` *pins* one of the false
sentences, so correcting the doc turns that gate red unless the checker moves in
the same commit. And `gate_b_sweep` carries
`required-features = ["batsat-reference"]` — removing the feature removes the
tool that produced the artifact ADR-1703 rests on.

### 1.2 The CDCL(T) migration is done-or-not per module — 5 done, 4 remaining

**Iteration 1 said three modules run both engines. That was wrong and it was my
error**: I counted `#[cfg(test)]` sites as routes. Verified totals for
`CdclT::new` are **4 shipping, 30 in test modules, 2 in test files**.
`lia_theory`, `lra_theory` and `string_theory` have **zero** shipping `CdclT` —
their sites are unit tests, three of which I re-checked by hand. The two sets are
disjoint: **no module runs both engines.**

Three facts that reshape the plan:

- **There is a third driver.** `Dpll` / `IncrementalArithDpll` has **7 shipping
  sites against `CdclT`'s 4**, two of them inside `uflra_online` / `uflia_online`
  themselves. Any plan promising "one driver" must say which of three, and this
  one does: the native core.
- **ADR-1703 never mentions `CdclT`** — zero hits, positive control BatSat 30,
  verified independently. The `CdclT` retirement was never decided. It needs its
  own ADR and must not ride in as Slice 2's neighbour.
- **Warm CDCL(T) does not exist on the native side.** `NativeIncrementalCdcl` is
  `Cdcl<'static, IncrementalSink>` with `T` defaulting to `NullTheory`, and
  `new_empty` lives in an impl block bound to `NullTheory`. **No public
  constructor pairs a theory with a persistent `Cdcl`.** The core names the gap
  itself at `proof_sat.rs:2572-2579`. This is the single blocker under both hard
  migrations.

### 1.3 The search-policy layer was unreachable from the theory side

Fixed today (`4d2fdf068`). `Cdcl::set_policies` had exactly two callers — the
one-shot SAT entry and a unit test — and `TheorySolveOptions` carried no policy
field, so **every** CDCL(T) search ran pinned phases and Luby restarts with no
way to choose otherwise. `RestartPolicy::mode_switching` and
`PhasePolicy::scheduled` were implemented, tested, and had zero production
callers.

### 1.4 The theory interface was the actual gap, and it was one direction

Also fixed today (`e4e6378b8`). `EufTheory::propagate` emitted entailed-`true`
equalities and nothing `false`; its own comment said the `false` direction "is
deferred". On `QF_UF/QG-classification/qg7/iso_icl_repgen004.smt2`:

| | before | after | z3 4.13.3 |
|---|---:|---:|---:|
| theory conflicts | 94,100 | **623** | **559** |
| decisions | 580,871 | 68,448 | 1,699 |
| wall clock (rung) | 75.6 s | 20.6 s | 0.04 s |

**This is the single most important number in this document.** After the fix we
need essentially the reference solver's conflict count. The remaining wall-clock
gap is constant factor, not reasoning quality — a different problem with
different fixes.

Checked and **ruled out** as the same defect: LRA and LIA. Their capability
strings carry the same "Propagation ... (deferred)" phrasing, but
`lra_online::propagate` probes both polarities and emits `value: false`. Their
under-approximation is the equality-atom skip, which is principled (an equality's
negation is a disjunction the conjunctive probe cannot represent). **Do not put
"fix LRA/LIA propagation" in a work queue on the strength of that string.**

### 1.5 Gate (b): the core is competitive with BatSat and behind the references

From ADR-1703, four engines on byte-identical DIMACS, 20 s, pinned cores:

| Family | Files | BatSat | native | CaDiCaL | Kissat |
|---|---:|---:|---:|---:|---:|
| p4dfa | 113 | 4 | **6** | 10 | 11 |
| Noetzli (100 sampled) | 100 | 86 | **86** | 88 | 89 |

Zero cross-engine disagreements over 852 (engine, file) pairs. The native core is
never worse than BatSat. The gap to CaDiCaL/Kissat is real, modest, and
family-dependent — and the note's own caveat is that the host was loaded, so
*ordering* is more reliable than seconds.

## 2. The gap, decomposed

Four distinct problems that get conflated as "our SAT is slow":

| # | problem | evidence | this plan |
|---|---|---|---|
| G1 | Two CDCL(T) drivers, half-migrated | §1.2 | Phase B |
| G2 | BatSat cleanup deferred by its own ADR | §1.1 | Phase A |
| G3 | Theory interfaces under-implemented | §1.4 — 151x on one file | Phase C |
| G4 | Core is behind CaDiCaL/Kissat | §1.5 — modest, measured | Phase D, **last** |

**The ordering is deliberate and is the plan's main claim.** G4 is the one that
looks like the problem and is the least valuable to attack first: gate (b) puts
it at a few files per family, while G3 was worth 151x the conflicts on a single
theory. Tuning a core that the theory starves is spending effort where the
measurement says not to.

## 3. Phases

### Phase A — retire BatSat (ADR-1703 Slice 2)

**A0 (done, `da911539a`).** `SolverConfig::native_cdcl` was documented "read by
nobody" and specified by ADR-1703 as a no-op. It was neither: `solver.rs`'s
warm-route eligibility compared it against its default, so setting a **retired**
flag silently disqualified a query from the warm engine. Excluded from the
comparison, doc corrected to name its two remaining readers. This was a live
defect, not cleanup, which is why it went first and alone.

**A1. Build the replacement referee before removing the current one.** R-B
sharpened the question I asked. The remaining automatic assurance is not
"nothing": model replay covers `sat` completely, and our own DRAT/LRAT checkers
cover `unsat` at 269 call sites across 36 files on default builds —
algorithmically independent, though same-project, and *verifying a refutation is
stronger than corroborating an opinion*. The real exposure is **a defect the
core and our own checkers share**.

The batsat differential never covered that either: it hands batsat the same
`CnfFormula` our parser built. **Only an external binary reading the DIMACS text
is immune** — the CaDiCaL/Kissat arm, not the in-process one. So the replacement
is an external-binary referee, which costs no Cargo dependency and is strictly
stronger than what is being removed.

Note also that the referee being retired **has never run automatically**: no
gate, CI job, justfile recipe or hook uses `--features batsat-reference`,
measured with positive controls. It has provided zero automatic assurance since
the day it landed.

**A2. Fix the 13 live-and-wrong docs**, moving `check-parity-docs.py:1295` in the
same commit — it pins one of the false sentences, so fixing the doc alone turns
that gate red. Leave the 76 historical files alone; they are the record.

**This bucket is pure prose and highly parallelizable.** R-B filtered every
`docs/` batsat line for command shapes and found **no broken command anywhere**:
every runnable line still works today (positive control — `cargo test` appears on
2,520 `docs/` lines, so the empty result is a real negative). All 13 are wrong
*claims*, not broken *instructions*, so none needs re-verification by running it.
Nine are the same sentence nine times, which is one edit repeated.

Count caveat, from the same lane: R-B's own note is a `docs/` file mentioning
batsat, so the sweep returns **111** at or after its landing commit against the
110 it reports. Subtract the note before comparing.

**A3. Fix the six live `.rs` files that say batsat while calling the native
core**, starting with the bench that mislabels its JSON key, and re-label or
re-generate the artifacts it has written since 2026-09-05.

**A4. Remove the feature and the dependencies** — last, and only after A1, since
`gate_b_sweep` requires the feature and produced ADR-1703's own artifact.

*Exit:* three crates absent from every `Cargo.toml`; zero non-historical `.rs`
references; the 13 docs corrected with their checker; and a **named, automatically
running** external-binary check on native-core verdicts.

### Phase B — one CDCL(T) driver, and it is the native core

Sequenced from R-A's dependency order, which inverts the intuitive one.

**B0. Write the ADR.** ADR-1703 does not mention `CdclT`; nothing has decided
this. The ADR must also state which of *three* drivers survives, since `Dpll`
has more shipping sites than `CdclT`.

**B1. `uflia` + `uflra`, together — the cheap half.** One dispatch arm split by
sort. Blocked only by `theory_propagations` not being returned from
`solve_native`, and their recorded deferral reason (a `--trace` gap) **was fixed
in the same commit that recorded it**. Half the remaining migration is waiting on
a stale blocker.

**B2. Build warm CDCL(T) on the native side** — a constructor pairing a theory
with a persistent `Cdcl`. This is the one missing feature under everything else,
and the core already names the gap.

**B3. `qinst_egraph`** after B2: it calls `backtrack_to_root` first thing, which
is already the native between-solves discipline, so it is a swap once B2 exists.

**B4. `ufbv_online.rs` — a swap plus one loop restructure, gated on a probe.
DECIDED 2026-09-10, ADR-1913.**

**Name the file, not "the warm BV client".** That phrase sent a lane to
`incremental.rs`, which has **zero** `CdclT` occurrences (control:
`ufbv_online.rs`, 18) and is already on the native stack. ADR-1908's decision
text was right; this summary line was the ambiguous one, and it propagated into
a brief.

Of the three obstacles the inventory named, one is **refuted**: dormant variables
do exist in `axeyum-cnf`, under the name **`branchable`** (20 occurrences in
`proof_sat.rs`). The inventory had grepped `inactive|dormant|activate_variables`
— a name-blind search, the failure `CLAUDE.md` documents as "do not search for a
thing by the name you have in mind". Its zero reproduces; its conclusion does
not follow. One is confirmed but **mispriced** — the route rebuilds a fresh
`CdclT` every outer refinement round, so the warmth mid-search insertion
protects is one round deep. One is confirmed. A fourth, folded into the third by
the inventory, is separated out.

Gated on a **decoupling probe** that prices the migration without doing it: keep
`CdclT`, replace the three mid-search insertions with backtrack-then-insert, and
compare verdicts, refinement rounds and PAR-2. Five pre-registered falsifiers;
the cheapest is runnable today. "One driver" is refused as a reason, since
ADR-1908 keeps `CdclT` as an oracle regardless.

**B5. Demote `CdclT`, do not delete it.** It is the differential oracle for the
native core — its own docstring says it "decides whether a shipping route may be
moved" — and it caught both defects of the scoping commit, including a
wrong-`unsat` shape. ADR-1703's precedent applies exactly: demote to oracle, as
BatSat was.

*Exit:* the native core on every shipping CDCL(T) path; `CdclT` retained only as
a gated oracle with a **running** differential; every migrated site
verdict-invariant on the committed corpus and the parity slices — this repo has
already measured that moving a route changes give-up reasons and models, not just
speed.

### Phase C — finish the theory interfaces

The EUF fix is the template and the evidence. For each online theory: does
`propagate` emit both polarities, does it implement ADR-1701's `final_check`,
and is there a benchmark family where the conflict count is far above the
reference's? **The conflict-count ratio against z3 `-st` is the instrument** —
it separates "our search is weak" from "our theory is silent", and those have
different fixes. That comparison cost one command today and is what made the
diagnosis possible.

Candidates already named: `xor_matrix.rs`, a 1,595-line complete Gaussian
propagator with zero `src/` callers, which `xor_cdcl.rs:51` names as the
enhancement its incomplete scheme defers to; and `xor_propagate.rs:94`, which
computes implied equalities and keeps only `.len()`.

*Exit:* per theory, either both-polarity propagation with a measured
conflict-count ratio, or a recorded reason it is not applicable.

### Phase D — core tuning, only after A–C

*Entry condition, not a date:* Phase C has closed and a conflict-count comparison
still shows a material gap on a family we care about. Then the CaDiCaL/Kissat
delta is worth attacking, with vivification, chronological backtracking and
mode-switching defaults as the candidate list. `AXEYUM_SEARCH_PROFILE` (landed
today) is what makes those measurable at all from a theory route.

## 4. What this plan does not do

- **Does not tune the core first.** §1.5 prices it and §1.4 outprices it.
- **Does not touch LRA/LIA propagation** on the strength of a capability string
  (§1.4).
- **Does not re-litigate ADR-1703.** BatSat is decided; only its cleanup remains.
- **Does not assume every `CdclT` site migrates.** R-A is asked specifically for
  the exceptions.

## 5. Open questions

1. What is the independent check on native-core SAT verdicts after BatSat goes?
2. Which single missing native feature unblocks the most `CdclT` sites?
3. **Why does the front door need ~4x the budget the rung needs?** Bracketed
   2026-09-10 on the §1.4 file:

   | entry | budget | verdict | wall |
   |---|---:|---|---:|
   | `euf-online` rung, direct | 24 s | **unsat** | 20.6 s |
   | front door | 25 / 30 / 50 s | unknown | burns the whole budget |
   | front door | 120 s | **unsat** | 45.2 s |

   So the rung decides inside 21 s and the front door cannot inside 50 s, but
   can inside 120 s. Two candidates ruled out: `lift_uninterpreted_sort_ite` is
   a **no-op here** (the file contains zero `ite`), and the two
   declared-but-unused symbols (`declare-sort U`, `declare-fun op1`) change
   nothing — stripping them reproduces the same result to 0.1 s. The remaining
   hypothesis, consistent with the 120 s row, is that the ladder hands
   `euf-online` roughly a **third** of the clock rather than the full remaining
   budget the code appears to give it, and something ahead of it spends the
   rest. Not yet identified; this is the highest-value unexplained number in
   this document, because it is what a user actually hits.

   **This is a measurement, not a diagnosis** — do not put a fix in a queue
   from it.

## 6. What iteration 1 got wrong

Recorded rather than overwritten, because both errors are instances of shapes
this repository keeps paying for.

**Mine, and the load-bearing one.** Iteration 1 said three modules run both
engines, from a `grep -c` that counted `#[cfg(test)]` sites as routes. The real
split is 4 shipping against 30 in test modules, and **no module runs both**. A
plan built on that would have scoped "decide per entry point" work that does not
exist. The general form: *a count is not an inventory*, and a count over a
pattern that matches test code is a measurement of the wrong population.

**Inherited.** Iteration 1 took ADR-1703's "~70 documentation references" and my
own 104 at face value; the verified number is 110, and 111 after R-B's note
lands. Also `SolverConfig::native_cdcl` was described by its own doc and by
ADR-1703 as inert, and was silently disqualifying queries from the warm engine.
*A decision record describes what was decided, not necessarily what shipped.*

**A false lead caught before it entered a queue.** The deferred-code survey
flagged LRA and LIA as carrying EUF's "Propagation ... (deferred)" defect on the
strength of a matching capability string. Reading the code showed both already
propagate in both directions. §4 records the refusal so it is not re-found.
