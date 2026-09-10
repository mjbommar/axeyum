# Consolidating the Boolean and CDCL(T) engines — plan (DRAFT, 2026-09-10)

**Status:** draft. Two research lanes (R-A: migration inventory, R-B: BatSat
Slice 2 surface) are in flight; sections marked **[pending R-A]** / **[pending
R-B]** are placeholders and must not be executed from until they land.

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
ADR does not do that sweep."* It has not run. **104** files under `docs/` still
mention batsat (the ADR estimated ~70), and ten `.rs` files still reference it,
not all of which are obviously feature-gated. **[pending R-B]** for the exact
four-bucket split and what is load-bearing.

### 1.2 The CDCL(T) migration is half-done *per module*, not per module

`CdclT` (`cdclt.rs`, 4,176 lines) and the native adapter (`native_cdclt.rs`,
764 lines, onto `proof_sat.rs`'s 8,945) both ship. Crude first count:

| module | `CdclT::new` | `solve_native` |
|---|---:|---:|
| `lia_theory` | 2 | 1 |
| `lra_theory` | 2 | 1 |
| `string_theory` | 1 | 1 |
| `ufbv_online` | 2 | 0 |
| `uflia_online` | 1 | 0 |
| `uflra_online` | 1 | 0 |
| `qinst_egraph` | 1 | 0 |
| `euf_egraph`, `dl_online` | 0 | 1 |

Three modules run **both engines depending on which entry point you hit**. That
is the fact that shapes the plan: this is not "swap five call sites", it is
"decide, per entry point, which engine it should be on and why". **[pending
R-A]** for the verified site-by-site inventory and the feature-parity matrix.

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

### Phase A — retire BatSat (ADR-1703 Slice 2) **[pending R-B]**

Cheapest, lowest risk, already decided. The only judgement call is what replaces
the differential suite as the independent check on the native core's verdicts —
if the answer is "nothing for pure SAT", that must be stated before the feature
goes, not after.

*Exit:* `batsat`, `rustsat`, `rustsat-batsat` absent from every `Cargo.toml`;
zero non-historical `.rs` references; docs split into "historical record, keep"
and "live guidance, fix"; and a named, running independent check on native-core
verdicts.

### Phase B — one CDCL(T) driver **[pending R-A]**

*Exit:* one driver on every shipping path, `cdclt.rs` deleted or reduced to
whatever R-A shows is genuinely better there, with the reason recorded. Every
migrated site verdict-invariant on the committed corpus **and** the parity
slices — this repo has already measured that moving a route changes give-up
reasons and models, not just speed.

Sequencing comes from R-A's dependency order, not from module size.

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
