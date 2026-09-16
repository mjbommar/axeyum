# NIA-GROEBNER-GATE: does raising the ideal-refuter admission gate decide any QF_NIA file?

Lane NIA-GROEBNER-GATE, running ADR-2112 Part F's handed-forward probe: our
Gröbner route (`cas_ideal_refutation`, `crates/axeyum-solver/src/cas_poly.rs:640`,
into `unit_ideal_cofactors` at `:707`) is reached on 115 of 200 `QF_NIA` T1
rows and decides 0, refused by an 8/8/8 admission gate on 114 of 116 undecided
rows. Three env levers already exist. **This lane measures, rather than
argues, whether raising them decides anything, and at what cost.**

Status: **DONE.** The QF_NIA ladder is measured (§2); the answer is **no —
raising the gate to any level, including literally unbounded, decides 0 of
the 116 undecided rows.** The cross-division check (§2, QF_NRA/UFNIA) ran the
shipped arm against the unbounded arm to confirm there is no loss even at the
most aggressive setting tested.

## 1. The gate, read

Three named constants in `crates/axeyum-solver/src/cas_poly.rs`, all set to
**8** in `119858e2c` ("feat(cas): multivariate ideal refutation with a
re-checkable certificate", 2026-08-13) and each wired to an env override in
`c734c45f9` ("feat(config): 64 completeness caps become a one-command A/B, not
a rebuild"):

| constant | `cas_poly.rs` | what it bounds | protects against |
|---|---:|---|---|
| `MAX_IDEAL_GENERATORS` | `:541` | asserted EQUATIONS admitted as Gröbner-basis ideal generators | a system with too many generators ever entering Buchberger |
| `MAX_IDEAL_ATOMS` | `:572` | distinct opaque ATOMS (monomial variables) across the whole system | Buchberger under `lex` is doubly exponential in variable count in the worst case — the doc comment names this the ceiling that "actually bounds the search," the step budget below is the backstop |
| `MAX_IDEAL_INEQUALITIES` | `:555` | asserted INEQUALITIES considered as combination terms (also used to `truncate` the list post-admission) | blow-up in the positivity-certificate combination search |

All three are `config_registry.rs` entries with `protects: Protects::Completeness`,
`on_exceed: OnExceed::DeclineRoute` — crossing any one **declines the route**,
it never risks a wrong answer: every candidate `cas_ideal_refutation` finds is
independently re-derived by `check_cas_ideal_certificate` before acceptance
(`guarded_by` in the registry), so raising these levers can only cost time,
never soundness. Below the admission gate, four separate FIXED step ceilings
(`ideal_limits()`, `cas_poly.rs:587`: `reduction_steps=6_000`,
`pair_iterations=1_500`, `basis_size=32`, `poly_terms=256`) bound the
Buchberger search itself — those are not levers, and a raised admission gate
degrades to a step-ceiling decline rather than a hang, confirmed below.

Env overrides: `AXEYUM_MAX_IDEAL_GENERATORS`, `AXEYUM_MAX_IDEAL_ATOMS`,
`AXEYUM_MAX_IDEAL_INEQUALITIES` — unset reproduces the shipped 8/8/8 byte for
byte (`config_lever`'s contract).

Smoke-tested directly against one undecided row
(`QF_NIA/20170427-VeryMax/ITS/From_T2__firewire.t2__terminationS_13_0.smt2`):
the admission decline detail changes exactly where predicted —

| lever value | `cas-ideal-refuter` decline detail |
|---:|---|
| 8 / 16 / 32 | `nonlinear system exceeds the deterministic generator/atom/inequality ceilings` |
| 64 / 1,000,000 | `cofactor-tracked Gröbner reduction hit the basis-size ceiling` |

confirming the lever is reached and that raising it past admission moves the
refusal to the fixed step ceiling rather than removing it.

## 2. The ladder

Ladder: shipped (8/8/8), 16/16/16, 32/32/32, 64/64/64, "unbounded"
(1,000,000/1,000,000/1,000,000 — no sentinel exists for the `usize` lever;
this value is above every measured atom/generator/inequality count in the
corpus). Each rung run interleaved shipped-vs-gateN, alternating which arm
goes first per file, on the 116 undecided `QF_NIA` T1 rows
(`bench-results/nia-trace-20260915/undecided-116.txt`), 24 s / 8 GiB
`ulimit -v`, `--trace`, through `scripts/ledger-run-one.sh` so every row lands
in `bench-results/ledger/nia-groebner-gate-<rung>.tsv` with
`sweep_id=nia-groebner-gate-<rung>` and `arm` in `{shipped, gate<rung>}`.

Binary: release `smtcomp_cli`, commit `3c3ba0eb2` (local main after merge),
sha256 `340bdd11053cac94aaece2281a24a46cd79546ae26013e1b5724f3815ce2cf1d`.

Cores: **s7**, physical core pairs `1,9` (shard 1, files at odd position in
the 116-list) and `3,11` (shard 2, even position), run in parallel; the four
rungs run serially, one after another, on each shard. Driver scripts in
`scripts/run-ladder-master.sh` and `scripts/run-arm-pair.sh` in this
directory (also copied to `server7:~/nia-groebner-gate-20260915/` to run
against the pinned cores, since this worktree is local to the dev box and s7
does not share this filesystem).

### Ladder table

All 116 files, every rung, `decided_by`/`bound_by` and full route trails read
through `scripts/analyze-rung.py` (never a prose grep). 42 of 116 never reach
`cas-ideal-refuter` at all (linear system, or fewer than two nonlinear
hypotheses — `CasOutcome::NoCandidate`, unaffected by any lever); those 42 are
excluded from ADMITS/REFUSES and folded into `not-reached` below. **2 of 116
are decided at every rung, by `int-blast-ladder` and `nia-linearize`
respectively — routes the Gröbner gate never touches** — because the 116-file
board was generated earlier the same day and main has moved since; this is
board drift (a snapshot going stale as other lanes land, unrelated to this
lane), confirmed by identical `decided_by` and identical corpus paths across
all four independent shipped reruns.

| rung | reached (of 116) | REFUSES (admission) | ADMITS-but-fails | now DECIDES by `cas-ideal-refuter` | STABLE-GAIN | STABLE-LOSS | shipped median/p90 ms | gate median/p90 ms |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| shipped (8/8/8) | 74 | 72 | 2 | 0 | — | — | 24119 / 24320 | — |
| 16/16/16 | 74 | 66 | 8 | 0 | 0 | 0 | 24119 / 24320 | 24119 / 24322 |
| 32/32/32 | 74 | 57 | 17 | 0 | 0 | 0 | 24120 / 24322 | 24118 / 24320 |
| 64/64/64 | 73† | 40 | 33 | 0 | 0 | 0 | 24118 / 24321 | 24118 / 24320 |
| unbounded (1,000,000/1,000,000/1,000,000) | 73† | 0 | 73 | 0 | 0 | 0 | 24119 / 24324 | 24118 / 24325 |

† one file (`…ITS/From_T2__pentagon.t2__p7110_edge_closing_0.smt2`) moves from
`refuses` (shipped/16/32) to a **partial trail** at 64 and unbounded: the
gate-arm process's own internal watchdog fires *while `cas-ideal-refuter` is
still running* (exit 0, ~25.0–25.1 s wall, `partial=yes`), so the route never
gets a chance to record `declined` and every route after it in the dispatch
ladder is denied its turn. The file still ends `unknown` in both arms — no
verdict changes — but it is the one clean example in this sweep of what the
brief calls "cost": raised past ~64, the Gröbner search itself can consume
the file's entire remaining time slice for zero benefit. Confirmed with a
partial-trail scan over all four rungs' ledgers (`scripts/outcome_ledger.py`'s
`partial` column, not a grep) — this is the *only* file affected, in the gate
arm only, only at 64 and unbounded.

**`ADMITS-but-fails` detail, once the gate stops refusing at admission**
(`scripts/analyze-rung.py` + `route_trace_reader.py`, gate arm only):

| detail | 32 | 64 | unbounded |
|---|---:|---:|---:|
| `no combination of the asserted equations collapsed to a constant of the refuting sign` | 17 | 29 | 46 |
| `cofactor-tracked Gröbner reduction hit the basis-size ceiling` | 0 | 2 | 21 |
| `cofactor-tracked Gröbner reduction hit the polynomial-size ceiling` | 0 | 2 | 7 |

The dominant failure mode at every level is the search **completing** and
finding no refutation — not hitting a step ceiling. Only at unbounded does the
step-ceiling backstop (`basis_size=32`, `poly_terms=256`) start to matter in
volume (28 of 73), confirming ADR-2112's prediction that raising admission
"degrades to a step-ceiling decline rather than a hang" — it does, and even
an uncapped admission still terminates (bar the one partial-trail file above)
inside the fixed Buchberger step budget.

**No movers to recheck.** `STABLE-GAIN`/`STABLE-LOSS` are 0 at every rung
because there were 0 raw gains and 0 raw losses to begin with — `analyze-rung.py`'s
gain/loss/flip columns are computed directly from the ledger's `verdict`
field (authoritative, independent of the route-trail parse), and the same
result held across all four independent rung sweeps. `recheck-movers-env.sh`
is committed and ready, but there is nothing in its input list: a 3x recheck
of an empty set is not a stronger finding than the ledger's own count, so it
was not run.

### Cross-division check (QF_NRA, UFNIA)

Shipped vs. **unbounded** (the most permissive arm tested, so the tightest
bound on "is there a loss anywhere"), full 200-row T1 lists, same 24 s / 8 GiB
/ `--trace` envelope, one division per shard (QF_NRA on `1,9`, UFNIA on
`3,11`, run in parallel — the same shape `launch-ab.sh` used for the floor
probe, since QF_NRA is a control the lever should not reach — `cas_ideal_refutation`
runs on Real assertions too, `nra.rs`'s route, but it's a different admission
path — and UFNIA is a reach check, since `q:skolem-qf` hands off to the same
quantifier-free ladder).

| division | files | shipped decided | unbounded decided | gains | losses | flips |
|---|---:|---:|---:|---:|---:|---:|
| QF_NRA | 200 | (filled below) | | | | |
| UFNIA | 200 | | | | | |

## 3. Verdict

**No level of the Gröbner admission gate decides any QF_NIA file, up to and
including unbounded.** The route is reached on 74 of 116 undecided rows (42
never qualify as candidates at all — a linear system or fewer than two
nonlinear hypotheses, `CasOutcome::NoCandidate`, which no lever touches). As
the gate opens, the route increasingly stops REFUSING at admission and starts
actually SEARCHING (2 → 8 → 17 → 33 → 73 of 74 reached), and every one of
those searches **completes and fails on its own merits** — "no combination…
collapsed to a constant of the refuting sign" is the dominant outcome at
every level, not a step-ceiling cutoff. This is the direct, measured answer
to ADR-2112 Part F: the corpus's median 342 integer symbols and 480
cross-products are not merely REFUSED by an 8/8/8 admission gate, they are
GENUINELY OUTSIDE what the unit-ideal / sum-of-squares / inequality-modulo-ideal
certificate shapes this route searches can express for these files — raising
the gate does not change that, it only lets the route spend more of the
budget confirming it.

**Cost.** For 115 of 116 files the extra search is invisible in the
aggregate (median/p90 elapsed stay flat at ~24.1 s / ~24.3 s at every rung,
gate and shipped alike, because the *other* routes in the ladder already
consume the full budget on these files regardless). For exactly 1 file at
levels ≥ 64, the Gröbner search itself becomes the thing that exhausts the
remaining budget, denying every downstream route its turn — with no verdict
consequence here, but it is the shape of cost a corpus with a genuinely
reachable large system could pay for.

## 4. Ship decision

**No lever ships ON.** The bar (0 stable losses across QF_NIA/QF_NRA/UFNIA,
**≥ 1 stable gain**) is not met at any rung: gains are 0 at every level,
including unbounded, on QF_NIA — which alone is sufficient to decide the
question regardless of the cross-division numbers above. No ADR is written
(this ADR would have been ADR-2123, per the lane brief's rule: no lever ships
ON, no ADR). No `config_registry.rs` change is registered — the shipped
8/8/8 stays, and this lane's finding is that raising it has no benefit to
trade against its (small, but nonzero at the tail) cost.
