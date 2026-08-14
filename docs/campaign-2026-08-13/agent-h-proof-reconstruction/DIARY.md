# agent-h DIARY — streaming resolution reconstruction

Append-only. Includes what broke.

Lane: `crates/axeyum-solver/src/reconstruct/` (owned). Build snapshot:
`~/.cache/axeyum-agent-h` from `git archive HEAD` at
`f19282dc442b479bfbf8d8e8305626f6314234ae`. **Not `/tmp`** (campaign rule 7).

---

## 2026-08-13 — orientation, and the first correction to the brief

Read `README.md`, `NEXT-MATH-STACK.md` item 1, `CLAUDE.md`, and agent-g's
`DIARY.md` (whose subject is `axeyum-cnf` parse/plan residency — disjoint from
mine, which is the Lean expression arena).

Read `resolution.rs` end to end (2151 lines). **The brief's framing needs one
correction before any work is done, and it is load-bearing:**

`DP_POOL_BUDGET` (`resolution.rs:426`, value **4096**) guards
`reconstruct_resolution_step_dp` — which is the *third* fallback, not the main
path. `reconstruct_resolution_step` (line 428) tries, in order:

1. `reconstruct_ordered_rup_step` (line 467) — replays LRAT's exact hint order.
   Linear in hint count. **This is what our own proofs take.**
2. `reconstruct_rup_closure_step` (line 1091) — deterministic unit closure when
   Alethe polarity normalization has disturbed the hint order.
3. `reconstruct_resolution_step_dp` (line 1241) — full Davis-Putnam, the only
   place `DP_POOL_BUDGET` exists.

So a proof produced by our own `solve_with_drat_proof` ->
`elaborate_drat_to_lrat` -> `lrat_to_alethe` pipeline never touches DP. Naming
`DP_POOL_BUDGET` as "the ceiling" would have sent this lane at a guard that our
own refutations do not reach. Measure first.

## 2026-08-13 — H1 probe written

`crates/axeyum-solver/examples/reconstruct_ceiling_probe.rs` (snapshot only for
now). DIMACS -> `solve_with_drat_proof` -> `elaborate_drat_to_lrat_backward` ->
`lrat_to_alethe` -> `reconstruct_resolution_proof`, reporting per stage: step
counts, hint counts, **kernel expression-arena length**, RSS, VmHWM, wall time.

Arena length is read by allocating one never-seen `BVar(u32::MAX - tag)` and
reading `ExprId::index()` — ids are dense and assigned in insertion order, so
that index *is* the arena length at the call. `Kernel` exposes no count; I did
not add one because `axeyum-lean-kernel` is off-limits this session.

## 2026-08-13 — first curve points

| instance | res steps | LRAT hints | arena nodes | RSS delta | recon s |
|---|---:|---:|---:|---:|---:|
| `rado-r3-a2-b1/F_14` | 5 | 85 | 16,443 | 2.0 MB | 0.022 |
| `rado-r3-a3-b1/F_27` | 29 | 536 | 139,601 | 13.4 MB | 0.099 |
| `rado-r3-a3-b2/F_31` | 38 | 1,000 | 294,738 | 26.3 MB | 0.337 |

Two numbers fall straight out:

- **~90-130 bytes of RSS per interned expression node** (`ExprNode` +
  `ExprMeta` + the intern table entry). At `F_31` it is 91 B/node.
- **~190-300 expression nodes per LRAT hint**, and *rising* with instance size
  (193 -> 260 -> 295). Not a constant. That is the shape that decides whether
  this is (a), (b) or (c) in the brief.

`DP_POOL_BUDGET` was not reached on any of these. The arena is the cost.

## 2026-08-13 — the ceiling is not `DP_POOL_BUDGET`, and here is the proof

`rado-r4-a1-b1/F_45` (180 vars, 4,408 clauses), through the shipped inlined
route: 336,432 DRAT steps, 150,594 LRAT additions, **4,572,930 hints**,
159,406 Alethe commands. `reconstruct_resolution_proof` ran for **6+ minutes**
at 2.2 GB and climbing, with no error and no Davis-Putnam involvement at all —
memory growth of ~6 MB/s against a proof that needs, on the measured curve,
~1.6e9 expression nodes at ~90 B each, i.e. **~140 GB**.

That is answer **(c)** from the brief, sharpened:

- The budget at `resolution.rs:426` is a guard on a **fallback that our own
  proofs never reach**. LRAT hint chains go through `reconstruct_ordered_rup_step`
  (`resolution.rs:467`); the Davis-Putnam pool (`resolution.rs:1241`) is the third
  choice, for general Alethe input that is not an ordered RUP chain. Nothing in
  the ladder above triggered it.
- The reconstruction is algorithmically fine. What is bounded is its
  **materialisation**: the kernel expression arena, which grows monotonically
  and is never released, at ~90-100 bytes per interned node.

## 2026-08-13 — the three things the inlined route does not do

Reading `bitblast.rs:1500-1680`, the `QF_BV` route already has the machinery the
clausal front door lacks. Concretely `reconstruct_resolution_proof`:

1. reconstructs **every** command, including learned clauses that never reach
   the empty clause (`reconstruct_bitwise_cps_tail` slices backwards; the
   clausal front door does not);
2. keeps clauses in the right-nested `Or` encoding and folds a RUP chain as `k`
   materialised binary resolvents, each an `Or.rec` elimination over both parents
   with `Or.inl`/`Or.inr` injection paths per survivor — where
   `construct_cps_rup_from_trace` builds the whole chain once, linear in the sum
   of reason widths;
3. inlines, where `ctx.closed_aliases.cps_clauses` already exists and admits each
   clause as a closed `Declaration::Theorem`.

None of that is new code. It is wiring that was built for the bit-blast lane and
never reached the SAT lane.

## 2026-08-13 — H2 landed: `reconstruct_resolution_proof_compact`

`resolution.rs`, new. Backward slice + CPS + one `Declaration::Theorem` per live
clause. **The per-step gate got stronger, not weaker**: `check_against` is
deferred, but `add_declaration` type-checks every clause alias against its stated
CPS proposition, so a wrong resolvent is rejected at the step that built it. The
closing `check_false_prop` runs with deferral explicitly turned back off.

## 2026-08-13 — the differential, and what it actually checks

`reconstruct_differential_probe.rs`. "Same statement" is nearly vacuous here —
both routes end at `False`. The statement that can silently shrink is *what
`False` is proved from*. So the harness decodes every `assume`-role hypothesis
axiom back out of its `Prop` encoding into a clause of `+-v<k>` keys
(`declared_assumption_clauses`, new in `resolution.rs`) and checks:

- **no alien axioms**: every hypothesis axiom is an actual clause of the input
  CNF (this is the check that catches a `False` proved from something that is not
  the problem);
- **subset**: compact's footprint is contained in inlined's — slicing may drop an
  unused input clause, it may never invent one;
- **nonempty**: a `False` from zero hypotheses is a bug, not a triumph.

An axiom whose type does not decode is reported as `<undecodable>`, never
skipped.

| instance | hints | inlined arena | compact arena | arena | inlined s | compact s | time | verdict |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| `r3-a2-b1/F_14` | 85 | 16,443 | 13,262 | 1.24x | 0.018 | 0.006 | 2.8x | SUBSET-OK |
| `r3-a3-b1/F_27` | 536 | 139,601 | 52,688 | 2.65x | 0.279 | 0.040 | 7.0x | SUBSET-OK |
| `r3-a3-b2/F_31` | 1,000 | 294,738 | 84,581 | 3.48x | 0.429 | 0.065 | 6.6x | SUBSET-OK |
| `r3-a1-b2/F_43` | 1,230 | 380,162 | 97,828 | 3.89x | 0.541 | 0.041 | 13.1x | SUBSET-OK |
| `r3-a2-b3/F_61` | 4,974 | 1,883,315 | 354,832 | 5.31x | 8.024 | 0.193 | 41.5x | SUBSET-OK |

**Zero alien axioms on either route, at every size.** Zero statement mismatches.
The ratios grow with instance size, which is the point: this is not a constant
factor, it is a change of slope.

The footprint shrinks a lot (`F_61`: 2,135 hypothesis axioms -> 413) because
backward slicing drops input clauses the refutation never consumes. That is a
**stronger** theorem — `False` from 413 of the 2,135 clauses — and it is exactly
the direction the audit has to distinguish from the dangerous one, which is why
the check is directional (subset), not equality.

## 2026-08-13 — H3: official Lean checks the refutations, with an empty "other" axiom list

`reconstruct_lean_certificate.rs`: compact route ->
`Kernel::write_lean_module_compact_with_inductives` **streamed to a file** (the
module is never one `String` in memory) -> `lean` v4.30.0.

Two things mattered for the axiom footprint:

- Passing `False` and `Or` as **real inductives** rather than letting them render
  as `axiom`s. With that, Lean regenerates `False.rec`/`Or.rec` *with their iota
  rules* — it checks the eliminations rather than being told them. The first run
  (default rendering) listed `False, Or, False.rec, Or.inl, Or.inr, Or.rec` as
  axioms; with real inductives that list is **empty**.
- `em` is declared but never consumed. The CPS/RUP construction is constructive
  (it case-splits on a premise it already holds), so `em` does not appear in
  `#print axioms` at any size.

Result at every size checked: `#print axioms axeyum_refutation` lists **only**
the input-clause hypotheses and the propositional atoms. No `propext`, no
`Classical.choice`, no `Quot.sound`, no `em`, no prelude connective.

## 2026-08-13 — what broke, and one thing that lied

**Broke:** `rustfmt --edition 2024 crates/axeyum-solver/src/reconstruct.rs` —
the single-file command `CLAUDE.md` prescribes for multi-agent hygiene — followed
the `mod` declarations and rewrote **five sibling modules I do not own**
(`arithmetic.rs`, `bitblast.rs`, `cnf.rs`, `direct.rs`, `quantifier.rs`) plus ~40
unrelated lines of `reconstruct.rs` itself. Caught it at the patch-review step
and reverted `reconstruct.rs` to HEAD plus a single three-line export edit; the
five siblings were never patched into the live tree.

**Lied:** chasing that, I found `cargo fmt --all --check` — the CI gate — does
not read those files at all. `mod reconstruct;` is at `lib.rs:183`, inside the
body of `macro_rules! full_modules` (`lib.rs:56`), and rustfmt does not expand
macros. Appending
`fn __fmt_probe(  ) ->    usize {   let    x=1  ;  x  }` to `resolution.rs` and
running `cargo fmt -p axeyum-solver -- --check` exits **0 with no output**.
**156 modules, 221,445 lines** of `axeyum-solver` — including the entire trusted
Lean reconstruction layer — are outside the formatting gate. Written up as F-H1.

## 2026-08-13 — the r4 ladder, and where Lean itself becomes the ceiling

`rado-r4-a2-b1/F_56` = `R_4(2(x-y)=z) = 56`, on s5: 1,674 DRAT steps, **53,402
LRAT hints**, reconstructed in **4.7 s** at 268 MB, rendered to a 20.7 MB Lean
module in 7.4 s. Footprint 1,171 assumption axioms, **0 alien**.

`lean` v4.30.0 accepted it in **40.7 s at 3.85 GB** — 1,337 axioms, of which
1,171 are input clauses and 166 are propositional atoms, and nothing else.

Note the ratio: our reconstruction peaked at 268 MB; **Lean needed 3.85 GB for
the same proof**, about 190x the module's own size. Past `n = 56` on `r4`, the
external checker, not axeyum, is the binding constraint.

## 2026-08-13 — the slice buys nothing on resolution work, and I had assumed it would

`h_slice_probe` (scratch, not committed) measures live hints / all hints over the
Alethe DAG. On every instance measured — `F_141`, `F_180`, `r4 F_56`, `r4 F_45` —
the answer is **1.0000**. `elaborate_drat_to_lrat_backward` already emits a fully
core proof; every resolution step reaches the empty clause.

What the backward slice *does* remove is unused **input clauses**: `F_141` 7,808
assumptions to 620, `F_45` 4,408 to 2,106. That is a smaller hypothesis
footprint, a smaller Lean module, and a stronger theorem — but zero resolution
work.

So the 5.6x / 55x belongs to **CPS + theorem aliasing**, not slicing. I had
assumed the opposite going in and would have written it that way if I had not
measured it. Corrected in `RESULT.md`.

## 2026-08-13 — tamper controls on an emitted certificate

Three edits to `rado-r3-a2-b1_F_14.lean`, each leaving a well-formed module, all
run through `lean` v4.30.0:

| tamper | what changed | Lean |
|---|---|---|
| weaken | one hypothesis clause loses a literal | **rejected** (application type mismatch at `hyp._4`) |
| relabel | one hypothesis names a different atom | **rejected** |
| reorder | one hypothesis's literals are permuted | **rejected** |
| control | untouched | accepted, axiom list as reported |

The certificate is not merely *accepted*; it is tied to the exact clause set it
claims. Note the third case: a permuted clause is *logically equivalent* and is
still rejected, because the proof injects through a fixed `Or.inl`/`Or.inr`
position — so acceptance is sensitive to the clause's syntactic form, not just
its truth.

**What these controls do NOT establish**, and it should be said: a third party
reading only the `.lean` file sees opaque `prop._N` and `hyp._M` names. Nothing
in the module ties them to variables and clauses of the source DIMACS. The Rust
side checks that (`alien 0` in every run) but the artefact does not carry it.
Added to F-H5.

## 2026-08-13 — the r4 frontier, and where I stopped

`rado-r4-a1-b1/F_45`: 4,572,930 hints, slice fraction 1.0. Inlined aborted after
25 min at 3.6 GB; compact aborted after 19 min at 3.5 GB. On the measured slope
that instance needs ~34 GB compact (~150 GB inlined) and it is not a constant
factor away from feasible — it needs the arena release path (F-H4).

`rado-r4-a3-b1/F_81` on s5 (24 GB ulimit): still climbing at 3.5 GB after 11 min
when I wrote this up. Recorded as unfinished rather than guessed at.

## 2026-08-13 — an accidental determinism check, and it passes

`rado-r4-a2-b1/F_56` and `rado-r4-a4-b2/F_56` are the same CNF
(md5 `a07b41b7...` both — `4(x-y)=2z` and `2(x-y)=z` have the same solution set).
I ran them on **different hosts** without noticing, s5 and s0, and got
byte-identical 20,656,289-byte Lean modules, md5
`9c2da811d51c6e012c9affc2e83621be`. Determinism is a public API promise; the
compact route keeps it across machines, not just across runs.

## 2026-08-13 — final state of the two unfinished runs

Recorded rather than guessed:

| run | host | cap | last observed | result |
|---|---|---|---|---|
| `r4-a1-b1/F_45` inlined | s0 | none | 4.1 GB @ 35 min | no result |
| `r4-a1-b1/F_45` compact | s0 | 20 GB | 15.4 GB @ 29 min | no result |
| `r4-a3-b1/F_81` compact | s5 | 24 GB | 12.4 GB @ 17 min (plateaued) | no result |

Left running under their own `timeout`s. 5.6x applied to a 34 GB requirement is
still 34 GB — this class needs F-H4, not another constant factor.

## 2026-08-13 — `F_45` finished, and it changes the frontier arithmetic

I had written `r4-a1-b1/F_45` up as unfinished. It then completed, compactly:

```
compact  ok true  arena 346,478,195  rss_kb 25,841,560  s 1945.993  assumes 2106  False
audit    compact_alien_axioms 0  compact_footprint 1802  source_clauses 2472
hwm_kb   26,469,984
```

**`R_4(x-y=z) = 45`: 150,594 resolution steps, 4,572,930 LRAT hints,
346,478,195 kernel expression nodes, 24.6 GB, 32.4 minutes, closing to a `False`
the trusted in-tree kernel accepts.** 86x more hints than anything reconstructed
before this session. The inlined route on the same instance was still climbing at
4.3 GB after 40 minutes with no result.

At this scale the constants come out slightly *better* than the small-instance
curve predicted: **75.8 nodes/hint** (predicted ~80) and **76.4 B/node**
(predicted 90-100). My 34 GB estimate was conservative by 38%. Worth noting
because the error was in the safe direction and I would have reported the
estimate as the answer if the run had not landed.

**Not externally Lean-checked.** Rendering this would be ~1.5 GB of Lean source
and Lean needs ~190x a module's size (measured: 3.85 GB for 20.7 MB). The largest
*externally* checked certificate stays `r4-a2-b1/F_56` at 53,402 hints.

Then the arithmetic that actually matters, which I nearly got wrong: the 741
cover's 699,572,027 steps are **across 6,241 cubes** — ~112,092 steps per cube,
i.e. *smaller* than `F_45`'s 336,432 DRAT steps. A single cube of the open claim
is within what just ran, not beyond it. Caveat recorded in `RESULT.md`: I do not
know the two counts measure the same thing, and one real cube should be measured
before anyone plans on it.

Also stopped a queued duplicate: `rado-r4-a2-b2/F_45.cnf` and
`rado-r4-a3-b3/F_45.cnf` are byte-identical to `rado-r4-a1-b1/F_45.cnf`
(md5 `d564fdc785dfc380d92f83558a2239e2` for all three), so the next 32-minute,
25 GB run would have produced no new information on a shared host.

## 2026-08-13 — `F_81` is rendering, which is itself a measurement

`rado-r4-a3-b1/F_81` (`R_4(3(x-y)=z) = 81`, the instance the brief names) on s5:
RSS **plateaued at 11.9 GB while `%CPU` stayed at 100** for eight minutes, which
looked like a hang. It is not — `~/agent-h/F_81.lean` was growing on disk. The
reconstruction had finished and
`write_lean_module_compact_with_inductives` was streaming the module out.

That flat-RSS-while-writing signature is the streaming render doing exactly what
it claims: the output side is already disk-bounded. Only the working arena is
not (F-H4). Worth recording because "plateaued memory at full CPU" reads as a
hang and I nearly logged it as one.

## 2026-08-14 — the render is the *next* wall, measured at 160 KB/s

`F_81`'s reconstruction had finished (that is what the growing `.lean` proved),
but the module was streaming out at a measured **160,366 B/s** — 10.5 MB to
20.1 MB over exactly 60 s. For an arena the size of `F_45`'s (346M nodes,
~5 B/node in rendered source) that is ~1.7 GB of Lean at ~3 hours of rendering,
which would have run past the job's 7200 s timeout.

So I killed it and re-ran `F_81` through `reconstruct_differential_probe
--compact-only`, which reconstructs and audits but does not render. Better
science: exact arena/time/footprint numbers instead of a certificate that is not
externally checkable at this size anyway (a 1.7 GB module needs ~320 GB in Lean
at the measured 190x).

That re-run also produced the shape of `F_81` for the first time, which the
certificate binary only prints at the *end*: **69,530 resolution steps,
2,163,930 hints** — about half of `F_45`. My example prints its summary after
rendering, which is the wrong order for a long job; noted for whoever picks
these probes up.

Also cleaned up after myself on s5: the queued `F_103` certificate run was killed
(it would have contended for a 27 GB box against the `F_81` re-run), and the
partial `F_81.lean` / `F_103.lean` spools were removed.

## 2026-08-14 — inlined `F_45`: 60 minutes, no result

The inlined run on `rado-r4-a1-b1/F_45` was killed at **60 minutes**, still
climbing, at **6.6 GB**. The compact route finished the same instance in 32.4
minutes at 24.6 GB. So in twice the compact route's total runtime the inlined
route had not reached a quarter of the compact route's final memory — the gap is
not a factor you can wait out.

## 2026-08-14 — `F_81` landed, and the model is now measured on two points

```
F_81.cnf  input    clauses 8044  res_steps 69,530  hints 2,163,930
F_81.cnf  compact  ok true  arena 155,231,696  rss_kb 12,135,500  s 974.701  False
F_81.cnf  audit    compact_alien_axioms 0  compact_footprint 4244  source_clauses 7992
F_81.cnf  hwm_kb   12,440,276
```

**`R_4(3(x-y)=z) = 81`** — the instance the brief names — reconstructed to a
kernel-checked `False` in **16.2 minutes at 11.6 GB**, 0 alien axioms.

The point of having two large instances rather than one is the slope:

| instance | hints | nodes | nodes/hint | B/node | minutes |
|---|---:|---:|---:|---:|---:|
| `r4-a3-b1/F_81` | 2,163,930 | 155,231,696 | 71.7 | 80.1 | 16.2 |
| `r4-a1-b1/F_45` | 4,572,930 | 346,478,195 | 75.8 | 76.4 | 32.4 |

`F_45` has **2.11x** the hints and cost **2.23x** the nodes, **2.13x** the
memory, **2.00x** the time. Linear, to within 6%. Everything I said about cube
scale for the 741 cover rests on that linearity, and it is now two measured
points a factor of two apart instead of an extrapolation off small instances.

Every r4 instance attempted this session is now complete. Nothing is left
pending.
