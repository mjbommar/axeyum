# agent-h RESULT — streaming resolution reconstruction

Lane: `crates/axeyum-solver/src/reconstruct/`.
Landed as `1b2b13c701f66b17e8bd02f33e8fad2fbb6bef1f` (`Agent: agent-h`).
Raw output in `logs/`; Lean certificates in `artifacts/lean-certs/`.

---

## Headline

1. **The documented ceiling was not the ceiling.** `DP_POOL_BUDGET` guards a
   Davis-Putnam fallback our own proofs never enter. Across 22 Rado instances
   (all 22 completed) spanning 85 to 4,572,930 LRAT hints it was
   **never reached**. The real bound is the kernel expression arena.
2. **The ceiling moved by ~5.6x in space and ~55x in time**, and the ratio is
   still rising at the top of the measured range —
   `reconstruct_resolution_proof_compact`.
   Concretely, **two 4-colour instances that did not reconstruct before now do**:
   `R_4(3(x-y)=z) = 81` (2,163,930 hints, 11.6 GB, 16.2 min) and
   `R_4(x-y=z) = 45` (4,572,930 hints, 346,478,195 kernel expression nodes,
   24.6 GB, 32.4 min), each closing to a `False` the trusted kernel accepts.
   `F_45` is **86x more hints than anything reconstructed before this session**;
   the inlined route was killed on it at 60 minutes with no result. Cost is
   **linear in hint count** across the two, to within 6%.
3. **The differential found no statement mismatch.** Zero alien hypothesis
   axioms on either route at every size, `F_45` included; the compact footprint
   is a strict subset of the inlined one at every size.
4. **19 distinct refutation certificates are now checked by official Lean
   v4.30.0** (covering 20 ledger instances — `r4-a2-b1/F_56` and `r4-a4-b2/F_56`
   are the same CNF, md5 `a07b41b7...` both), up to `R_3(x-y=5z) = 286` and
   `R_4(2(x-y)=z) = 56` (53,402 hints), with
   `#print axioms` listing **only the input clauses and the propositional
   atoms** — no `propext`, no `Classical.choice`, no `Quot.sound`, no `em`.

---

## H1 — where the ceiling was

### The correction that had to come first

`reconstruct_resolution_step` tries three routes in order. Line numbers are given
**before** this session's change (`f19282dc`, the state the brief describes) and
**after** (`1b2b13c70`):

| # | route | before | after | when |
|---|---|---:|---:|---|
| 1 | `reconstruct_ordered_rup_step` | 467 | 785 | LRAT hint order replays exactly — **our own proofs** |
| 2 | `reconstruct_rup_closure_step` | 1091 | 1385 | polarity normalization disturbed the order |
| 3 | `reconstruct_resolution_step_dp` | 1241 | 1535 | general Alethe; **the only user of `DP_POOL_BUDGET`** |

`reconstruct_resolution_step` itself: 428 -> 746. `DP_POOL_BUDGET = 4096`:
426 -> 744. The new route `reconstruct_resolution_proof_compact` is at 545 and
`declared_assumption_clauses` at 242. It did not fire once in this session. Anything built against it would have been built against a guard that
does not run.

### The curve (inlined route, committed Rado ledger)

Kernel expression-arena nodes read by allocating one never-seen `BVar` and
reading `ExprId::index()` — ids are dense and assigned in insertion order.

| instance | res steps | LRAT hints | arena nodes | RSS delta | recon s | nodes/hint |
|---|---:|---:|---:|---:|---:|---:|
| `r3-a2-b1/F_14` | 5 | 85 | 16,443 | 2.0 MB | 0.018 | 193 |
| `r3-a3-b1/F_27` | 29 | 536 | 139,601 | 13.4 MB | 0.279 | 260 |
| `r3-a3-b2/F_31` | 38 | 1,000 | 294,738 | 23.4 MB | 0.429 | 295 |
| `r3-a1-b2/F_43` | 56 | 1,230 | 380,162 | 29.4 MB | 0.541 | 309 |
| `r3-a4-b1/F_64` | 80 | 1,820 | 580,557 | 47.3 MB | 1.407 | 319 |
| `r3-a4-b3/F_73` | 120 | 3,374 | 1,344,035 | 100.3 MB | 6.614 | 398 |
| `r3-a1-b3/F_94` | 149 | 3,539 | 1,389,635 | 104.9 MB | 7.886 | 393 |
| `r3-a2-b3/F_61` | 237 | 4,974 | 1,883,315 | 171.8 MB | 8.024 | 379 |
| `r3-a5-b4/F_141` | 175 | 4,519 | 2,064,735 | 194.1 MB | 12.370 | 457 |
| `r4-a1-b1/F_45` | 150,594 | 4,572,930 | — | 6.6 GB and rising | **60 min, no result** | — |

Two constants fall out and hold across the whole range:

- **~90-100 bytes of RSS per interned expression node.** (`F_141`: 194.1 MB /
  2,064,735 = 94 B.)
- **~190-460 expression nodes per LRAT hint**, rising with clause width.

### Which of (a)/(b)/(c) is true

**(c), with a correction.** The reconstruction is algorithmically fine — it is
linear in the hint chain, and the DP fallback that could blow up is not on the
path. What is bounded is its **materialisation**: the `Kernel` arena
(`crates/axeyum-lean-kernel/src/lib.rs:247`) is three monotone `SegmentedVec`s
and nothing is ever released.

It is not (a): the budget is not conservative, it is *irrelevant*. It is not (b)
in the sense of a superlinear working set: RSS per node and nodes per hint are
both near-constant. The cost is simply that **the whole proof term must be
resident**, and the inlined route's encoding makes that term ~4-5x larger than it
needs to be.

Extrapolating the measured slope to `r4-a1-b1/F_45`: 4.57M hints x ~350 nodes x
~92 B is **~150 GB** inlined, and — since the slice removes no resolution work
there (see below) — **~34 GB** compact.

The compact figure was then **measured** rather than left as an extrapolation:
346,478,195 nodes at 24.6 GB, i.e. **75.8 nodes/hint and 76.4 B/node**. The
prediction was conservative by 38% — the per-node cost falls at scale (the
intern table amortises), which is the direction that helps. `R_4(5(x-y)=4z) = 741`'s 699,572,027 proof steps are four
orders of magnitude beyond that. No constant factor closes that gap; see
"where the ceiling is now" for what does.

---

## H2 — where the ceiling is now

`reconstruct_resolution_proof_compact` (`resolution.rs`), three changes:

1. **Backward slice** from the step deriving `(cl)`. On these proofs this removes
   only unused *input clauses* — see "attributing the win" below — but it removes
   a lot of them, and each one it drops is a hypothesis axiom the theorem no
   longer depends on.
2. **CPS clause encoding.** A RUP chain is built once from its validated
   unit-propagation trace (`construct_cps_rup_from_trace`) instead of folding `k`
   materialised binary resolvents through `Or.rec` with `Or.inl`/`Or.inr`
   injection paths per survivor.
3. **Global theorem aliases.** Each live clause is admitted as a closed
   `Declaration::Theorem`; downstream steps reference one `Const` node.

None of this is new machinery. All three already existed for the bit-blast lane
(`bitblast.rs:1505-1680`) and had never been wired to the clausal front door the
doc comment calls "the foundation shared by all clausal proofs (`QF_BV`, SAT)".

**The per-step soundness gate got stronger, not weaker.** `check_against` is
deferred, but `add_declaration` type-checks every clause alias against its stated
CPS proposition, so a wrong resolvent is rejected at the step that built it
rather than propagating. The closing `check_false_prop` runs with deferral
explicitly turned back off.

### Measured, inlined -> compact

| instance | hints | arena (in) | arena (out) | space | time (in) | time (out) | speed |
|---|---:|---:|---:|---:|---:|---:|---:|
| `r3-a2-b1/F_14` | 85 | 16,443 | 13,262 | 1.24x | 0.018 | 0.006 | 2.8x |
| `r3-a3-b1/F_27` | 536 | 139,601 | 52,688 | 2.65x | 0.279 | 0.040 | 7.0x |
| `r3-a3-b2/F_31` | 1,000 | 294,738 | 84,581 | 3.48x | 0.429 | 0.065 | 6.6x |
| `r3-a1-b2/F_43` | 1,230 | 380,162 | 97,828 | 3.89x | 0.541 | 0.041 | 13.1x |
| `r3-a4-b1/F_64` | 1,820 | 580,557 | 143,497 | 4.05x | 1.407 | 0.120 | 11.7x |
| `r3-a4-b3/F_73` | 3,374 | 1,344,035 | 253,866 | 5.29x | 6.614 | 0.144 | 46.1x |
| `r3-a1-b3/F_94` | 3,539 | 1,389,635 | 263,007 | 5.28x | 7.886 | 0.131 | 60.0x |
| `r3-a2-b3/F_61` | 4,974 | 1,883,315 | 354,832 | 5.31x | 8.024 | 0.193 | 41.5x |
| `r3-a5-b4/F_141` | 4,519 | 2,064,735 | 369,679 | 5.59x | 12.370 | 0.224 | 55.3x |

The ratios are still climbing at the top of the range — this is a change of
slope, not a constant factor. Compact settles near **~80 nodes/hint** against the
inlined route's 190-460.

### Attributing the win correctly

I expected the backward slice to be a large part of it. **It is not.** Measured
directly (`logs/slice-probe.log`, live hints / all hints):

| instance | LRAT additions | all hints | live hints | slice fraction |
|---|---:|---:|---:|---:|
| `r3-a5-b4/F_141` | 175 | 4,519 | 4,519 | **1.0000** |
| `r3-a4-b5/F_180` | 1,595 | 42,426 | 42,426 | **1.0000** |
| `r4-a2-b1/F_56` | 1,586 | 53,402 | 53,402 | **1.0000** |
| `r4-a1-b1/F_45` | 150,594 | 4,572,930 | 4,572,930 | **1.0000** |

`elaborate_drat_to_lrat_backward` already emits a fully core proof: **every**
resolution step reaches the empty clause. The slice removes exactly one thing —
**unused input clauses**, and a lot of them (`F_141`: 7,808 assumptions to 620;
`F_45`: 4,408 to 2,106). That shrinks the hypothesis footprint and the emitted
Lean module, and it makes the theorem stronger, but it removes **no** resolution
work.

So the 5.6x arena and 55x time are **CPS encoding plus theorem aliasing**, not
slicing. Stating this because the opposite attribution is the natural guess and
would send the next lane at proof trimming, which on these proofs has nothing
left to take.

Instances the inlined route was never run on because it would not finish, done
compactly:

| instance | hints | recon s | peak RSS |
|---|---:|---:|---:|
| `r3-a2-b5/F_181` | 21,423 | 2.71 | 145 MB |
| `r3-a3-b4/F_109` | 21,818 | 2.92 | 131 MB |
| `r3-a3-b5/F_186` | 31,884 | 6.53 | 227 MB |
| `r3-a4-b5/F_180` | 42,426 | 13.52 | 257 MB |
| `r4-a2-b1/F_56` | 53,402 | 4.72 | 269 MB |
| **`r4-a3-b1/F_81`** | **2,163,930** | **974.70** | **11.6 GB** (peak 11.9) |
| **`r4-a1-b1/F_45`** | **4,572,930** | **1,945.99** | **24.6 GB** (peak 25.2) |

`r4-a1-b1/F_45` is the headline of this section and deserves its own numbers:
**`R_4(1(x-y)=1z) = 45`**, 150,594 resolution steps, 4,572,930 LRAT hints,
**346,478,195 kernel expression nodes**, closing to a `False` that the trusted
in-tree kernel accepts. Every one of the 150,594 clause aliases was type-checked
by `add_declaration` against its stated CPS proposition on the way, and the
closing term was `infer`-checked against `False` with per-step deferral turned
off. Footprint audit: **0 alien axioms**, 1,802 of the 2,472 distinct source
clause keys.

The inlined route was run on the same instance concurrently and **did not
finish**: killed at **60 minutes**, still climbing, at 6.6 GB — i.e. it had not
even reached a quarter of the compact route's *final* footprint in twice the
compact route's *total* runtime.

This is **86x more hints than the largest refutation reconstructed before this
session** (`r4-a2-b1/F_56`, 53,402).

**`r4-a3-b1/F_81` — the instance the brief names — also reconstructed**, and it
is the cleanest confirmation that the model holds:
**`R_4(3(x-y)=z) = 81`**, 69,530 resolution steps, **2,163,930 LRAT hints**,
**155,231,696 kernel expression nodes**, **11.6 GB** (peak 11.9), **16.2
minutes**, `False`, **0 alien axioms**, footprint 4,244 of 7,992 distinct source
clause keys.

The two large instances agree on the constants to within 6%:

| instance | hints | nodes | nodes/hint | B/node | minutes |
|---|---:|---:|---:|---:|---:|
| `r4-a3-b1/F_81` | 2,163,930 | 155,231,696 | **71.7** | **80.1** | 16.2 |
| `r4-a1-b1/F_45` | 4,572,930 | 346,478,195 | **75.8** | **76.4** | 32.4 |

Both memory and time are **linear in hint count** at r4 scale — `F_45` has 2.11x
the hints of `F_81` and cost 2.23x the nodes, 2.13x the memory and 2.00x the
time. That is the property the cube-scale extrapolation below depends on, and it
is now measured on two points a factor of two apart rather than assumed.

**It is not externally Lean-checked, and that must be said plainly.** Rendering
this proof to a Lean module would produce roughly 1.7 GB of source — measured
render throughput is **160,366 B/s**, so about **three hours of writing** — and
Lean needs ~190x a module's size in RAM (measured: 3.85 GB for a 20.7 MB module),
i.e. **~320 GB** to check it. The external check is out of reach at this scale
today; what is established here is that **axeyum's own trusted kernel** accepts
the refutation, with all 150,594 clause aliases type-checked on the way. The
largest *externally* Lean-checked certificate remains `r4-a2-b1/F_56` at 53,402
hints.

### The differential — and it found no mismatch

"Same statement" is nearly vacuous when both routes end at `False`. The statement
that can silently shrink is *what `False` is proved from*: the hypotheses are
opaque `Axiom`s the reconstruction declared itself, so a mis-encoded clause would
still yield a perfectly well-typed `False` — from a formula that is not the
problem. `infer` cannot see that.

`declared_assumption_clauses` decodes each `assume`-role axiom back out of its
`Prop` encoding into `±atom` keys. An axiom whose type does not decode is
reported as `<undecodable>`, never skipped (unit-tested). The harness then
requires:

- **no alien axioms** — every hypothesis is an actual clause of the source CNF;
- **subset** — compact's footprint ⊆ inlined's;
- **nonempty** — a `False` from zero hypotheses is a bug, not a triumph.

Exact scope, because a count is easy to inflate:

- **Both routes, full differential: 9 instances** (`F_14` through `F_141`, the
  table above). Every one: `compact_alien_axioms 0`, `inlined_alien_axioms 0`,
  `compact_not_in_inlined 0`, verdict `SUBSET-OK`.
- **Compact route, alien-axiom audit only: 13 further instances**, including
  `r4-a3-b1/F_81` at 2.16M hints and `r4-a1-b1/F_45` at 4.57M — the ones the
  inlined route is too slow to run. Every one: `alien 0`.

**No statement mismatch was found, at any size, on either route.**

The footprints do differ, in the safe direction: at `F_61` the inlined route
assumes all 2,135 input clauses and the compact route assumes 413 of them. That
is a **stronger** theorem, which is exactly why the check is directional.

Seven unit tests landed with the route (`reconstruct/tests.rs`), including three
soundness-negative ones (pivot-free resolution, wrong resolvent, no empty clause)
that must be rejected *through the alias gate*, plus the subset differential and
the `<undecodable>` audit.

---

## H3 — Lean-checked certificates

`reconstruct_lean_certificate` streams the module to disk via
`Kernel::write_lean_module_compact_with_inductives` (never one `String`), with
`False` and `Or` passed as **real inductives** so official Lean regenerates
`False.rec`/`Or.rec` *with their iota rules* rather than being handed them as
axioms. Checked with `lean` v4.30.0.

| instance | statement | hints | recon s | module | lean s | lean RSS | `#print axioms` |
|---|---|---:|---:|---:|---:|---:|---|
| `r3-a2-b1/F_14` | `R_3(2(x-y)=z)=14` | 85 | 0.004 | 74 KB | 0.18 | 100 MB | 45 hyp + 34 atom |
| `r3-a3-b1/F_27` | `R_3(3(x-y)=z)=27` | 536 | 0.018 | 322 KB | 0.57 | 161 MB | 129 + 53 |
| `r3-a3-b2/F_31` | `R_3(3(x-y)=2z)=31` | 1,000 | 0.033 | 538 KB | 0.75 | 207 MB | 181 + 74 |
| `r3-a1-b2/F_43` | `R_3(x-y=2z)=43` | 1,230 | 0.039 | 633 KB | 0.87 | 228 MB | 185 + 77 |
| `r3-a2-b3/F_61` | `R_3(2(x-y)=3z)=61` | 4,974 | 0.253 | 2.3 MB | 4.98 | 566 MB | 413 + 114 |
| `r3-a4-b1/F_64` | `R_3(4(x-y)=z)=64` | 1,820 | 0.165 | 920 KB | 1.55 | 300 MB | 259 + 90 |
| `r3-a4-b3/F_73` | `R_3(4(x-y)=3z)=73` | 3,374 | 0.171 | 1.6 MB | 4.96 | 462 MB | 415 + 150 |
| `r3-a1-b3/F_94` | `R_3(x-y=3z)=94` | 3,539 | 0.150 | 1.7 MB | 2.21 | 477 MB | 400 + 146 |
| `r3-a3-b4/F_109` | `R_3(3(x-y)=4z)=109` | 21,818 | 2.917 | 9.0 MB | 22.24 | 1.83 GB | 1024 + 216 |
| `r3-a5-b1/F_125` | `R_3(5(x-y)=z)=125` | 3,697 | 0.297 | 1.7 MB | 3.30 | 466 MB | 390 + 141 |
| `r3-a5-b2/F_125` | `R_3(5(x-y)=2z)=125` | 6,033 | 0.461 | 2.8 MB | 4.91 | 715 MB | 625 + 182 |
| `r3-a5-b3/F_125` | `R_3(5(x-y)=3z)=125` | 9,302 | 0.734 | 4.2 MB | 9.72 | 965 MB | 797 + 227 |
| `r3-a5-b4/F_141` | `R_3(5(x-y)=4z)=141` | 4,519 | 0.319 | 2.3 MB | 3.63 | 620 MB | 620 + 195 |
| `r3-a1-b4/F_173` | `R_3(x-y=4z)=173` | 5,506 | 0.677 | 2.6 MB | 5.62 | 663 MB | 592 + 202 |
| `r3-a4-b5/F_180` | `R_3(4(x-y)=5z)=180` | 42,426 | 13.524 | 17.0 MB | 39.56 | 3.31 GB | 1453 + 291 |
| `r3-a2-b5/F_181` | `R_3(2(x-y)=5z)=181` | 21,423 | 2.706 | 8.9 MB | 16.62 | 1.86 GB | 1078 + 241 |
| `r3-a3-b5/F_186` | `R_3(3(x-y)=5z)=186` | 31,884 | 6.532 | 13.2 MB | 23.83 | 2.67 GB | 1386 + 309 |
| `r3-a1-b5/F_286` | `R_3(x-y=5z)=286` | 6,731 | 0.578 | 3.2 MB | 4.51 | 789 MB | 684 + 252 |
| **`r4-a2-b1/F_56`** | **`R_4(2(x-y)=z)=56`** | **53,402** | **4.72** | **20.7 MB** | **40.65** | **3.85 GB** | **1171 + 166** |
| `r4-a4-b2/F_56` | `R_4(4(x-y)=2z)=56` | 53,402 | 25.96 | 20.7 MB | 103.49 | 3.84 GB | 1171 + 166 |

(`r4-a4-b2/F_56` is the same CNF as `r4-a2-b1/F_56` — md5
`a07b41b72a2f193613fdabfb118861e1` for both — so it is a reproducibility check,
not an independent data point. Its slower times are contention: it ran on a
loaded s0 while the other ran on an idle s5.

**It is also a cross-machine determinism check, and it passes.** The two runs
were on different hosts and produced **byte-identical** 20,656,289-byte Lean
modules, md5 `9c2da811d51c6e012c9affc2e83621be`. Determinism is a public API
promise in `CLAUDE.md`; the compact route keeps it — the name counter is
monotone, command order is the input order, and every lookup structure is a
`BTree*`.)

The `#print axioms` column is complete: at every size the list contains **only**
the input-clause hypothesis axioms and the propositional atoms. Nothing else —
no `propext`, no `Classical.choice`, no `Quot.sound`, no `em`, no prelude
connective. `em` is *declared* (the classical commitment is made explicit) but
the CPS/RUP construction is constructive and never consumes it.

### Tamper controls

Acceptance alone is weak evidence. Three edits to
`artifacts/lean-certs/rado-r3-a2-b1_F_14.lean`, each leaving a well-formed
module, run through `lean` v4.30.0:

| tamper | what changed | Lean |
|---|---|---|
| weaken | one hypothesis clause loses a literal | **rejected** — application type mismatch at `hyp._4` |
| relabel | one hypothesis names a different atom | **rejected** |
| reorder | one hypothesis's literals permuted (logically equivalent!) | **rejected** |
| control | untouched | accepted; axiom list as reported |

The permutation case is the informative one: the certificate is sensitive to the
clause's syntactic form, not merely its truth, because the proof injects through
fixed `Or.inl`/`Or.inr` positions.

**What the controls do not establish.** A third party reading only the `.lean`
file sees opaque `prop._N` / `hyp._M` names; nothing in the module ties them to
variables and clauses of the source DIMACS. Lean's acceptance is evidence that
*some* clause set is unsatisfiable. The Rust-side audit closes that gap
(`alien 0` at every size) but the artefact does not carry it. See F-H5.

### The honest comparison with AB Support LLC

AB Support (Zenodo 10.5281/zenodo.20753303, 2026-06-18) claim a Lean certificate
of the unsatisfiability of the threshold instance for `R_4(x+y+z=2w) = 19`, with
axiom footprint `[propext, Classical.choice, Quot.sound]`.

Stating this precisely, because it is easy to overclaim:

- **Different equation family.** Theirs is `x+y+z=2w`; ours is `a(x-y)=bz`. These
  are not the same instances and the numbers are not directly comparable.
- **Comparable in scale, in our favour.** The published artefact is a single
  4-colour instance at `n = 19`. The largest here is a 4-colour instance at
  `n = 56` with 53,402 LRAT hints, plus eighteen 3-colour instances up to
  `n = 286`.
- **Strictly better footprint.** Their three axioms are the standard Lean
  classical trio. Ours is empty of all three, and of `em`. That is a real
  difference in what the certificate depends on, and it is checkable by anyone
  who runs `lean` on the files in `artifacts/lean-certs/`.
- **Not yet at open scale, but closer than it looks.** `R_4(5(x-y)=4z) = 741`
  closed with 699,572,027 proof steps over 6,241 cubes — **~112,092 per cube**,
  which is *smaller* than the 336,432-step `F_45` proof the compact route
  reconstructed this session. The honest claim is "kernel-checked refutations at
  cube scale, and externally Lean-checked refutations three orders of magnitude
  past the published one", not "the open problem is Lean-certified".

The `#print axioms` comparison is also **not yet apples-to-apples in the other
direction**: our modules are `prelude`-mode and re-declare their own logical
connectives, so Lean is checking the proof against axeyum's `False`/`Or` (as real
inductives it regenerates), not against Lean core's. That is a deliberate and
documented property of `render_lean_module`, and it should be said out loud
wherever the axiom count is quoted.

---

## What did not get done, and where I stopped

**`r4-a1-b1/F_45` did complete compactly** — after 32.4 minutes and 24.6 GB, see
above. The inlined route on the same instance was killed at **60 minutes**, still
climbing, at 6.6 GB, with no result.

**`r4-a3-b1/F_81` also completed** — 16.2 minutes, 11.6 GB, see above. My first
attempt at it went through `reconstruct_lean_certificate` and got stuck *writing*
the module (see the render wall below); re-running it without rendering gave the
numbers in 16 minutes.

**Nothing in the measured set is left unfinished.** What follows is what was not
attempted.

**What is still not done: the arena has no release path**, so proof size is
bounded by RAM, not by disk. The compact route makes each learned clause a closed
`Declaration::Theorem` whose body is finished and never referenced structurally
again — exactly the unit that could be spooled out and dropped. Doing it needs a
checkpoint/truncate API in `Kernel`, and `axeyum-lean-kernel` was off-limits this
session (unreachable codex CLI session holding uncommitted WIP there). Reported
as F-H4 with the shape it wants.

### What this means for the 741 cover, done carefully

`R_4(5(x-y)=4z) = 741` closed with **699,572,027 proof steps across 6,241
cubes**. The naive read — 153x `F_45`'s hint count, therefore hopeless — is the
wrong one, because the cover is *already decomposed*:

- **699,572,027 / 6,241 = 112,092 steps per cube on average.**
- `F_45`, which just reconstructed in 32 minutes at 24.6 GB, took **336,432 DRAT
  steps / 173,512 additions / 150,594 LRAT additions / 4,572,930 hints**.

So **the average cube of the 741 cover is roughly a third of the proof this
session reconstructed**, on the DRAT-step measure. A single cube of the open
frontier claim is now *within* what the compact route does, not beyond it.

Two honest caveats before anyone builds on that:

1. I do not know that the 699,572,027 figure counts the same thing as `F_45`'s
   336,432. If those are DRAT steps of similar character the per-cube cost is
   ~8 GB and ~10 minutes; if they are LRAT additions it is closer to `F_45`
   itself. **Measure one real cube before planning on either.**
2. A per-cube refutation is not a certificate of the theorem. It needs the cover
   to be shown exhaustive, and 6,241 kernel-checked cube refutations do not
   compose inside one arena today — which is F-H4 again, from the other
   direction.

Rough shape of the full job on the optimistic reading: 6,241 x ~10 min is ~43
single-core days, ~3 days on 16 cores, at ~8 GB per concurrent cube. That is a
schedulable computation rather than an impossible one. The linearity needed for
that estimate is now measured rather than assumed — `F_81` and `F_45` are a
factor of 2.1 apart in hints and 2.0-2.2x apart in nodes, memory and time.

Getting there still needs the arena release path, a cover-completeness argument,
and — for anything *externally* Lean-checked — a second answer to the ~190x wall
in Lean itself.

---

## Top three roadmap items

1. **Kernel arena checkpointing (F-H4).** Spool admitted
   `Declaration::Theorem`s to disk and truncate the arena behind them, keeping
   only their types in the environment. `write_lean_module_compact_with_inductives`
   already streams the *output*; only the working arena is unbounded. This is the
   single change that converts "bounded by RAM" into "bounded by disk", and the
   compact route was built so that this change is now a local one.

   The concrete target it unlocks: **one cube of the 741 cover**. On the measured
   `F_45` numbers a cube is ~8-25 GB and 10-32 minutes, i.e. schedulable — but
   6,241 of them do not compose in one arena today, and that is precisely what
   checkpointing fixes. Measure one real cube first (caveat in "What this means
   for the 741 cover").

2. **Make the assumption-footprint audit part of every certificate (F-H5).** A
   kernel-checked `False` says nothing about *what* was refuted. The decoder
   exists and costs nothing; wire it into the emitted evidence so a certificate
   carries "this `False`, from exactly these clauses of this CNF" rather than a
   bare axiom list. Then ship Lean certificates alongside the DRAT in
   `artifacts/claims/rado/*/` (F-H6) — every `r3` instance in the ledger can have
   one today, for seconds and a couple of MB gzipped.

3. **Close the formatting-gate hole (F-H1).** `cargo fmt --all --check` does not
   read 156 modules / 221,445 lines of `axeyum-solver`, including the entire
   trusted reconstruction layer, because `mod reconstruct;` lives inside a
   `macro_rules!` body. Reproduced with a deliberately malformed function and an
   exit-0 gate. This is the same failure shape as the corpus sweep that ran zero
   tests for 15 days, and the fix is the same: make the gate reconcile the file
   set it read against the file set on disk.
