# agent-g FEEDBACK — roadmap items from the DRAT memory lane

Every item cites file and line at commit `017eebe68`. Ordered by value per unit
of work, in my judgement. Measurements are in `RESULT.md`.

**Landed this lane:** `8e84b2358` (file-backed backward checking + typed resource
decline, 8.0x -> 2.4x resident) and `017eebe68` (32-bit plan, 2.4x -> **1.49x**),
with ADR-0426. The differential test between the two backward routes found **no
disagreement** on any input, including the four largest committed certificates
run through both routes in one process.

---

## G-1 (capability, HIGH) — `CnfFormula` costs 2.1x a flat arena, and 3.9x with a packed literal

**Measured**, `parse_dimacs` resident size, not estimated:

| formula | DIMACS | clauses | literals | resident | flat floor (8 B/lit) | headroom |
|---|---:|---:|---:|---:|---:|---:|
| `F_741` | 8.59 MB | 269,664 | 1,622,431 | 31.7 MB | 14.1 MB | 1.47x |
| `F_188` | 525.5 MB | 19,807,560 | 109,858,889 | **2.04 GB** | 958 MB | **2.13x** |

`CnfFormula` is `Vec<CnfClause>` of `Vec<CnfLit>`
(`crates/axeyum-cnf/src/lib.rs:181` and `:206`), so every clause costs a 24-byte
`Vec` header, a heap allocation with power-of-two capacity slack, and glibc's
16-byte chunk header — about 72 bytes for a 3-literal Schur clause that holds 24
bytes of literals.

**Correction to agent-a's FEEDBACK #6**, which reads "2.3 GB RSS for 330 MB of
literals — a 7x overhead from per-clause allocation". The 2.0-2.3 GB is right and
the diagnosis is right, but the factor is **2.13x**, not 7x: 109.9 M literals at
`size_of::<CnfLit>() == 8` are 879 MB on their own. The 330 MB figure looks like
DIMACS text, not literal storage. Sizing the fix against 7x would set the wrong
expectation and, worse, would make a correct fix look like a failure.

**Two independent changes, in this order:**

1. **Flat arena.** `lits: Vec<CnfLit>` plus `clause_ends: Vec<u32>`. Gets to the
   958 MB floor: **2.13x**.
2. **Packed `CnfLit`.** It is `{ CnfVar(u32), negated: bool }` = 8 bytes
   (`lib.rs:139`); as a single `u32` code `var << 1 | negated` it is 4. The
   derived `Ord` is *unchanged* by this — lexicographic `(var, negated)` and
   numeric order on `var << 1 | negated` agree — and every accessor (`var`,
   `is_negated`, `negated`, `dimacs`, `positive`) keeps its signature. Floor
   drops to 519 MB: **3.9x total.**

   This one is nearly free and helps *everywhere*, including the parsed DRAT
   step vector and the backward checker's arena. The only things to check are
   the two places inside `axeyum-cnf` that read the fields directly
   (`clause_fingerprint`, `lib.rs:4337`) and any test asserting on `Debug`
   output.

**Why I did not do it.** `.clauses()` has **113 call sites across four crates** —
77 in `axeyum-cnf` (mine), 15 in `axeyum-solver`, 13 in `axeyum-search`, 8 in
`axeyum-bench` — and `axeyum-search` is off-limits to this lane. `CnfClause`
appears 263 times. This is a one-owner refactor, not a multi-agent-night one.
Suggest doing (2) first: it is confined to `axeyum-cnf`, breaks nothing, and
banks half the win.

## G-2 (performance, HIGH for cube-and-conquer) — the backward checker rebuilds the formula's plan on every call

agent-b's FEEDBACK #2 reports "a large per-call fixed cost". I could not
reproduce that as a *per-call* constant and I can reproduce it as a
*per-formula* one, which changes the fix.

- Trivial proof, trivial formula: **0.41 us per call**, in-memory and
  file-backed alike, stable across 1,000 / 10,000 / 100,000 repetitions. There is
  no meaningful fixed constant.
- Same trivial proof against `F_741`'s 269,664 clauses: **165 ms per call**
  (down from 349 ms before `8e84b2358`).

The cause is `PlanBuilder::new`
(`crates/axeyum-cnf/src/drat_backward.rs`): every call pushes every formula
clause into the arena, computes its sorted literal-set key, hashes it and inserts
it into the deletion index. For a cover this is identical work repeated once per
cube.

For agent-b's **6,241-cube** cover of `R_4(5(x-y)=4z)`: **17.2 minutes of pure
plan construction** across the cover, all of it redundant.

**Fix.** Split the formula prefix out of `PlanBuilder` and let it be built once
and cloned per check — a `memcpy` of three vectors and a hash table instead of a
sort-and-hash per clause. Sketch:

```rust
pub struct BackwardPlanBase { /* the formula's arena, records, deletion index */ }
impl BackwardPlanBase {
    pub fn for_formula(formula: &CnfFormula) -> Self;
    pub fn check_reader<R: BufRead>(&self, reader: R) -> Result<bool, DratError>;
}
```

Expect roughly an order of magnitude on that term. It composes with the cover
harness without changing any verdict, and the existing differential test
generalises to it directly: the base-plus-clone plan must be byte-identical to
the from-scratch one, which is a cheap and total assertion.

## G-3 (memory, MEDIUM) — the deletion index is now the largest term, and it is a temporary

**Done and landed** was the `u32` narrowing (`017eebe68`): 2.4x -> **1.49x** on
`F_256`, with `ClauseRecord::start` deliberately left 64-bit. What remains,
measured on `PHP(8, 7)` from allocation capacities:

| term | bytes held | share |
|---|---:|---:|
| clause arena | 458,752 | 42% |
| clause records | 327,680 | 30% |
| **deletion index** | **236,544** | **22%** |
| step maps | 65,536 | 6% |

The deletion index (`HashMap<u64, RecordSlot>` in
`crates/axeyum-cnf/src/drat_backward.rs`) is a *temporary*: it exists only while
the plan is being built and is dropped by `PlanBuilder::finish`. It is
nevertheless resident at the construction peak, which for a large proof *is* the
peak.

Two cheap reductions:

- `RecordSlot` is 24 bytes because of its rare `Many(Vec<usize>)` arm. A
  `Many(u32, u32)` side-table arm would make it 8, taking the slot from 33 bytes
  to 17 — about a 10% cut in total held.
- The index could be dropped before `BackwardChecker::new` allocates its watch
  lists rather than at the same moment, so the two peaks do not overlap. Worth
  measuring before doing: glibc may or may not hand the pages back.

Neither is worth much on its own; both are worth listing because at 1.49x the
easy factors are gone and the next one has to come from somewhere specific.

## G-4 (defect, LOW) — the file-backed route pays for a proof with no refutation

`check_drat_backward` scans for the empty clause first and returns `Ok(false)`
immediately when there is none. `check_drat_backward_reader` cannot: it discovers
the absence only by reading to the end, and by then it has built the whole plan.
Measured on `F_741` with a one-step non-refutation: **0 ms vs 174 ms**.

This is inherent to reading a stream once and is the right trade for the normal
case (a proof that *is* a refutation), but it is a surprise worth a doc line, and
a caller feeding many non-refutations should use the in-memory route. Currently
undocumented.

## G-5 (measurement, MEDIUM) — the head of a DRAT proof is not representative

Relevant to anything that wants to size a job from a file it has not read.
Measured error in the estimated added-literal count from a head sample:

| sample | `F_81` | `F_103` | `F_171` | `F_256` |
|---:|---:|---:|---:|---:|
| 0.1% | +92% | +102% | +93% | +54% |
| 1% | +87% | +23% | +9% | +4% |
| 5% | +11% | +8% | +1% | -1% |
| 10% | +11% | +3% | 0% | 0% |

The *step* count is fine at any sample size (within 11%); it is the mean clause
width that drifts, because a proof's early lemmas are wider than its later ones.
The bias is toward over-estimating, which is the safe direction for a memory
budget. `DratProofShape::recommended_sample_bytes` encodes 5% with a 1 MiB floor.

Worth knowing beyond this module: any statistic taken from the head of a DRAT
proof is biased, and several natural "let me peek at the file" heuristics would
inherit it.

## G-6 (process, MEDIUM) — `MemAvailable` is the only instrument that is right about `/tmp`

Three ways to ask how much memory is free, on a host whose `/tmp` is a 62 GiB
tmpfs holding 39 GiB:

- `df -h /tmp` reports 24 GiB free **disk**. It is not disk.
- `free`'s `free` column reports 16 GiB and ignores reclaimable page cache.
- `/proc/meminfo`'s `MemAvailable` reports 72 GiB, and it already excludes
  `Shmem`.

The coordinator's process note says "`df` says disk; `free` says `shared`;
neither view alone predicts the OOM". `MemAvailable` alone does, and it is what
`MemoryBudget::from_system()` uses. Suggest the contributor guide say so once,
because every lane that schedules a memory-bound job will otherwise re-derive it.

Related and stronger: `MemoryBudget::from_system()` returns `Option`, and a
`None` is **not** treated as unlimited. Defaulting a missing measurement to no
limit is exactly the behaviour that produced the OOM kills.

## G-7 (defect risk, LOW) — a wrong-answer shape I looked for and did not find

Per action item 1's prose-guard sweep, I checked the one place in this change
where a memory optimisation could have become a soundness bug: the deletion index
is now keyed by a 64-bit hash of the clause's literal set. **The hash never
decides a match.** `RecordSlot::pop_matching` recomputes the candidate's sorted
key from the arena and compares the sets themselves, so a collision costs a
comparison and can never delete the wrong clause. That is a by-construction
argument, not a probability, and it is stated as such in the code.

I mention it because the *tempting* version — trusting a 64-bit hash, on the
reasoning that a collision is astronomically unlikely — would have been faster,
smaller, and silently wrong on some future proof, with the failure showing up as
an accepted refutation of a formula that is not the one on disk. It is the exact
shape of the guard class action item 1 is sweeping for.

---

## Top three

1. **G-1(2) — pack `CnfLit` into a 4-byte code.** Confined to `axeyum-cnf`,
   breaks no signature (the derived `Ord` is provably unchanged), and halves
   literal storage in the formula, the parsed DRAT step vector and the backward
   checker's arena at once. Half the `CnfFormula` win for a fraction of the
   `.clauses()` refactor.
2. **G-2 — build the formula's plan once per cover, not once per cube.**
   17.2 minutes of redundant work on agent-b's 6,241-cube cover, measured; the
   fix is a struct split and the differential assertion is trivial (the cloned
   plan must be byte-identical to the from-scratch one).
3. **G-5 — treat any head-sampled statistic of a DRAT proof as biased.** Not
   just for memory: a 0.1% head sample over-estimates mean clause width by up to
   2x, and several natural "let me peek at the file" heuristics would inherit
   that silently. `DratProofShape::recommended_sample_bytes` encodes the fix for
   this one use; the finding generalises.

Runners-up: G-3 (the deletion index is now the largest single term, and it is a
temporary), G-4 (the file-backed route pays for a non-refutation),
G-6 (`MemAvailable` is the only instrument that is right about `/tmp`).
