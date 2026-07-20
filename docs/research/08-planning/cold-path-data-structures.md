# Cold-path performance: prototype evidence and the ADR-0285 resolution

Status: historical prototype note, corrected 2026-07-20 after ADR-0285.
Companion to
[`axeyum-glaurung-pareto-strategy.md`](axeyum-glaurung-pareto-strategy.md)
(Pillar B). The originally named scratch directories are not present in this
checkout, so their ratios are motivating observations, not reproducible or
accepted evidence. ADR-0285's committed in-tree gate is authoritative.

## The question

Cold one-shot solving trails z3 by ~1.34x on the deduped corpus; the durable
attribution puts **84% of the cold cost in term -> AIG -> CNF lowering**
(`bit_blast + cnf_encode`), not SAT. Two candidate levers, both of which MUST be
WASM-safe because deployability -- not speed -- is the thesis (the six-cell
result has warm Bitwuzla beating axeyum on all four drivers, so the value is
pure-Rust / WASM / no-C / proofs / determinism):

- (A) portable SIMD on the lowering loops;
- (B) data-structure / memory layout.

Both were reported as scratch prototypes **before** codifying, to avoid an
ADR-0200-style guess (a prior fingerprint-map data-structure change regressed
CNF 8.55%). Only the later ADR-0285 in-tree result is retained evidence.

## Prototype 1 -- SIMD: reported mechanism, but no retained hot-path surface

- **Reported scratch observation:** one pure-Rust
  `wide::u64x4` / `+simd128` source lowers to AVX2 on native
  (`vpand/vpor/vpxor %ymm`) AND simd128 on wasm32 (`v128.xor/and/or`,
  `i64x2.*`); a clean scalar loop autovectorizes to the same `v128` under
  `+simd128` (so the flag alone is the free win), and a scalar-fallback build
  (0 `v128`) covers WASM's lack of runtime SIMD detection.
- **But axeyum's hot loops do not vectorize.** The 84% lives in AIG
  `AndUniqueTable` open-addressed **hash-probe** insertion and CNF
  `tseitin_encode` **fingerprint-index / collision / clause-emit** work
  (ADR-0200/0259) -- pointer-chasing and hashing, the same class as SAT-core
  BCP. Portable SIMD has near-zero surface on the cost that matters.
- **Current decision:** do **not** invest engineering in SIMD. A future dual
  simd128/scalar deployment build is permissible only after its own committed
  build/runtime gate; this note does not establish that product configuration.
  Forbidden as
  envelope-breaking: linking a C SAT core, hand-written AVX-512 / `pulp`-style
  native-only multiversioning, SharedArrayBuffer threading. (Pillar B4.)

## Prototype 2 -- flat clause arena: motivating layout, rejected production candidate

**Code finding.** `axeyum-cnf` uses `CnfClause { lits: Vec<CnfLit> }` +
`clauses: Vec<CnfClause>` -- **one heap allocation per clause**, ~272k clauses,
avg ~2.2 literals (from the ADR-0259 profile). That is the classic SAT hot-path
anti-pattern. Kissat/CaDiCaL use a **flat clause arena** (all literals in one
contiguous buffer, clauses addressed by offset+length); **Varisat** implements
exactly this in Rust (one `Vec<LitIdx>` + a clause header per clause via
`#[repr(transparent)]`).

**Reported scratch microbenchmark** on a distribution derived from the real
profile (272k clauses / 600k literals;
sizes ~8% unit / 65% binary / 29% ternary / <1% larger, taken from the ADR-0259
attribution), comparing `Vec<Vec<Lit>>` (current) vs a flat `Vec<Lit>` +
`(offset,len)` arena:

| metric | Vec-per-clause | flat arena | delta |
|---|---:|---:|---|
| allocations | 272,000 | 2 | -- |
| build | 5.0 ms | 1.3 ms | **3.9x faster** |
| scan (clean heap) | 0.93 ms | 0.89 ms | 1.05x (wash) |
| scan (fragmented heap) | 1.44 ms | 0.89 ms | **1.61x faster** |
| memory (estimate) | 11.1 MB | 4.6 MB | **2.4x smaller** |

- The **build** win is eliminating 272k `malloc`s. The **scan** win appears only
  under a *fragmented* heap (the realistic case -- clauses are allocated amid
  gate/term construction, not on a fresh contiguous heap): 1.61x. The clean-heap
  scan is a wash, so the fragmentation result is the honest one to quote.
- **Memory 2.4x smaller** is also a WASM/deployability win (constrained linear
  memory), and it amplifies under wasm's `dlmalloc` where per-object allocation
  is dearer. The arena code compiles for `wasm32` unchanged (plain `Vec`s).
- **Low-risk:** the CNF clause DB is **append-only** (grep-confirmed:
  `clauses.push`, no `remove`/`retain`/`drain`/`swap_remove`), so the flat
  arena's one downside -- compaction on deletion -- **does not apply**. The
  change is localized to `axeyum-cnf` construction + handoff to `rustsat-batsat`;
  batsat keeps its own learned-clause DB, untouched.

## Honest scope (do not over-claim)

- The 3.9x / 1.61x is the **emission/allocation sub-phase**, not the whole 42%
  CNF cost, which also includes literal canonicalization, false-constant dropping
  (186k), and fingerprint hashing the arena does not touch. Per ADR-0259's own
  rule -- **"counts are not time"** -- the end-to-end CNF speedup is a *fraction*
  of 3.9x and MUST be measured in-tree before any paper number.
- **Do NOT touch:** the CNF fingerprint map (ADR-0200 regressed 8.55%), the AIG
  unique table (already index-based `u32`, open-addressed), or the hasher
  (already a custom `FingerprintHasher` over hashbrown/SwissTable).
- If a future representation clears an independent in-tree gate, its intended
  value is a narrower cold gap plus lower footprint, not a paper headline or a
  claim of closing the Bitwuzla gap. ADR-0285 did not clear that gate.

## ADR-0285 authoritative result

The in-tree flat representation passed all 162 exact decision, replay,
construction-count, and offset/accounting checks. Its aggregate logical storage
was 54.08% of the legacy lower bound, but five payload-dominated singleton-
clause rows used 92.86--96.27% and failed the preregistered per-instance <=80%
gate. Timing was therefore forbidden, the candidate was removed, and production
was restored. The scratch ratios above must not be promoted or used to relax
that gate post-observation.

Current recommendation:

1. do not invest in SIMD for the measured hash/probe-dominated hot path;
2. do not rerun or retune the ADR-0285 flat arena from its rejected rows; and
3. keep algorithmic word-level reduction as the open cold-path direction. A
   different memory layout needs independent motivation and a new zero-row ADR.

## Prototype-artifact availability

The originally cited `scratchpad/simd-proto/` and
`scratchpad/clausedb-proto/` directories are absent. Preserve the reported
numbers only as hypothesis-generating history. Reproduce the accepted/rejected
production decision from ADR-0285 and its committed artifact-v38 result instead.

## References

- MiniSat/CaDiCaL/Kissat contiguous clause memory layout:
  https://www.msoos.org/2016/03/memory-layout-of-clauses-in-minisat/
- Varisat clause storage (flat `Vec` + header, Rust):
  https://jix.one/refactoring-varisat-2-clause-storage-and-unit-propagation/
- CaDiCaL 2.0 (CAV 2024):
  https://cca.informatik.uni-freiburg.de/papers/BiereFallerFazekasFleuryFroleyksPollitt-CAV24.pdf
- ABC / FRAIGs (AIG structural hashing):
  https://people.eecs.berkeley.edu/~alanmi/publications/2005/tech05_fraigs.pdf
- Portable SIMD in Rust (state of SIMD 2025):
  https://shnatsel.medium.com/the-state-of-simd-in-rust-in-2025-32c263e5f53d
