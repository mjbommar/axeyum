# Sub-problem reuse — roadmap

Status: **proposed, no slice started.** Written 2026-09-17 from a survey of the
tree, not from measurement; the first slice IS the measurement, and every
later slice is conditional on its number.

> One sentence: **make the things the solver already reuses inside one arena
> reusable across arenas, processes and files — without any reused thing ever
> becoming a verdict on its own.** A hit changes time; only replay, a checked
> core, or a proved template changes an answer.

ADR numbers reserved for this programme: **2170–2179**. Do not allocate below
2170 for it; the board lanes are landing in the 2140s and 2150s this week.

## 0. What exists today, and the exact gap

Every reuse layer in the tree is keyed by something that dies with the arena or
the process:

| layer | reuses | key | lives | source |
|---|---|---|---|---|
| term arena | hash-consing; a `TermId` *is* structural identity | arena-local | process | `crates/axeyum-ir` |
| AIG | gate structural hashing | arena-local | process | `crates/axeyum-aig` |
| lowering memo | term → bit ranges; `IncrementalLowering` | `TermId` | process | ADR-0152, ADR-0009 |
| SAT core | learned clauses, phases, retained trail | CNF variable numbering | one `IncrementalCnf` | ADR-2145 |
| verdict cache | sat-with-replay / exact unsat / superset unsat over assertion **sets** | sorted set of `TermId` | one `IncrementalBvSolver` | ADR-2144, ADR-0189/0190 |
| Glaurung process cache | text-keyed verdicts | SHA-256 of assertion bytes | process | ADR-0303/0304 |
| fact ledger | proved theorems | name + formal statement | repository | `artifacts/facts/` |

Three facts pin the gap:

- `IncrementalCnf::formula_snapshot_assuming` (`crates/axeyum-cnf/src/lib.rs`)
  documents "Learned clauses are not exported." Nothing learned crosses a core.
- `crates/axeyum-rewrite/src/alpha.rs` has `alpha_equivalent` — a *decision*
  between two terms in one arena — and no alpha-normal **form**. There is no
  identity for a term that survives the arena, so there is nothing to key a
  cross-arena store by. This is the one primitive every slice below needs.
- ADR-2144 measured **62 % exact assertion-set reuse within one Glaurung
  session** (12,902 checks) and **0 effect on the 200-file QF_BV pinned list**
  because one-shot files never repeat a set inside one process. Whether files
  repeat sub-problems *across* each other is unmeasured. That is the number
  this roadmap turns on.

## 1. The units of reuse

"Sub-problem" is five different things. They are ranked by how well they travel
across problems and how cheaply a hit can be **validated** — validation is what
keeps a cache inside "untrusted fast search, trusted small checking."

| # | unit | value stored | validation on hit | travels? |
|---|---|---|---|---|
| U1 | route / strategy decision | which ladder rung and config decided problems with this feature vector | none needed — it is a hint; it changes order, never verdicts | best; key is features, not content |
| U2 | sub-formula → unsat core | the core over the canonical numbering (not the DRAT stream) | re-solve the core alone or check its proof; before that it is a **cut hint**, asserted first | across a benchmark family, where files are generated variants |
| U3 | sub-formula → model | model bytes over canonical symbols | replay against the original term (already a hard rule) | same; a near-miss model is still useful as initial phases |
| U4 | lemma template | a word-level lemma with constants abstracted to pattern variables | proved once (kernel, or reference solver labelled `cas-internal`-style), instantiation is then free | across divisions; this is ADR-2136's NIA lemmas made durable |
| U5 | circuit for a fixed expensive shape | the simplified AIG for `(op, widths)` after rewriting | trust-free (structural) | everywhere, but lowering is already cheap — build only if measured |

A learned CNF clause is **not** on this list on purpose: it is a set of Tseitin
variables that mean nothing outside the core that numbered them. The thing that
travels is its word-level lift, which is U4.

## 2. Representation

### 2.1 The canonical content key

`canonical_key(arena, term) -> CanonicalKey { bytes: Vec<u8>, hash: [u8; 32] }`
in `crates/axeyum-rewrite` next to `alpha.rs`.

- Merkle: `h(node) = H(op, sort, width, h(child_1), …)`.
- Free symbols are replaced by their **first-occurrence index in a
  deterministic traversal** plus their sort (de Bruijn for free variables).
  Bound variables are already positional in the alpha traversal.
- AC operators sort children by a **shape hash** (variable identity erased)
  before hashing. This is graph canonization, hard in general; we take the
  sound-but-incomplete version: two equivalent terms may get different keys,
  two non-equivalent terms never share one because —
- **the key is the serialized canonical bytes; the hash is only the index.**
  On a hash match, compare bytes. Soundness never rests on hash quality.
- Two tiers: the **exact key** (U2, U3) and the **shape key** with constants
  abstracted (U1, U4).
- Step-budgeted like `alpha_equivalent`; a budget exhaustion returns `None`,
  and `None` is a miss, never an error.

Determinism: the bytes are a public artifact. A golden test pins the bytes of
twenty fixtures; a mutation that changes traversal order must kill exactly that
test.

### 2.2 The entry is a receipt

Every stored value carries (ADR-0602's frame — operations are receipts):

```
Entry {
  key:        CanonicalKey            // exact or shape
  unit:       U1..U5
  value:      bytes                   // model / core / template / hint / aig
  producer:   { route: &str, config_digest: u64 }   // config_registry::digest()
  validated:  { how: Replay | CoreRecheck | Proved | None, at: producer version }
  provenance: { source file digest, division }   // never a path
}
```

`producer.config_digest` is the invalidation handle: a buggy producer is retired
by version, not by hunting its entries.

### 2.3 Storage

- **In-process:** the existing bounded LRUs (ADR-2144, ADR-0190) re-keyed by
  `CanonicalKey` instead of `TermId`, so a fresh arena in the same process
  hits. This is the smallest change with a measurable consumer (the Python
  `Incremental`, Glaurung's warm path).
- **On disk:** a content-addressed, append-only object store,
  `$AXEYUM_OBJECT_STORE` defaulting to `~/.cache/axeyum/objects/<hh>/<hash>`.
  Write to a temp file, `rename` into place; a second writer of the same key
  writes the same bytes, so concurrent lanes and processes never conflict and
  **there is no index file** — this repository has lost content twelve times
  through shared append points and this store must not be the thirteenth.
  Pure Rust hashing (`sha2` is already a workspace dependency; `blake3` is
  faster and also pure Rust — decide in ADR-2170, the default build stays free
  of C/C++ either way).
- Store small, validatable values (cores, models, templates, hints). Circuits
  (U5) only if slice 1 says the shapes recur and slice 6 says lowering costs.

### 2.4 Determinism and the lever

Cache on/off is a registered `config_registry` lever (`AXEYUM_SUBPROBLEM_CACHE`,
`on`/`off`, read once per process), shipped **OFF**, exactly as ADR-2144's
`AXEYUM_CANONICAL_CACHE`. The determinism promise is stated relative to config:
with the cache on, a repeated `sat` may return a different (replayed) model; a
verdict never differs. The corpus identity sweep compares on and off.

Every hit counter has a **rejection counter beside it** (`hits`,
`rejected_on_replay`, `rejected_on_recheck`, `rejected_stale_producer`). A
cache whose rejection counter cannot go nonzero is a checker that cannot fail;
each rejection path gets a soundness-negative fixture that dies alone when its
guard is deleted.

## 3. Slices

Each slice compiles, passes its named gates, and lands alone. Sizes are in lane
days on one host. "Gate" lists what the lane runs **on the branch** before
handoff, in addition to the pre-push hook.

### Slice 1 — the canonical key and the recurrence census (2 days) — ADR-2170

The measurement everything else is conditional on.

- `crates/axeyum-rewrite/src/canonical_key.rs`: `canonical_key`, exact and
  shape tiers, budget, golden bytes test, a commutativity test
  (`x + y` and `y + x` share a key), a non-equivalence test (`x - y` and
  `y - x` do not), and an alpha test (`forall x. P x` and `forall y. P y` do).
- `crates/axeyum-bench/examples/subproblem_census.rs`: for a list of files,
  parse, canonicalize with the shipped canonicalizer, and emit for every
  sub-term above a size threshold its exact key, shape key, node count and
  file. Output is a TSV, one row per (key, file). **The example refuses, it
  does not skip:** a file that fails to parse is a counted row with a reason,
  never silently omitted, or the census measures the accepted subset.
- Run it over the 16-division pinned lists (`bench-results/board-*`) and report
  three numbers per division: sub-terms recurring **within** a file, **across
  files in one family**, **across divisions** — each as a share of total
  sub-term nodes, weighted by node count, at thresholds 8, 32, 128 nodes.

Exit: the ADR carries the table. **Decision rule, fixed now:**

- cross-file exact recurrence ≥ 10 % by weight in at least three divisions →
  slices 3–5 proceed as written;
- 2–10 % → slices 3–4 proceed only for the divisions above 10 %; slice 5 is
  re-scoped to those;
- < 2 % everywhere → slices 3, 4, 6 are cancelled; slices 2 and 7 still stand
  (they do not depend on cross-file recurrence).

Gate: `cargo test -p axeyum-rewrite`, clippy on the crate, the golden bytes
test, and a positive control for the census (a directory of one file copied
twice must report 100 % cross-file recurrence).

### Slice 2 — re-key the in-process caches (2 days) — ADR-2171

Independent of slice 1's number.

- ADR-2144's `CanonicalConstraintCache`: key by the sorted set of exact
  `CanonicalKey` hashes instead of `TermId`; the model is stored over canonical
  symbol indices and mapped back through the live arena's symbol table before
  replay. Replay against the live term stays mandatory.
- ADR-0190's ordered cache: same re-keying.
- Consumer: the Python `Incremental` and Glaurung's warm path with **two
  arenas** in one process (today's 0 % → measured hit rate).
- Existing mutation controls must still each kill exactly one test; add one:
  a symbol-map mutation (swap two indices) must be caught by replay, counted
  under `rejected_on_replay`, and produce a fresh solve, never a wrong `sat`.

Gate: `tests/canonical_constraint_cache_2144.rs`, the new session fuzz from
ADR-2145 (push/assert/check/pop against a fresh solve, a replay and z3), the
`QF_BV` and `QF_ABV` pinned lists one-binary interleaved on/off (0 verdict
movers is the exit).

### Slice 3 — the object store and the receipt (2 days) — ADR-2172

- `crates/axeyum-solver/src/subproblem_store.rs` (or a new leaf crate if the
  boundary is exercised by two consumers — ADR-0001 says prove the boundary
  first): `put(Entry) -> Hash`, `get(&CanonicalKey, unit) -> Vec<Entry>`,
  content-addressed, temp-then-rename, no index, no lock.
- The lever, registered in `config_registry` with its note, shipped OFF.
- Counters on `stats()`: hits, and the three rejection counters.
- Concurrency test: sixteen threads `put` the same entry; exactly one file
  exists and its bytes equal the input. A stale-producer test: an entry with a
  foreign `config_digest` is read, counted `rejected_stale_producer`, never
  used.

Gate: crate tests, clippy, and `cargo build --target wasm32-unknown-unknown -p
axeyum-solver` — the store is behind a `std`-only feature so the wasm build
(ADR-0017) stays green.

### Slice 4 — U3 models and U2 cores as cut hints (4 days) — ADR-2173

The first slice that touches a verdict path.

- On a one-shot `unsat` with a core available, `put` the core over canonical
  symbols for **each maximal sub-formula the core lies inside** (the whole
  assertion set, and each assertion group the parser delimits). On `sat`, `put`
  the model for the whole set.
- On solve, before the ladder: exact-key lookup. A model hit is replayed; on
  success it is the answer. A core hit is **asserted first as a cut** and the
  ladder runs as usual — the SAT core reaches the conflict at once if the hint
  is right and is unaffected if it is wrong. A core hit becomes a verdict only
  in slice 5.
- A/B on the pinned lists of the divisions slice 1 named, one binary, two
  environment values, arms interleaved per file, 24 s / 8 GiB, three rounds on
  every mover. Warm the store with pass 1 of the same list; measure pass 2.
  The cold pass is the regression control and must show 0 verdict movers.
- Soundness-negative fixtures: a model from file A replayed against a
  key-colliding-by-construction file B (force the collision by mutating the
  key function under `cfg(test)`) is rejected and counted; a core hint that is
  wrong (mutated one literal) changes nothing but time.

Exit: verdict movers ≥ 0 on both passes, 0 losses, 0 flips, `:status`
disagreements 0, and the ADR reports the hit and rejection counts per division.

Gate: the corpus sweep (`--features full`, nonzero count), the five z3
differential fuzzes for any division whose arithmetic route is touched, the
capability ratchet with its reference frame lines read.

### Slice 5 — a checked core is a verdict (3 days) — ADR-2174

- A core hit is re-solved **alone** under a small budget; `unsat` on the core
  alone, with the core's assertions each `alpha_equivalent` to a live
  assertion, is an `unsat` verdict at `SatRefutation` assurance with the
  refutation produced by that re-solve — never the stored one. The store's
  role is to make the re-solve small; the trust comes from the fresh proof.
- If the re-solve is `unknown` under budget, the hint falls back to slice 4's
  behaviour, counted.
- Mutation: delete the `alpha_equivalent` check between core assertions and
  live assertions; exactly one soundness-negative dies (a core from a
  differently-signed variant must not refute the live file).

Gate: as slice 4, plus `tests/theory_lemma_proof_contract.rs` (ADR-1704) if
the core carries theory lemmas.

### Slice 6 — U5 circuit memo (2 days, conditional) — ADR-2175

Only if slice 1's shape census shows the wide `bvmul` / `bvudiv` / `bvurem`
families recur AND a profile of the lowering phase on those files shows
rewriting-plus-lowering above 10 % of decided time. Otherwise cancelled and
the ADR records the two numbers.

- Key: shape key of the operator node with widths; value: the simplified AIG
  in ASCII AIGER (already exportable); on hit, splice by `IncrementalLowering`
  input maps. Equivalence check on hit: random simulation over 64 vectors,
  counted, then a bounded SAT equivalence check on the first use per process.

### Slice 7 — U1 route hints (3 days) — ADR-2176

Independent of slice 1's number and the largest expected effect on the board.

- Feature vector: division, assertion count, node count, the operator
  histogram over the shape keys, quantifier depth, max width, literal
  magnitude class. Deterministic, printed on `stats()`.
- Value: for each decided pinned-list file, the rung that decided it and its
  time; aggregated per feature bucket into an order over the ladder.
- On solve with the lever on, `AXEYUM_LADDER_ORDER`'s mechanism (`auto.rs`)
  takes the hinted order for that bucket; unhinted buckets keep `DERIVED`.
- The three `unsat → unknown` losses from ADR-2136 are the first target: they
  are budget starvation of a later rung, and a hint that moves that rung
  earlier for their bucket is a one-line experiment.
- A/B on all 16 divisions; a held-out family per division is scored blind
  (the partition is declared in the ADR before the run, per the held-out
  discipline).

Exit: net ≥ +0 with 0 stable losses on pinned AND held-out, else ships
DISARMED with the movers listed.

### Slice 8 — U4 lemma templates (5 days, after slices 3 and 7) — ADR-2177

- Mine: on every theory lemma emitted by `nia_linearize.rs`, `cdclt.rs` and
  the string routes on a decided file, abstract constants to pattern variables
  and store under the shape key with `validated: None`.
- Prove: a separate job takes stored templates, tries the kernel first
  (`arith_prelude` / `int_prelude` order and monotonicity facts are the
  targets), then z3 as a labelled yardstick; a proved template gets
  `validated: Proved` with the proof's trust id. Unproved templates are never
  instantiated.
- Use: on solve, instantiate proved templates whose trigger (the shape key)
  matches, as input clauses — ADR-1704 already says how a refutation modulo
  enumerated theory lemmas is checked and labelled.
- Measure on QF_NIA, UFNIA, and a Real-sorted control that must show 0 movers.

## 4. Order and dependencies

```
S1 census ──┬──> S4 models+cores ──> S5 checked core verdict
            ├──> S6 circuits (conditional)
            └──> (decision rule gates S4/S5/S6)
S2 re-key in-process ───────────────────────────> S8 templates
S3 object store ─────┬──> S4                     ^
                     └──> S7 route hints ────────┘
```

S1, S2, S3 and S7 have no dependency on each other and can run as four lanes.
S4 waits on S1's decision and S3. S8 is last.

## 5. What this roadmap is not

- Not a learned-clause database. Clauses do not travel; their lifts do.
- Not a trusted component. No entry is ever a verdict without replay, a fresh
  refutation, or a proof — the store makes the trusted check *small*, it does
  not replace it.
- Not a change to the ladder's defaults. Every lever ships OFF and moves only
  on a pinned-list A/B with a held-out partition, like every lever this month.

## 6. Hazards named in advance

- **Identity by hash without validation is a soundness hole.** The key is the
  bytes; every hit is validated; the rejection counters are tested to be
  reachable.
- **Graph canonization is hard.** The key is deliberately incomplete under AC
  and symmetry. Slice 1 reports how often `alpha_equivalent` pairs get
  different keys on the census, so the incompleteness is a number.
- **A shared on-disk store is a shared append point.** Content-addressed,
  append-only, temp-then-rename, no index. The lock-free property is a test.
- **Cache warmth taxes measurement.** Every A/B states whether the store was
  warm and from what; a warm-store pass 2 is compared to a cold pass 1 of the
  same binary, never to a different day's board.
- **A census that skips is a census of the accepted subset.** The census
  counts refusals as rows.
- **The store must not become a second fact ledger.** Proved templates (U4)
  that are theorems in their own right go into `artifacts/facts/` through the
  normal validator; the store holds only the trigger and the pointer.
