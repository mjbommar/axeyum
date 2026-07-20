# Cold-path data-structure candidates: agent review + prototypes (2026-07-20)

Status: research note. Follow-up to
[`cold-path-data-structures.md`](cold-path-data-structures.md) (SIMD ruled out;
flat clause arena rejected at ADR-0285). This round investigated *other* data
structures via two sub-agents (one analyzing axeyum's `ir`/`aig`/`cnf`/`bv`, one
cloning splr + varisat for transferable techniques) plus three
counting-allocator prototypes. Scratch prototypes are motivating, not accepted
evidence -- every candidate must clear an in-tree gate before shipping.

## Method
- Agent A: read-only analysis of `axeyum-ir/arena.rs+term.rs`, `axeyum-aig`,
  `axeyum-cnf` encoder core, `axeyum-bv` bit-blast core -> ranked candidates.
- Agent B: cloned `splr` (Kissat-inspired) + `varisat` (documented flat
  allocator) -> transferable techniques, cross-checked against axeyum's ADR
  history to avoid re-proposing closed work.
- My prototypes (`scratchpad/{clausedb-proto2,memo-proto,intern-proto}`),
  counting-allocator, on distributions from the ADR-0259 profile.

## Closed avenues (do not re-open)
| Idea | Status | Evidence |
|---|---|---|
| Flat shared clause arena | rejected | ADR-0285 per-instance <=80% storage gate (singletons 92-96%) |
| `SmallVec<[Lit;3]>` clauses | rejected | my prototype: 98% (mixed) / **112%** (unit-heavy) peak heap vs Vec -- inlining wastes space on the dominant tiny clauses |
| Streaming / discard-after-encode | infeasible | formula persists for `to_dimacs`/DRAT/handoff |
| Encoder scratch-buffer reuse | regressed | **ADR-0146: -1.1 to -4.9%** despite removing allocations |
| Zero-copy reverse planning traversal | regressed | **ADR-0147** (this is Agent A's "trivial" collect+rev -- already tried) |
| Clause-Vec capacity hints / pre-sizing | regressed | **ADR-0148 (+2.5%/+10% CNF), ADR-0149 (+0.83% CNF)** |
| CNF fingerprint open addressing | regressed | ADR-0200 (-8.55%) |

Meta-lesson (repeated in axeyum's own history): **"removes allocations" does not
imply "faster"** on this harness. Structural/allocation counts are not time
(ADR-0259). Every candidate below is "measure in-tree," not "obviously safe."

## Ranked candidates (converged across the two agents + my prototypes)

### 1. Dense-index bit-blast memo -- TOP candidate (three-review convergence; in-tree measurement required)
`axeyum-bv/src/lib.rs:780,1073`: `memo: BTreeMap<TermId, Vec<AigLit>>` -- the
term->AIG bridge, keyed by a *dense u32* arena index, looked up ~3x per term
(2 operands + root). This is the **one** place axeyum uses a tree map where its
own convention (`AndUniqueTable`, `node_vars`, `xor_gates`, ...) and both SOTA
solvers use O(1) dense-index `Vec`s. Agent A #3, Agent B #5, and my prototype
independently flag it.
- **Fix:** `Vec<Option<Vec<AigLit>>>` (or `Vec<Option<Rc<[AigLit]>>>`) sized to
  the arena, matching `term_bit_ranges` two crates over; Agent A notes the
  `BTreeMap` is never iterated, so its ordering buys nothing and it duplicates
  the existing dense arena (it can likely be *deleted*, not just re-typed).
- **Reported scratch measurement (not reproducible from this checkout):** the
  review diary reported BTreeMap+Vec-clone 77.0ms -> dense `Vec`+`Rc` 19.8ms
  (3.89x) over 300k synthetic terms, with 83% peak heap and 50% churn. The named
  `scratchpad/memo-proto` and diary directories are absent, and the candidate
  combines indexing with `Rc`; this is motivation only, not evidence.
- **Storage hypothesis:** this does not touch clause storage and may reduce
  lookup overhead, but dense slots can waste space on unreachable arena terms.
  Storage and RSS therefore remain measured gates. **Honest scope:** even a
  real memo win affects only part of bit lowering; whole-client time selects it.

### 2. Probe-before-allocate term interning -- strong, high-volume, measured
`axeyum-ir/arena.rs:460-468,235-244`: `app()` builds `Box<[TermId]>` **before**
the intern hit-check, so every construction pays 1 alloc even on a hash-consing
hit; `intern_node` clones the box again on a miss. Agent A #5, Agent B #6.
- **Fix:** `hashbrown` raw-entry / `Equivalent<TermNode>` with a borrowed
  `AppKey{op, args:&[TermId]}`; allocate the owned key only on a genuine miss.
  `hashbrown` already in the lockfile.
- **Measured (intern-proto, 1M constructions):** lookup-before-allocate scales
  with CSE hit rate -- 1.08x @30%, 1.27x @60%, **1.75x @85%**; churn to 69%.
  Rewrite/bit-blast paths are hit-heavy, so the effective rate is high.
- **Storage gate:** allocation reduction, no new duplication -> safe.

### 3. Packed `CnfLit` -> one `u32` -- orthogonal uniform win (Agent B #3)
`CnfLit { var: CnfVar(u32), negated: bool }` is 8 bytes (`axeyum-cnf:108-111`);
both SOTA solvers pack `(var<<1)|neg` into one 4-byte `#[repr(transparent)]`
word. **Halves every `Vec<CnfLit>` footprint uniformly, regardless of container**
-- it is orthogonal to the closed storage-strategy axis and would *improve* the
very ratio the arena failed. Clean memory + cache win; touches the `CnfLit` API.

### 4. `NonZeroU32` niching for dense `Option` memos (Agent B #4)
`node_vars: Vec<Option<CnfVar>>` (reallocated every `encode()`), `Option<TermId>`,
etc. halve if the backing `u32` is offset-by-one `NonZeroU32` (`Option` niches to
4 bytes). Small, safe, storage-positive.

### 5. `SmallVec`/fixed-array for transient planning gates (Agent B #8)
`NotAndGate` (provably <=2 elems), `AndTreeGate`, `DistributableNegativeAnd` use
`Vec` for small, transient, planning-phase data that is **never persisted into
`CnfFormula`** -- so it does not touch the per-instance storage gate. Sibling
`XorGate`/`NotIteGate` already use `[AigNodeId;2]`; this just applies axeyum's own
correct pattern to its inconsistent siblings.

### 6. Gate-plan take-restore instead of clone (Agent A #4)
`axeyum-cnf:3714,3724,4092,4094`: `self.not_and_gates[i].clone()` per AND-tree
node purely for the borrow checker; replace with `take()`-then-restore
(allocation-free move). Correctness trap: must restore or `CnfEncodingStats`
zeroes out. Not in the regressed-ADR list; verify.

## Recommendation
- **Implement + gate #1 (dense-index memo) first** -- strongest code-audit
  candidate and consistent with Axeyum's dense-ID convention. ADR-0300 replaces
  the absent, conflated scratch result with a BTree telemetry baseline, an
  isolated dense-`Vec` candidate, exact structural/storage checks, and paired
  whole-client timing. No micro number or assumed storage win selects it.
- **Then #2 (probe-before-allocate interning)** -- high volume, CSE-heavy paths.
- **Batch #3-5 (packed CnfLit, NonZero niching, SmallVec planning gates)** as
  orthogonal memory/cache wins independent of the storage-strategy debate.
- **Do NOT** retry scratch reuse (ADR-0146), reverse traversal (ADR-0147),
  capacity hints (ADR-0148/9), or any shared clause arena / SmallVec clause /
  streaming (this round + ADR-0285).
- Cold-path work stays bounded and is not the paper headline; it narrows the
  honest cold gap + footprint. It will not close the gap to Bitwuzla (SAT core is
  batsat's).

## Reproduction status

The reported scratch paths (`scratchpad/clausedb-proto2`, `memo-proto`,
`intern-proto`, `ds-review-logs`, and `ds-clones`) are absent from this checkout.
Their numbers are not accepted evidence. ADR-0300 replaces the top candidate's
missing reproduction with a committed representation-neutral profile, exact
client structural comparison, and conditional paired timing gate.
