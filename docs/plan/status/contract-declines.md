# Lane: contract-declines — why all 27 producer-contract dispatches declined

<!-- plan-section: lane-status -->

**Answered (`done-for-now`, contract-declines, 2026-09-01).** The 2026-08-27
batch dispatched 27 facts through the two seed producer contracts and all 27
declined (15 `TrustedDeclaration`, 12 `TerminalNotClosed`). The question was
whether the contracts were aimed at the wrong shape (a), whether one specific
capability was missing that every dispatch hits (b), or something else (c).

**Verdict: (c).** Full write-up, with the command behind every number, in
[docs/research/11-design-review/2026-09-01-why-every-contract-dispatch-declined.md](../../research/11-design-review/2026-09-01-why-every-contract-dispatch-declined.md).

- Not (a): both shape predicates matched exactly their families and nothing
  else. The mismatch is one level up — both contracts named the same recipe
  (`examples/modeq_family_operation.rs`), whose vocabulary can only *permute*
  equalities already given as hypotheses. The members it can permute were
  already proved before the contracts were written, so each shape covered
  exactly the complement of its recipe's competence.
- Not (b): four structurally distinct causes across two pipeline stages.
  `TrustedDeclaration` is not a producer decline reason at all — for all 15
  nat-coprime facts the producer never ran.

**Root causes (27 rows, grouped; groups sum to 27):**

| # | stage | reason | mechanism | facts | disposition |
|---|---|---|---|---:|---|
| G1 | import | `TrustedDeclaration` | `Quot` via `Nat.minFac` | 1 | permanent (hard rule) |
| G2 | import | `TrustedDeclaration` | `eq_self`, needs `propext` | 5 | permanent (kernel has none) |
| G3 | import | `TrustedDeclaration` | `Nat.mod_lt` via `Nat.gcd`'s WF elaboration | 9 | deferred, ≥15 uncovered theorems incl. 7 WF internals (doc 295) |
| G4 | producer | `TerminalNotClosed` | goal needs a NEW `Int.emod` equality | 12 | deferred, a whole `emod` theory |

**The finding that actually explains the silence: 26 of the 27 declined facts
are now `proved`** — closed within days by hand-authored kernel declarations
(`int_prelude/modeq_family.rs`, `nat_prelude/primes.rs`) that never invoked a
producer, contract, or the import pipeline. The one still open is
`F:ml430-nat-coprime-of-lt-minfac-0f79bdba`, the single permanently-blocked
`Quot` case. The contract layer now matches **2 of 217** dependency-ready
open facts (`shape_matched_count`), and the only three facts in the 209-fact
`proof-route-only` pool that either contract's `statement_contains` would
match are outcome-blind mutation negative controls. Both contracts describe
exhausted families.

**Re-run, per the brief.** Two of the 27 dispatches (one per contract, one
per stage) were re-run today on the 2026-08-27 exports, whose sha256 digests
match the `identity.export_ndjson_sha256` recorded in the decline artifacts.
Both reproduce exactly. **No decline flipped**, and no bounded change would
flip one: every group is far above 200 lines, two are architecturally
permanent, and for 26 of 27 facts a flip would re-prove an already-proved
fact. No Rust and no checker was changed.

**Landed:**
- `docs/research/11-design-review/2026-09-01-why-every-contract-dispatch-declined.md`
  — the verdict, the 4-cause table, the reproduction, the 209-fact
  classification, the minimum change.
- `docs/research/09-decisions/adr-1510-a-contract-is-sized-by-the-frontier-and-a-decline-dies-with-its-fact.md`
  — a contract records the open population it was sized against and retires
  when that population empties; a decline against a settled fact must carry a
  `resolution` block. Both are strictly additional guards on artifacts; no
  accept path, kernel policy, or substitution allowlist changes.

**Next actions (for other lanes, not started here):**
1. Dispatch `F:ml430-nat-coprime-factorizationlcmleft-factorizationlcmright-e7db70ce`
   — it is `admissible`, dependency-ready, and has never been dispatched;
   `selection.outcome` is `selected`, not `refused`. Expect a G3 decline, but
   from a run.
2. Implement ADR-1510: the `resolution` backfill on 21 decline artifacts and
   the validator guard must land together, or the gate goes red.
3. Size a third producer against the 209-fact pool *before* writing its
   contract. The pool is dominated by `Iff`-headed (40), existential (14),
   `Decidable` (10) and higher-order induction-principle (10) statements no
   current producer addresses.

**Did not run:** no Lean/`lean4export` invocation on s5 (exports reused,
digests checked); 25 of the 27 dispatches not re-run; no workspace test
sweep; no mutation control (nothing mutable was changed).
