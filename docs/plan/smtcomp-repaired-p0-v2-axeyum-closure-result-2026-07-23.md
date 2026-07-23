# SMT-COMP repaired P0 v2 Axeyum closure result

Status: live process-free closure complete and independently validated; cvc5
blocked until these exact result and admission-source bytes are integrated on
`origin/main`
Date: 2026-07-23
Plan: [export-layout closure plan](smtcomp-repaired-p0-v2-export-layout-closure-plan-2026-07-23.md)
Preparation: [P0-S1 v2 result](smtcomp-repaired-p0-preparation-s1-result-2026-07-23.md)

## Result

The integrated closure implementation was run exactly once against the frozen
Axeyum v2 cell in closure-only mode. It launched no solver or coordinator
process. The strict generic run validator remained unchanged and reproduced
the frozen 1,810-record canonical bundle. The process-free operation:

- installed the exact recomputed adjudication under
  `cell-results/axeyum/p0-cell-adjudication.json`;
- migrated only the exact legacy top-level adjudication to the content-bound
  ignored path
  `cells/axeyum/quarantine/p0-cell-adjudication-layout-v1-fe880b9ae4dc04aeed938ad9e3fd7a350fe326cdba1a97fd6361721f85a6a824.json`;
- generated the complete 1,810-row legacy raw export under the external result
  namespace; and
- installed and validated the external cell completion last.

The original runtime records, attempts, terminals, shard completions, resource
completion, multi-host completion, timings, and sidecars were not rewritten.

## Bound identity

| Item | Value |
|---|---|
| Preparation root | `/nas3/data/axeyum/harness/official-selection-2026-sq/repaired-p0-prep-20260723-75e544a8-v2` |
| Preparation completion SHA-256 | `8d9145b2673ee10bf7c38990c20301f13323cfe4ab02c9946b403d0d2e4f4261` |
| Preparation record SHA-256 | `d3ae8e7cd870c48c19417495aeb99b53ed1a797db58092b79d0828b9255b5f7b` |
| Run identity SHA-256 | `5d75bf98f1fe7e8458ac1f5efbd75ea728bd57cff9b0c674002986c6e8dcd2d3` |
| Canonical bundle SHA-256 | `104f27cd184b3aff00e33b2322409fcc707bf7f37f9c6a548e0bb6376f733c6a` |
| Adjudication file SHA-256 | `fe880b9ae4dc04aeed938ad9e3fd7a350fe326cdba1a97fd6361721f85a6a824` |
| Adjudication record SHA-256 | `bf26f54c89d2f09b49155ff13239c1fb87fc165deffa61e6537c6471e5073598` |
| Raw export SHA-256 | `9424ab09f44c63b7370e3472b299eeab051b1e7d66cfe2de967cb05088581820` |
| Raw export rows | 1,810 |
| External completion file SHA-256 | `28402ac34a91715ab60ad2ff6dd1f1774ec60b5594131592da317dd23faa33ca` |
| External completion record SHA-256 | `97f27a480f9694e97765d669823b05c34ced8825f2f598c16e00ea301b1c4a57` |
| Resource completion file SHA-256 | `99483e252237bf40afd99a556fc4b94a5b079dac36a032acd87a28bd55bcd900` |
| Resource completion record SHA-256 | `2ef457926974aa3684e9bb32a31556a50f2f5266d8c018fba5f396b35815af93` |
| Multi-host completion file SHA-256 | `8e2463fc157a6324149b2902739f7a282fec11c978b5ba467f6e529014c459cc` |
| Multi-host completion record SHA-256 | `ab0648347ab4b1a34f7f1bef58f3683930805039034ef7bf817f3334f73b5eaa` |
| Safe to continue | `true` |

The recomputed adjudication remains 450 `sat`, 464 `unsat`, 280 `unknown`, and
616 no-verdict records; 1,192 processes completed and 618 hit the registered
wall timeout. Known-status contradictions and cross-solver disagreements are
both zero.

## Independent validation

After closure, an independent validation pass established:

- the generic preparation validator passes with runtime evidence admitted;
- `validate_cell_result` recomputes the adjudication and raw export and returns
  record SHA-256 `97f27a48...b1c4a57`;
- only the three registered external result files exist;
- the legacy top-level adjudication and raw export are absent;
- the quarantined and external adjudication bytes both hash to
  `fe880b9a...a6a824`;
- replaying the closure command leaves all three external file SHA-256 values
  byte-identical; and
- cvc5 and Bitwuzla each retain zero runtime-evidence artifacts, while `s5`,
  `s6`, and `s7` retain zero matching solver/coordinator processes.

## Credit and next admission

The Axeyum v2 cell now has the complete external result required by the closure
plan. It receives no P0 credit while this result document and its new
admission-source check exist only on the topic branch. The coordinator now
requires this exact document, the closure plan, and its source files to be
byte-identical to `origin/main` before admitting cvc5. Once those bytes are
integrated, revalidate the Axeyum external completion and launch only the
frozen cvc5 initial allocations. Bitwuzla remains blocked behind a validated
cvc5 external completion.
