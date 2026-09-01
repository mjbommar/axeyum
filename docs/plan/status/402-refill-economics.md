# Lane: refill-economics — measure the refill economics; say what would raise the ceiling

<!-- plan-section: lane-status -->

**Done (`DONE`, refill-economics, 2026-09-01).** ADR-1475, proposed.
Analysis lane; no draw authored, no constant, partition, threshold or screen
changed. Merged base `050b54ad7` (already `origin/main`, no merge needed).

**The binding constraint is ADMISSION, not supply.** 2,470 pinned inventory
rows pass every screen `select()` applies; eleven draws have admitted 500.
Of the rest, **1,922 sit in a module already bound to one of the 50 drawn
families** — 1,589 in a DEVELOPMENT or TRAIN family, of which **1,443 are
genuinely new** (Mathlib name not yet a kernel declaration). They are
unreachable: `select()` `continue`s past a drawn family via
`drawn_freeze()`, and raising `PER_FAMILY` does not merely fail to help —
guard **F4 refuses the whole generator** (`F4 drawn family
'descent-and-well-ordering' records 10 rows, not the 20 a draw takes`).
Unfreezing `integer-order` and re-selecting returns the identical ten rows
while 293 further screened rows sit in its module, so the pool is deep and
the CAP is what binds.

**New-family supply IS exhausted, and R5 is where it fails.** 79 screened
rows in 23 undrawn modules; one module reaches ten alone
(`Mathlib.Data.Nat.Count`, 22). Of **1,011** minimal undrawn bundles reaching
ten rows, **17** are R11-clean as held-out under the real `screen_family()`;
sixteen of those contain `Mathlib.Data.Nat.Factorization.Basic` and so
pairwise intersect, leaving `candidate-count` in every one of the 16 disjoint
pairs — and `assert_draw_lawful` **refuses** it (`do-not-draw-held-out`,
ADR-1100 restated by ADR-1115). Controls: 20 committed held-out families
rescore 0 refused; a bundle built from a development family's own module
(`Batteries.Data.Nat.Bitwise.Lemmas`) is refused with 2 topic hits. Note
`screen_family` alone calls `candidate-count` **clean** — the module bar
lives only in `assert_draw_lawful`.

**No held-out row has ever been settled.** 206 rows, 20 families, every one
`open`; positive control in the same population, development 273 proved / 27
open and train 197 proved / 11 open, 0 manifest rows without a fact file. All
seven ADR-0542 amendments are contamination REPAIRS, none an evaluation.
This is not an argument to thin the fraction and the ADR refuses to.

**A four-family draw pays 50% held-out, not one third.** `PARTITION_CYCLE`
restarts per draw, so n=4 lands held-out at cycle indices 0 and 3. A
six-family draw spends the **same two** held-out families for **40**
dispatchable rows against n=4's 20. Over the 11 real draws: 500 rows, 310
dispatchable (62%), mean 4.55 families and 28.2 dispatchable rows per draw.

**The vocabulary lever routes into the same bottleneck.** 1,156 rows are
blocked by exactly one missing constant; greedily adding the twelve best
(`instSubNat` 312 alone, then `Int.lcm`/`bmod`/`fmod`/`fdiv`/`tdiv`/`tmod`/
`sign`/`instMonoid`/`instMax`/`instMin`, `GE.ge`) admits 810 rows — but
**779 (96.2%)** land in already-frozen families.

**Recommends**, in measured order: (1) a dispatchable top-up into drawn
dev/train families — `select()` appends past the freeze, F4 becomes a prefix
check, R9/R11/R12 re-scope from family to row; **R3 headroom is 104 rows**
(attested 409, unattested 305) before re-attestation is required; (2) run a
blind evaluation; (3) extend the vocabulary, but only after (1); (4) draw six
rather than four. **Refuses** thinning the held-out fraction, lowering
`PER_FAMILY`, and construction batching, each with the measurement that kills
it.

**Zero-write**, proved with a working negative control:
`git status --untracked-files=no -- artifacts/` 0 lines; re-deriving all 500
drawn rows and comparing `(partition, family, source_name)` against the
manifest gives **DIFF 0**, and flipping one held-out row's partition in the
re-derived copy gives **DIFF 1**.

**Gates run** (statuses captured bare, not after a pipeline):
`gen-autogenesis-nursery-refill.py --check` 0 (`entries=500|…|attested=409|
unattested=305|screen_drift=31`), `check-holdout-adjacency.py` 0 (20
held-out families, 0 refused, 4 undisclosed sweeps — advisory here),
`check-dispatchable-frontier.py` 0 (**15 dispatchable**, 244 open mirrors, 205
held-out, 12 mutation controls, 12 divergence-blocked), `check-links.sh` 0,
`gen-adr-index.py` regenerated (`rows=752|duplicate_numbers=0166,0167`).

**Did not run:** any aggregate gate (`just check`, `check.sh`) or `cargo`
— this lane added one read-only Python script and Markdown, and touched no
`.rs`. The top-up in recommendation (1) was not implemented or trialled; it
is arithmetic from the measured pool. The ~5 min attestation cost is quoted
from `provision-lean-import-toolchain.sh`'s own figure, not re-measured here.

Full reasoning:
[ADR-1475](../../research/09-decisions/adr-1475-the-refill-ceiling-is-admission-not-supply.md).

<!-- plan-section: landed-changes -->

| 2026-09-01 | refill-economics | ADR-1475: refill ceiling is admission not supply; 1,443 dispatchable rows unreachable behind `PER_FAMILY`/F4, new-family supply exhausted at R5 |
| 2026-09-01 | refill-economics | `scripts/measure-refill-economics.py`, read-only supply and per-draw economics through the real generator |
