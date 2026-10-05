# Lane: draw-16

<!-- plan-section: lane-status -->

Status: complete (2026-08-31). Nursery draw 16 is AUTHORED.

## What this lane did

ADR-1240 and ADR-1245 filled cycle indices 0 and 3 with construction-only
unblocks and each left R11's authorable disclosure to the draw lane, which was
the only remaining refusal. This lane performed both reviews and authored the
draw.

- `artifacts/autogenesis/nursery-v2-extension.json` 420 -> **460** entries;
  `development` 160 -> 170, `train` 110 -> 120, `held-out` 150 -> **170**.
- `check-holdout-adjacency.py` 16 -> **18** held-out families, 0 refused,
  reviews 4 -> **6**.
- `check-autogenesis-holdout-isolation.py` `held_out` 166 -> **186**,
  `settled=0` before and after, `references=0`. No fact moved partition,
  `nursery-v1.json` untouched, nothing registered as settled.
- Forty fact files written by the generator, all `open`.

Everything was re-measured against a `shape_search --release` **rebuilt in this
worktree** at 2711 declarations (three more than ADR-1245's 2708:
`Int.firstSupplementaryLawResidue`, `Int.wilsonHalfSplit`, `Nat.sub_sub_self`),
with the real `select()` / `assign_partitions()` / `screen_family()` /
`guard()`. `propose-nursery-refill.py` was not used as a candidate space.

## The corrections and the findings

- **Layout RP does not exist as four single-module families.** At env 2711 only
  three unassigned modules carry a pool of 10 alone, two of which are the
  held-out candidates; `Mathlib.Data.Int.Fib.Basic` yields 6 and
  `Mathlib.Data.Int.NatPrime` yields 2, so `select()` RAISES on the literal
  reading. ADR-1220's own table said "2 modules" / "7 modules"; the two later
  ADRs dropped the parenthetical. Both fillers were rebuilt as bundles (14 and
  13). Index 1's primary module is effectively forced — one unassigned module
  in the whole sort window has a pool above 1.
- **`Mathlib.Data.Nat.Prime.Nth` was available and deliberately excluded.** It
  is the nth-prime module and `natural-nth-selector` is a standing held-out
  family. R11 would not have seen it: `cmd_check` scores a held-out family only
  against families drawn no later than itself.
- **Both disclosure sweeps found a gap in the SCREEN.** The
  characteristic-constant threshold (3 of 10 rows) drops `Nat.casesOn` and
  `Nat.floorRoot`, so their stems are never swept although a drawn row is about
  each. Hand-swept; both empty, but a review running only the automated sweep
  would not have known.
- **`Nat.Primrec.of_eq` looks unreachable without `funext`**, which this kernel
  deliberately lacks (`prelude.rs:61`; stems `funext`/`propext`/`choice` all
  sweep to 0). Disclosed as a reading, not as an established impossibility — a
  row that can never be established inflates the blind population's count.
- **`Nat.ceilRoot_pow_self` and the standing held-out `Nat.nthRoot_pow` are the
  same statement with a different root function**, along with three further
  rhyming pairs. Not a leak — R11 compares held-out against PUBLISHED and both
  are blind — but the two "root" families are not independent signals, and no
  screen we have asks that question.
- **The four advisory-undisclosed standing families were swept and DECLINED,
  with numbers.** `natural-nth-selector` (`nth` -> 4 declarations) and
  `natural-square-root` (`sqrt` -> 21, sixteen of them `CReal`, and no row is
  `sqrt_zero`/`sqrt_one`) were read in full and are clean. No review row was
  written: a `reviews` row is a live tripwire on the swept stems, and `abs`
  (73) and `sqrt` (21) are high-traffic namespaces under active development.
- **`Nat.fib_add` is already declared here** — one of the ten development rows,
  flagged `[MATCH]` by `check-autogenesis-already-proved.py`, exit 0. R9
  screens held-out only, so it neither fires nor should; the fibonacci family
  buys roughly three rows of real work, which is stated rather than glossed.

## Gates

| gate | result |
| --- | --- |
| `check-autogenesis-nursery.py` | exit 0, `v1=216 v2=460 components=365` |
| `check-autogenesis-holdout-isolation.py` | `held_out=186 settled=0 references=0 PASS` |
| `check-holdout-closed-evaluation.py` | `held_out=186 closed_shaped=0 violations=0 PASS` |
| `check-holdout-adjacency.py` | 18 families, 0 refused; `--self-test` 11 passed |
| `create-autogenesis-nursery-dispatch-baseline.py --check` | exit 0, literal unmoved |
| `gen-autogenesis-nursery-refill.py --check` | exit 0, `env=2711`, reproduces |
| `check-shape-duplicates.py` | exit 0, 15 groups, all allowlisted |
| `validate-facts.py` | exit 0 |
| `check-settled-fact-statements.py` | `settled=2253 pinned=2253 drifted=0 PASS` |
| `check-merge-hygiene.sh` | `markers=0 adr_index=ok generated=current PASS` |
| `check-links.sh` | `all links ok` |
| `check-absence-claims.py` | exit 0, **122 against a budget of 122** |
| `check-dispatchable-frontier.py` | **`DISPATCHABLE: 24`** — G7 was 4 against a floor of 10 |

**G7 `queue-below-floor` is the point of the draw and it is fixed**: 4 -> **24**
dispatchable, all twenty new `development`/`train` rows plus the four that were
already there.

`check-absence-claims.py` needed one edit: a sentence of the ADR read
"`--const Nat.nthRoot` is ABSENT", which the census classifies as a bare
absence claim naming a declaration that is in fact PRESENT (the claim is about
what mentions it, which the marker grammar cannot express). Reworded to name
the probe's result instead. The brief's report that this gate is red on `main`
at 123/122 is **stale** — ADR-1250 landed the fix during this lane's run, and
the gate is green at 122 both on `main` and here.

## Landed changes

| what | where |
| --- | --- |
| draw 16 authored (layout RP, 4 families, 40 rows) | `scripts/gen-autogenesis-nursery-refill.py`, `artifacts/autogenesis/nursery-v2-extension.json`, `artifacts/facts/` |
| both R11 disclosure reviews, performed | `artifacts/autogenesis/holdout-adjacency-review-v1.json` |
| the screen, over the real machinery | `docs/research/09-decisions/adr-1255-draw-16-screen.py` |
| the decision and both sweeps in full | `docs/research/09-decisions/adr-1255-draw-16-is-authored-and-both-disclosure-sweeps-found-something.md` |

## What is next

- The four advisory-undisclosed families are now costed rather than vague:
  `natural-nth-selector` is minutes, the other three put a permanent tripwire
  on high-traffic stems. A lane that intends to carry that maintenance should
  take it; a draw lane passing through should not.
- Index 0's pool is **11 against a floor of 10**. If two of those eleven ever
  become catalogued or unstatable, `select()` raises and the next refill fails.
- The supporting theorems for `Nat.Primrec`, `Nat.floorRoot` and `Nat.ceilRoot`
  can now land from `development`, where they cost nothing — but the
  `factorization_root` lane must re-run the adjacency screen first (ADR-1245),
  and finding 4 above says why that matters more than it looked.
