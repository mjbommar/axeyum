# Lane: lra-diagnosis — gap #1's "one shared cause" was a hypothesis, and it is refuted

<!-- plan-section: lane-status -->

**Ranked gap #1 is diagnosed: three causes, not one, and the largest single
block of losses is a route that quits at 5 % budget use** (`WIP`,
agent-lra-diagnosis, 2026-08-21). Measured at `8426fbd2d` over the four pinned
200-file competition lists (sha256 unchanged from their `PARITY.md` entries),
axeyum + z3 4.13.3 at 24 s each, then a second pass for route ladders. cvc5 is
not installed on this host; z3 lands within 5 files of cvc5's recorded count in
every division, which is why it is used to decide which failures count.
Instrument validated by reproducing QF_LRA's recorded 86/200 exactly.

278 misses classify as: **T** budget exhausted 146, **S** admission decline on a
size constant 73, **I** incompleteness 48, **P** front-door reject 11. The
route ladders say these are **three** causes, and they do not line up with the
divisions:

- **`dl-online` runs out of clock** — 64/65 QF_IDL and 51/55 QF_RDL misses. The
  one genuinely shared cause, and it is shared by two divisions, not four.
- **the LRA route** — QF_LRA (and QF_RDL's tail): half refuse on
  `MAX_ONLINE_LRA_ATOMS = 1_024`, half time out.
- **the lazy UF/arith CEGAR** — QF_UFLIA, **82 of 82** traced misses, one route.
- plus **26 QF_UFLIA files rejected at the parser** for `Int` literals beyond
  `i128` (the Certora/EVM family, 2^256 constants). A capability zero, 13 % of
  the division, untouched by any solver work.

Two one-constant A/Bs, built in a private snapshot, positive-controlled, never
in the shared tree:

- **REFUTED** — making the LRA atom cap fall through instead of terminal
  (`lra_theory.rs:203`): **0** new decides over 71 files and **54** memory
  aborts past 12 GiB. The cap is load-bearing protection; both routes are
  inadequate above ~1,000 atoms.
- **CONFIRMED** — `MAX_MINIMIZED_THEORY_CORE_ATOMS` 128 → 4 096
  (`dpll_lia.rs:48`). QF_UFLIA **92 → 109 (+17)**, QF_IDL 65 → 64 (the one loss
  re-decides on a quieter box on **both** binaries), **0 disagreements** against
  z3 and **0** against the declared `:status`. The 48 QF_UFLIA `I1` files return
  `unknown` after a median **1.3 s of 24 s** with `core_src_minimized=0` — the
  cores too wide to minimise are exactly the cores whose width then exhausts
  `MAX_DYNAMIC_LARGE_CORE_LITERALS`.

Next: the shipped form of that fix is **not** the constant this A/B moved —
minimisation should be budget-driven rather than width-gated, keeping the memory
protection the `Large` bucket exists for. Nothing here has been through
`scripts/parity-run.sh`, which is still gated by nothing (gap #2).

Full finding, all counts and controls:
[`../../research/05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md`](../../research/05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md).

<!-- plan-section: landed-changes -->

| 2026-08-21 | (pending) | `docs/research/05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md` + `bench-results/linear-arithmetic-diagnosis-20260821/`: gap #1 diagnosed — three causes not one, 800-file per-file classification, two A/Bs (one refuted, one +17 QF_UFLIA files at 0 disagreements). |
