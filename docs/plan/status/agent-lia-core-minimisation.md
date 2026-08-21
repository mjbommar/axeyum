# Lane: lia-core-minimisation — the width gate that made the solver quit at 5 % budget use is gone

<!-- plan-section: lane-status -->

**Gap #1's one confirmed fix is landed, in the form its diagnosis said to ship
it in: minimisation is budget-driven, not width-gated** (`WIP`,
agent-lia-core-minimisation, 2026-08-21). `dpll_lia.rs` had one constant doing
two jobs — deciding whether a theory conflict core was minimised at all, and
deciding which cores are charged against the wide-clause retention budget. The
[diagnosis](../../research/05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md)
§5.2 measured what that costs: the cores too wide to minimise are exactly the
cores whose width then exhausts the retention budget, so a solve declines for
want of the narrow clauses it refused to narrow. The jobs are now separate —
`MINIMIZATION_ORACLE_CALL_BUDGET` (a deterministic **oracle-call** ration, chosen
over wall clock because determinism is a public API promise) admits the pass;
`WIDE_THEORY_CORE_ATOMS` (still 128) only decides retention accounting, by
**retained width** rather than by provenance, which keeps the memory protection
the naive constant bump gives up.

Measured on the pinned 200-file competition lists, three binaries plus z3 4.13.3
run **adjacent in time per file** so contention is shared across the arms:

| division | base | A/B (128→4 096) | **shipped** | vs z3 | vs declared `:status` |
|---|---:|---:|---:|---|---|
| **QF_UFLIA** | 92 | 112 | **114 (+22, −0)** | **0** disagreements / 114 | **0** / 114 |
| QF_IDL (control) | 66 | 66 | **65 (+0, −1)** | **0** / 63 | **0** / 65 |

- **The diagnosis's A/B reproduces**: identical baseline (92), +20 here against
  its +17 on a more loaded sweep.
- **The shipped version strictly dominates the constant bump** — every file the
  bump decides, plus two more, losing none, while keeping the memory protection.
- The decline it targets (`retained N literals in unminimized theory cores`)
  occurs 31 times in the baseline arm and **0 times in 400 patched runs**. The
  QF_UFLIA files that still decline now fail on the *pre-SAT skeleton envelope* —
  a different constant, the diagnosis's separate `S2` class, and the next
  increment on this route.
- 7 of 8 guard mutations kill **exactly one** test; the survivor is a pre-existing
  arm whose unreachability is documented in the test rather than papered over.
- The control's single loss re-decides `unsat` on **all three** arms in isolation
  — but the shipped arm is ~**11 %** slower on that file, which on a loaded box
  pushed a 15-second file past the external kill. The change costs measurable
  time on QF_IDL and buys nothing there; that is what the control shows.

Capability ratchet (`progress_frontier`, `--features full`, 10 tests, 0 failed):
no REGRESSION on any family, and the reference frame reports **scale 1.09x–1.14x**
at load 3.1–4.2, so nothing is NOT COMPARABLE or ADVISORY. `lia_cuts` — the family
whose engine this touches — sits at 35 against a floor of 26. No baseline raised.

Not a parity result: the reference here is z3 4.13.3, cvc5 is absent on this
host, and only `scripts/parity-run.sh` may move a `PARITY.md` number.

Full method, controls and per-file data:
[the budget-driven theory-core minimisation note](../../research/05-algorithms/budget-driven-theory-core-minimisation-2026-08-21.md),
[ADR-0538](../../research/09-decisions/adr-0538-theory-core-minimisation-is-rationed-by-oracle-calls-not-by-core-width.md).

<!-- plan-section: landed-changes -->

| 2026-08-21 | `40a1ab969` | `crates/axeyum-solver/src/dpll_lia.rs` + ADR-0538 + `bench-results/lia-core-minimisation-20260821/`: theory-core minimisation rationed by an oracle-call work budget instead of a core-width gate. QF_UFLIA 92 → 114 (+22, −0) at 0 disagreements against z3 and 0 against the declared `:status`. |
