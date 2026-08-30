# Lane: modeq-div-gcd — the modular-cancellation-by-gcd family

<!-- plan-section: lane-status -->

**Done (`modeq-div-gcd`, 2026-08-30).** All five facts closed:

- `F:ml430-nat-modeq-cancel-left-div-gcd-57ef8287`
- `F:ml430-nat-modeq-cancel-right-div-gcd-22a4f40d`
- `F:ml430-nat-modeq-cancel-left-div-gcd-cfca1225`
- `F:ml430-int-modeq-cancel-left-div-gcd-b2d407e8`
- `F:ml430-int-modeq-cancel-right-div-gcd-00cd73fa`

Two prior lanes (`nat-modeq-mirrors`, `docs/plan/status/329-nat-modeq-mirrors.md`;
`int-dvd-mirrors`, `docs/plan/status/335-int-dvd-mirrors.md`) had sized this
whole family as needing a new "divide-by-gcd factorization" slice, built
around `Nat.gcd_mul_right` (which landed for a sibling family within the
hour before this lane started). **`gcd_mul_right` turned out NOT to be what
unlocks this family, on either carrier.** What actually closes it:

Detail moved to [`../notes/339-modeq-div-gcd.md`](../notes/339-modeq-div-gcd.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | `932812b9c` | wip: `modeq_cancel_div_gcd.rs` Nat family (3 mirrors), not yet compiled. |
| 2026-08-30 | `82752e56e` | Nat family admitted, axiom-free, registered, tested (concrete discriminating + symbolic); fixed a `mul_assoc` direction bug found via `Kernel::render_lean`. |
| 2026-08-30 | `590477e33` | Flip the three Nat facts + `depends_on` cascade fix (3 files). |
| 2026-08-30 | `6ec2edf6f` | wip: `modeq_cancel_div_gcd.rs` Int family (2 mirrors), compiles. |
| 2026-08-30 | `30cb26f7a` | Int family admitted, axiom-free, registered, tested; new `Int.mul` cancellation-by-nonzero lemma (first in this development). |
| 2026-08-30 | `523e45393` | Flip the two Int facts + `depends_on` cascade fix (2 files). |
