# Nat.fib_add_two admission

Date: 2026-08-19

Registration prestate: `11c700a9b92536655bd3d0f1cc99810f4d257c32`

## Result

The flywheel converted the checked two-kernel `Nat.fib_add_two` receipt into
durable ledger knowledge. The machine frontier selected exactly
`F:ml430-nat-fib-add-two-b86e0c82`; no caller supplied a route, checker,
footprint, or status. The registered operation replayed the immutable receipt,
and the typed transaction derived an axiom-free `kernel-lean` admission.

## Durable chain

| Object | Content identity |
|---|---|
| Frontier before | `15a60980c1badc99163c5e47b6c84e87526264668983e6139de1c1595f6cdbf6` |
| Operation execution | `d55dac246e5d4ffc5a6eb716fb236ab183cc84ca8f147a81d53073dc8c61bb85` |
| Prepared transaction | `b37e368a87cdf8dd497c835afd3d92df131e5f16d54289d79d03a10fa677fe3e` |
| Durable admission event | `1a868c6ab73c220c5c965859e81512b2a6bb569d9cc8ae2b97d7e4bb00972587` |
| Frontier after | `34b1c5e8e4e94dbda448927b4eaf493ac39350481e64e6713e29f2c42411881a` |
| Readiness delta | `88c71e198f8656ce77d45c975bb5f7670ab124ad05571eb7b26b101b681b4ec3` |

The complete read-only archive, including the journal and complete Git bundle,
is `/nas3/data/axeyum/autogenesis/admissions/11c700a9b-mathlib-nat-fib-add-two-v1/`.

## Crash control and measured unlock

The first apply stopped after durable intent with exit status 75. The fact was
byte-identical to its prestate; recovery from only the transaction and journal
then committed the event. The settled fact operation replays and all 324 facts
validate.

Three facts directly depend on this recurrence, but exactly two are newly ready:

- `F:ml430-nat-fib-coprime-fib-succ-162fc738`
- `F:ml430-nat-fib-le-fib-succ-d1ef4a3d`

`F:ml430-int-fib-add-two-739358dd` remains blocked by the open
`F:ml430-int-fib-natcast-d5886be4`. This distinction is derived from the
frontier, not inferred from adjacency.

## Remaining control

The admission is committed and archived, but clean isolated replay is still
pending. The generic replay tool now compares the fresh and retained readiness
deltas instead of assuming every admitted fact is a leaf. Final archive credit
requires that replay to reproduce both newly ready children exactly.
