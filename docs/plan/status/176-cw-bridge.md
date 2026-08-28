# Lane: cw-bridge — the `close_within` → `CReal.Converges` regularity bridge

<!-- plan-section: lane-status -->

**Status: IN PROGRESS (cw-bridge, 2026-08-28).** Target: a public bridge
taking `close_within`-shaped evidence (`le (abs (add (f n) (neg L))) (ofRat
(natDivSucc rate n))`, the shape `UniformConvergesOn.spec` produces) into
`CReal.Converges f L` (a bound on the RATIONAL representative samples at a
shared index). `docs/plan/status/175-pi-r2b.md` sized this as the single
missing piece under π rung 2 and as comparable in scale to
`CReal.converges_add`'s own construction.

<!-- plan-section: landed-changes -->

| 2026-08-28 | cw-bridge | opened the `close_within` → `Converges` bridge lane |
