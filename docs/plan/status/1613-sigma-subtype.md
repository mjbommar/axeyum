# Lane: sigma-subtype — declare `Sigma`/`Subtype`/`Fin` in the kernel and re-test the three sites they blocked

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, sigma-subtype, 2026-09-04).** W0-5: dependent pairs
are an ordinary inductive, not an axiom, and the kernel has none. Three ADRs hit
the same wall in one day — ADR-1595 (the image of a hom needs a subtype),
ADR-1602 (a metric subspace needs `Subtype`), ADR-1612 (L¹ needs `Sigma` to
bundle an integrability witness into a carrier). ADR-1606 rejected `Fin n → CReal`
for the same reason. This lane finds out by trying whether the absence is an
oversight or ADR-1495's constructor-field universe guard refusing `Sort (max u v)`.

Step 0 (absence confirmed, 2026-09-04): `shape_search --include-constructed`
over `declarations=3935` reports zero declarations under each of `Sigma`,
`PSigma`, `Subtype`, `Fin`; positive controls `Metric.creal_complete` (FOUND 1)
and the same-group `Exists` (FOUND 1, inductive) confirm the index is current
and covers the logic group where these belong.

<!-- plan-section: landed-changes -->

| 2026-09-04 | sigma-subtype | opened W0-5: confirmed `Sigma`/`PSigma`/`Subtype`/`Fin` absent at declarations=3935 with two positive controls |
