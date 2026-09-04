# Lane: rado-in-kernel — W1-1: define Rado numbers in-kernel and close the computed→proved gap

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, rado-in-kernel, 2026-09-04).** Roadmap item W1-1 (the
C2 convergence: 07.1, 11.1, 12.4). The ledger holds two `computed` Rado numbers
(`F:rado-r4-a5-b3` = 625, `F:rado-r4-a5-b4` = 741) with search certificates, and
nothing in the kernel says what a Rado number IS. This lane defines the object
over `Nat.Finset` / `Nat` and states the two halves (upper bound: every
k-colouring of `[1..n]` admits a monochromatic solution; lower bound: a specific
colouring of `[1..n-1]` admits none), parameterized over `n` so the unary numeral
625 is never FORMED.

Step 0 (shape_search, rebuilt 2026-09-04): `declarations=2674`,
`groups=[logic,nat,axreal,integer,ipc,rat,characterization,string]`, positive
control `Nat.Finset.exists_collision` (landed 2026-09-03, commit `164e4d329`)
MATCHed, exit 0.

<!-- plan-section: landed-changes -->

| 2026-09-04 | rado-in-kernel | lane opened: W1-1, Rado numbers in-kernel; shape_search baseline declarations=2674 |
