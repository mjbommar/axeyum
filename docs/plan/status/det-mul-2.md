# Lane: det-mul-2

<!-- plan-section: lane-status -->

**Status:** in progress. Picking up where `det-mul-general-n` stopped
(ADR-1541): `Rat.det_row_selection` is landed, and `Rat.det_mul` needs only
ADR-1440's obligation 1 — the expansion of `det (A·B) n` over index functions,
which needs a `Rat` analogue of `Int.sumMaps` (and possibly `Rat.prodRange`).

Step 0 (retrieval), then `Rat.prodRange` if needed, then `Rat.sumMaps`, then
obligation 1 and `Rat.det_mul`.

<!-- plan-section: landed-changes -->
