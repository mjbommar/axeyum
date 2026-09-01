# Lane: statement-headers — give the newly-annotated facts a checkable header

<!-- plan-section: lane-status -->

**In progress (`statement-headers`, 2026-08-31).** `check-settled-fact-statements.py`
reads `header_exempt=79` against `floor_header_exempt=67` and fails, blocking the
push. Verified this is a side effect of `366f11a91` (`resolve-kernel-subjects`),
not a regression: that commit added `formal.kernel_theorem` to 28 facts, and
exactly **12** of those carry a headerless `formal.statement`, which the gate
only counts once a fact names a declaration. 79 − 12 = 67, the old floor.

Work: give each of the twelve a real `theorem <Name> : ` header taken from the
kernel's own `canonical_type`, record one amendment per fact, and **lower**
`coverage_floor.max_header_exempt` to what is achieved. The ceiling is not
raised.

<!-- plan-section: landed-changes -->
