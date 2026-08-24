# 246 — Hash-bound transport projection

The first F4 projection derives source-to-admission lineage from existing
statement-adapter manifests and fact evidence. A chain is complete only when
the fact ID, source-statement SHA-256, and imported-goal SHA-256 agree. It has
no name-based fallback: unmatched adapter records remain incomplete.

Current census: nine adapter chains, all nine evidence-bound complete chains.
Completion accepts either an exact source-statement plus imported-goal binding,
or the newer exact adapter-manifest plus imported-goal plus target-content
binding. Neither form uses a theorem name as a fallback. This is a lineage
view, not theorem admission.
