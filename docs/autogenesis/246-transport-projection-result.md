# 246 — Hash-bound transport projection

The first F4 projection derives source-to-admission lineage from existing
statement-adapter manifests and fact evidence. A chain is complete only when
the fact ID, source-statement SHA-256, and imported-goal SHA-256 agree. It has
no name-based fallback: unmatched adapter records remain incomplete.

Current census: nine adapter chains, five evidence-bound complete chains, and
four incomplete chains. This is a lineage view, not theorem admission.
