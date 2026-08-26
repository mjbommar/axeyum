# 256 — Kernel semantic review queue

Date: 2026-08-24

## Result

[`kernel-semantic-review-queue-v1.json`](../../artifacts/autogenesis/kernel-semantic-review-queue-v1.json)
turns the accepted-kernel dependency projection into a reproducible review
population. At the current snapshot it contains:

<!-- kernel-semantic-review-census:start -->
| Measure | Count |
|---|---:|
| Empty-footprint kernel theorems | 1,287 |
| Active reviewed semantic anchors | 6 |
| Unreviewed queue entries | 1,281 |
<!-- kernel-semantic-review-census:end -->

Each entry records only mechanical information already in the kernel
projection: declaration identity, visibility, direct theorem dependencies, and
direct reverse references. The order is deterministic: reverse references,
then dependencies, then declaration identity.

## What the queue does not claim

Graph centrality is a review-order observation, not a statement about
mathematical importance, concept coverage, proof technique, producer fit, or
admission authority. A highly reused congruence theorem may deserve early
review because it connects many library paths, but it does not thereby map to a
concept, become a producer capability, or authorize a fact transition.

Likewise, a candidate or deprecated overlay link does **not** remove an item
from this queue. Only an active, manually reviewed kernel-source `formalizes`
link does. This protects the distinction between a proposed association and a
durable reviewed one.

## Review protocol

For a selected queue entry, a reviewer must read:

1. the kernel theorem's exact checked statement and footprint;
2. the pinned external concept or encounter source;
3. the proposed mapping's scope and explicit non-claims.

Then add one qualified overlay link, run the overlay validator and this queue's
freshness check, and regenerate dependent coverage artifacts. Do not use names
or namespace prefixes as a mapping generator. Those are only review cues.

```sh
python3 scripts/gen-autogenesis-kernel-semantic-review-queue.py --check
python3 -m unittest scripts.tests.test_gen_autogenesis_kernel_semantic_review_queue
just autogenesis-knowledge-derived-freshness
```

This is the bridge from the current small, defensible semantic batch to
kernel-scale enrichment: scalable selection with human-reviewed meaning.
