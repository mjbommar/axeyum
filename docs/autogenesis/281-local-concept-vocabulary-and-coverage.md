# 281 — Local concept vocabulary and restored coverage

Date: 2026-08-26

## Result

Axeyum now owns a small semantic vocabulary that can grow without resolving or
pinning another repository. The reviewed seed contains six concepts:

- excluded middle;
- complex numbers;
- circle geometry;
- factorial products;
- modular arithmetic; and
- equivalence relations.

Fifteen active `formalizes` links connect those concepts to three
empty-footprint kernel theorems and nine settled fact records. Every mapping is
human-reviewed and explicitly partial. The same theorem or fact can support
more than one concept when the reason names the exact law; this is why fifteen
links represent twelve distinct formal sources.

The generated coverage projection now joins three dimensions again:

| Dimension | Current population |
|---|---:|
| Reviewed family-topic concepts | 9 |
| Train/development family-topic facts | 177 |
| Qualified formalization facts | 9 |
| Reviewed kernel semantic anchors | 3 |
| Union of projected concepts | 13 |
| Held-out formalization links | 0 |

The projection includes the union of reviewed family topics and locally
formalized concepts. A concept may therefore appear with only topic guidance,
only formal content, or both. Empty dimensions are visible rather than treated
as falsehood or lack of mathematical relevance.

## Trust boundary

The overlay validator requires a `formalizes` link to have:

1. a locally resolved concept endpoint;
2. a checked fact or an empty-footprint kernel theorem as its source;
3. human-reviewed assurance and provenance;
4. a written reason identifying the exact law; and
5. `completeness: partial` plus an explicit coverage role.

Kernel acceptance establishes the theorem, not the semantic label. Human review
establishes the qualified label, not proof or admission authority. The concept
coverage projection excludes held-out fact identities and carries no dispatch
authority. The external-coupling gate confirms the overlay contains no sibling
path, revision, namespace, or resolver.

## Process for the next batch

1. Select a small cluster from the generated semantic-review queue or an
   uncovered family-topic row.
2. Read each exact formal statement and its footprint.
3. Author or reuse one self-contained local concept definition.
4. Add proposition-specific partial links with distinct reasons.
5. Run the overlay, coverage, queue, held-out, and external-coupling controls.
6. Regenerate all three derived views in the same commit.

Do not bulk-copy a reference graph, manufacture mappings from names, or count a
topic-family association as a formalization. The next useful batch should close
a measured search or curriculum gap and remain small enough for every edge to
be reviewed.

```sh
just autogenesis-knowledge-controls
just autogenesis-concept-coverage
python3 scripts/gen-autogenesis-kernel-semantic-review-queue.py --check
python3 scripts/check-external-coupling.py
```
