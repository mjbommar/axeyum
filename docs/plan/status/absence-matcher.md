# Lane: absence-matcher

**Status:** in progress -- narrowing `scripts/check-absence-claims.py`'s
claim-to-declaration association from BLOCK granularity to SENTENCE
granularity.

## The deficiency

A claim phrase fires on one sentence in a multi-paragraph block, and `DECL_RE`
then harvests **every** `Root.name` in the whole block as a candidate. Most of
those are cited as PRESENT evidence, not as the claim's subject. The
`absence-and-orphans` lane audited the remaining ~249 bare sites exhaustively
and found zero further genuine claims -- all false positives -- and scoped the
structural fix out of its own task.

## Landed changes

(none yet)
