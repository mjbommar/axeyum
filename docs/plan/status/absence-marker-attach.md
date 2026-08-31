# Lane: absence-marker-attach

**Status:** in progress — diagnosing why a `was-absent:` marker would not attach.

## Finding (measured, not guessed)

`docs/plan/status/first-supplementary-law.md:50` carries a claim whose harvested
subject is exactly `Int.prodRange_split`, and a `<!-- was-absent:
Int.prodRange_split -- ... -->` marker sits in the same block. The site was
still reported BARE.

The cause is neither of the two hypotheses in the brief. The marker is written
across **three lines**, and `MARKER_RE`'s body group is `.*?` **without
`re.DOTALL`**, applied per line in every one of the three places that read a
marker. So the marker is not merely unattached — it is **not parsed at all**:

    MARKERS PARSED IN FILE: 0
    SITE line 50 | annotated=False | candidates: ('Int.prodRange_split',)

Surveyed over the whole scanned surface (4,695 files): 68 per-line marker
matches against 69 DOTALL matches. **Exactly one multi-line marker exists in
the tree, and it is this one.**

## Landed changes

| what | where |
| --- | --- |
| (in progress) | |
