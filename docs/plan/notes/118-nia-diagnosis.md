# Notes: 118-nia-diagnosis

Detail moved out of [`../status/118-nia-diagnosis.md`](../status/118-nia-diagnosis.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **The projected-clause estimator over-approximates by 9.4×**, measured
  (74,329,095 projected against 7,917,733 actual on one file). Lifting the gate
  by exactly that factor decides **0 of 49** and causes **0** memory aborts — the
  refusal was in front of a search that does not finish either. My explanation of
  *where* the slack comes from (constant-operand multiplies) was also measured
  and **refuted**: a popcount-aware charge moves the estimate 6 %.
- **The technique this family needs is already implemented and unreached.**
  `nia_linearize::small_domain_lemmas` splits a product whose narrow factor has a
  width-≤4 box, which is exactly the `[-2, 2]` box these benchmarks declare — but
  it is reachable only through the *lazy* refinement loop, which runs 19–126
  rounds and times out when the admission envelope is lifted.

**Postscript.** The board was re-measured 127 s after this landed
(`5be2b296c`) and the row now reads **40.7 % (33/81)**. Three same-day cvc5
runs give **76 / 76 / 81** against the **89** recorded 15 days earlier — the 89
is the outlier, and every "N files behind" priced off it is a few files too
large. My 38 is five above both same-day parity runs and I did not measure why;
treat it as this instrument's count. Nothing in the diagnosis moves: the classes
are per-file properties of our own failures, and a five-file boundary shift moves
no class across a conclusion.

Next, if this is picked up: an **eager** small-domain split feeding the resulting
linear integer problem to the LIA route, measured against the 74 `VeryMax/ITS`
misses. It is the one hypothesis these measurements have not refuted; it is
unpriced, and it is a route, not a constant.
