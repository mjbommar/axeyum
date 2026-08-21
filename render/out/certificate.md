# The p = 2 tame-point weight certificate

*Closed form, admissibility, and exact sharpness for the Kramer-Miller--Upton weight at p = 2, e = 3*

Authors: Axeyum render strand (prose only; every number is machine-produced)

> Kramer-Miller and Upton's local-to-global machinery needs an admissible weight, and at $p = 2$ their own remark records that they do not have one. This page is the output of a self-checking program that establishes one: a closed form for the transition coefficients, the valuation identity it implies, admissibility of $a(k) = \lfloor (k-1)/3 \rfloor + (k \bmod 2)$ over a swept range, and a single coefficient that caps the achievable growth rate exactly rather than bracketing it.

Kramer-Miller and Upton, *Newton Polygons of Sums on Curves I* (arXiv:2110.08656v1), build a local-to-global comparison out of a WEIGHT: a function $a(k)$ on pole orders that makes a certain truncated space stable under the Frobenius operator $U_p$. At an auxiliary tame point with $\eta(P) = 1$ their construction needs the weight to satisfy three admissibility conditions, the load-bearing one being $d(k) \ge 1$ for every $k$ above the truncation, where $d(k)$ measures how far the operator moves a term away from the boundary of the truncated space. Their own Remark 6.5 records that at $p = 2$ the estimate they have is "too low for applications to the global setting": the weight they use is not admissible there.

That gap is closed, elementarily, at $p = 2$ with tame ramification index $e = 3$. The transition coefficients $c_{k,j}$ of $U_2$ turn out to be hypergeometric in closed form (Theorem 1); their $2$-adic valuation is then a digit-sum identity (Theorem 2), which yields a tail bound (Lemma A); the weight $a(k) = \lfloor (k-1)/3 \rfloor + (k \bmod 2)$ -- KMU's own weight plus a parity indicator -- satisfies all three admissibility conditions for every $k$ (Theorem 3); and the achievable growth rate is pinned exactly, not bracketed, by a single coefficient (Theorem 4). The arguments are written out in `newton-over-hodge-char2/research-log/04-weight-proof.md` and were re-derived line by line by an adversarial audit in `newton-over-hodge-char2/research-log/20-verify.md`, Part Two.

This page is not a summary of that work: it is the output of a checker. Every number below was read out of one run of a self-checking Rust program that recomputes the coefficients in exact rational arithmetic and asserts each claim over a stated finite range, exiting nonzero if any assertion fails. The run wrote a record; the record carries the SHA-256 of the source that produced it, the command that reproduces it, and its exit status; and the claim badges on this page are computed from that record rather than typed. A separate, deliberately broken copy of the same program is run the same way and its failing record is on this page too, folded away below, so that the machinery which turns evidence into badges can be seen failing as well as passing.

**Claim -- Theorem 3 (the closed-form weight is admissible)** [EVIDENCE]

For $a(k) = 0$ when $k \le 3$ and $a(k) = \lfloor (k-1)/3 \rfloor + (k \bmod 2)$ when $k \ge 4$, KMU's admissibility conditions hold at the tame point with $p = 2$, $e = 3$, $\mu(P) = 3$: (A1) the weight vanishes below the truncation; (A2) it is $O(k)$; and (A3) $d(k) \ge 1$ with the minimum attained at the leading term. Checked over $4 \le k \le 400$ with support $m \le 250$: 397 columns, 0 violations, and 0 columns whose minimum sits anywhere but the leading term.

- Evidence `R:noh-wt-certificate` (primary): 7 of 7 checks of the p = 2 tame-point weight certificate passed; 0 assertion failures. -- `noh_wt_certificate --emit-run render/examples-input/cert/run-certificate.json --source render/producers/noh_wt_certificate_emitrun.rs --record-id R:noh-wt-certificate --replay-seconds 1 --role production` exited 0, 1 input(s) re-hashed.
  - run claim `c5-theorem-3-admissibility` [EVIDENCE]: Theorem 3 (admissibility) for a(k) = 0 (k <= 3), a(k) = floor((k-1)/3) + (k mod 2) (k >= 4): (A1) a(k) = 0 for k <= mu(P) = 3; (A2) 2 a(k) <= k + 6, so a(k) = O(k); (A3) d(k) = min over the computed support of [a(k) - a(j) + v_2(c_{k,j})] is >= 1 for every 4 <= k <= 400, the minimum is attained at the leading term m = 0 for every such k, and d(k) >= 40 once k >= 300.
  - replay: `rustc --edition 2024 -O -o /tmp/noh_wt_cert render/producers/noh_wt_certificate_emitrun.rs && /tmp/noh_wt_cert --emit-run render/examples-input/cert/run-certificate.json --source render/producers/noh_wt_certificate_emitrun.rs --record-id R:noh-wt-certificate --replay-seconds 1 --role production`

A finite sweep, not the proof. The proof -- a three-case parity argument for the tail and a six-case mod-6 identity for the leading term -- is `newton-over-hodge-char2/research-log/04-weight-proof.md` sec. 4, confirmed line by line at `newton-over-hodge-char2/research-log/20-verify.md` P2-3. What the sweep adds is that the argument's conclusion survives contact with the actual numbers over a range no one checked by hand.

**Claim -- Theorem 4 (sharpness: the bound at $k = 6$ is universal)** [EVIDENCE]

$j'(6) + e = 6$, so $k = 6$ lies in its own support and the (A3) constraint there reads $a(6) - a(6) + v_2(c_{6,6}) \ge d(6)$, in which the weight cancels identically. Since $c_{6,6} = 2$ and $v_2(c_{6,6}) = 1$, $d(6) \le 1$ for EVERY admissible weight whatsoever -- not merely for the weight above.

- Evidence `R:noh-wt-certificate` (primary): 7 of 7 checks of the p = 2 tame-point weight certificate passed; 0 assertion failures. -- `noh_wt_certificate --emit-run render/examples-input/cert/run-certificate.json --source render/producers/noh_wt_certificate_emitrun.rs --record-id R:noh-wt-certificate --replay-seconds 1 --role production` exited 0, 1 input(s) re-hashed.
  - run claim `c6-theorem-4-sharpness` [EVIDENCE]: Theorem 4 (sharpness): j'(6) + e = 6, so k = 6 lies in its own support, and the (A3) constraint there reads a(6) - a(6) + v_2(c_{6,6}) >= d(6), in which the weight cancels identically. Since c_{6,6} = 2 and v_2(c_{6,6}) = 1, d(6) <= 1 for EVERY admissible weight whatsoever.
  - replay: `rustc --edition 2024 -O -o /tmp/noh_wt_cert render/producers/noh_wt_certificate_emitrun.rs && /tmp/noh_wt_cert --emit-run render/examples-input/cert/run-certificate.json --source render/producers/noh_wt_certificate_emitrun.rs --record-id R:noh-wt-certificate --replay-seconds 1 --role production`

Two computed facts are asserted here: that $k = 6$ is a self-loop of the support map, and the value of one coefficient's valuation. That a target $d(k) \ge \max(1, \gamma k)$ is therefore achievable if and only if $\gamma \le 1/6$ follows in one line ($6\gamma \le 1$) and is argued at `newton-over-hodge-char2/research-log/04-weight-proof.md` sec. 5; the certificate prints that consequence but does not separately check it. It replaces an interval -- earlier work bracketed the threshold, first in $[1/6, 1/5)$ and then in $[1/6, 2/11)$ -- with a point, and the witness is one coefficient rather than a linear program.

The whole of Theorem 4, in five steps. Every value is read from the run record's statistics; none is transcribed.

0. **least pole order in the image: $j'(k) = k/2$ for even $k$**
   - in: $k = 6$, $p = 2$, $e = 3$
   - out: $j'(6) = 3$
1. **support of $U_2(t^{-6})$ is $j'(6) + e m$, $m \ge 0$**
   - in: $j'(6) = 3$
   - out: $j \in \{3, 6, \ldots\}$ -- and $j'(6) + e = 6 = k$, a self-loop
2. **$3 \mid 6$ terminates the product after one factor**
   - in: closed form of Theorem 1 at $k = 6$
   - out: $U_2(t^{-6}) = 1 \cdot t^{-3} + 2 \cdot t^{-6}$, and $c_{6,9} = 0$
3. **$2$-adic valuation**
   - in: $c_{6,6} = 2$
   - out: $v_2(c_{6,6}) = 1$
4. **the weight cancels; substitute the valuation**
   - in: the (A3) constraint at $(k, j) = (6, 6)$: $a(6) - a(6) + v_2(c_{6,6}) \ge d(6)$
   - out: $d(6) \le 1$ for every weight; for the weight of Theorem 3, $a(6) = 1$, $a(3) = 0$ and $d(6) = 1$, so the bound is attained
   - note: The two tightnesses are complementary: this is the one place Lemma A is tight, and it is exactly where the parity indicator lowers the increment rather than raising it.

<details>
<summary>Table</summary>

$d(k)$ for the weight of Theorem 3, taken from the `d-table` of run record `R:noh-wt-certificate` -- every row of it: the certificate swept $4 \le k \le 400$ (397 columns). No row is copied into this document, so a changed measurement changes this table. `argmin m` is the term of the support at which the minimum is attained -- it is the leading term $m = 0$ in every column.

| k | jprime | a_k | a_jprime | d | argmin_m |
| --- | --- | --- | --- | --- | --- |
| 4 | 2 | 1 | 0 | 1 | 0 |
| 5 | 4 | 2 | 1 | 1 | 0 |
| 6 | 3 | 1 | 0 | 1 | 0 |
| 7 | 5 | 3 | 2 | 1 | 0 |
| 8 | 4 | 2 | 1 | 1 | 0 |
| 9 | 6 | 3 | 1 | 2 | 0 |
| 10 | 5 | 3 | 2 | 1 | 0 |
| 11 | 7 | 4 | 3 | 1 | 0 |
| 12 | 6 | 3 | 1 | 2 | 0 |
| 13 | 8 | 5 | 2 | 3 | 0 |
| 14 | 7 | 4 | 3 | 1 | 0 |
| 15 | 9 | 5 | 3 | 2 | 0 |
| 16 | 8 | 5 | 2 | 3 | 0 |
| 17 | 10 | 6 | 3 | 3 | 0 |
| 18 | 9 | 5 | 3 | 2 | 0 |
| 19 | 11 | 7 | 4 | 3 | 0 |
| 20 | 10 | 6 | 3 | 3 | 0 |
| 21 | 12 | 7 | 3 | 4 | 0 |
| 22 | 11 | 7 | 4 | 3 | 0 |
| 23 | 13 | 8 | 5 | 3 | 0 |
| 24 | 12 | 7 | 3 | 4 | 0 |
| 25 | 14 | 9 | 4 | 5 | 0 |
| 26 | 13 | 8 | 5 | 3 | 0 |
| 27 | 15 | 9 | 5 | 4 | 0 |
| 28 | 14 | 9 | 4 | 5 | 0 |
| 29 | 16 | 10 | 5 | 5 | 0 |
| 30 | 15 | 9 | 5 | 4 | 0 |
| 31 | 17 | 11 | 6 | 5 | 0 |
| 32 | 16 | 10 | 5 | 5 | 0 |
| 33 | 18 | 11 | 5 | 6 | 0 |
| 34 | 17 | 11 | 6 | 5 | 0 |
| 35 | 19 | 12 | 7 | 5 | 0 |
| 36 | 18 | 11 | 5 | 6 | 0 |
| 37 | 20 | 13 | 6 | 7 | 0 |
| 38 | 19 | 12 | 7 | 5 | 0 |
| 39 | 21 | 13 | 7 | 6 | 0 |
| 40 | 20 | 13 | 6 | 7 | 0 |
| 41 | 22 | 14 | 7 | 7 | 0 |
| 42 | 21 | 13 | 7 | 6 | 0 |
| 43 | 23 | 15 | 8 | 7 | 0 |
| 44 | 22 | 14 | 7 | 7 | 0 |
| 45 | 24 | 15 | 7 | 8 | 0 |
| 46 | 23 | 15 | 8 | 7 | 0 |
| 47 | 25 | 16 | 9 | 7 | 0 |
| 48 | 24 | 15 | 7 | 8 | 0 |
| 49 | 26 | 17 | 8 | 9 | 0 |
| 50 | 25 | 16 | 9 | 7 | 0 |
| 51 | 27 | 17 | 9 | 8 | 0 |
| 52 | 26 | 17 | 8 | 9 | 0 |
| 53 | 28 | 18 | 9 | 9 | 0 |
| 54 | 27 | 17 | 9 | 8 | 0 |
| 55 | 29 | 19 | 10 | 9 | 0 |
| 56 | 28 | 18 | 9 | 9 | 0 |
| 57 | 30 | 19 | 9 | 10 | 0 |
| 58 | 29 | 19 | 10 | 9 | 0 |
| 59 | 31 | 20 | 11 | 9 | 0 |
| 60 | 30 | 19 | 9 | 10 | 0 |
| 61 | 32 | 21 | 10 | 11 | 0 |
| 62 | 31 | 20 | 11 | 9 | 0 |
| 63 | 33 | 21 | 11 | 10 | 0 |
| 64 | 32 | 21 | 10 | 11 | 0 |
| 65 | 34 | 22 | 11 | 11 | 0 |
| 66 | 33 | 21 | 11 | 10 | 0 |
| 67 | 35 | 23 | 12 | 11 | 0 |
| 68 | 34 | 22 | 11 | 11 | 0 |
| 69 | 36 | 23 | 11 | 12 | 0 |
| 70 | 35 | 23 | 12 | 11 | 0 |
| 71 | 37 | 24 | 13 | 11 | 0 |
| 72 | 36 | 23 | 11 | 12 | 0 |
| 73 | 38 | 25 | 12 | 13 | 0 |
| 74 | 37 | 24 | 13 | 11 | 0 |
| 75 | 39 | 25 | 13 | 12 | 0 |
| 76 | 38 | 25 | 12 | 13 | 0 |
| 77 | 40 | 26 | 13 | 13 | 0 |
| 78 | 39 | 25 | 13 | 12 | 0 |
| 79 | 41 | 27 | 14 | 13 | 0 |
| 80 | 40 | 26 | 13 | 13 | 0 |
| 81 | 42 | 27 | 13 | 14 | 0 |
| 82 | 41 | 27 | 14 | 13 | 0 |
| 83 | 43 | 28 | 15 | 13 | 0 |
| 84 | 42 | 27 | 13 | 14 | 0 |
| 85 | 44 | 29 | 14 | 15 | 0 |
| 86 | 43 | 28 | 15 | 13 | 0 |
| 87 | 45 | 29 | 15 | 14 | 0 |
| 88 | 44 | 29 | 14 | 15 | 0 |
| 89 | 46 | 30 | 15 | 15 | 0 |
| 90 | 45 | 29 | 15 | 14 | 0 |
| 91 | 47 | 31 | 16 | 15 | 0 |
| 92 | 46 | 30 | 15 | 15 | 0 |
| 93 | 48 | 31 | 15 | 16 | 0 |
| 94 | 47 | 31 | 16 | 15 | 0 |
| 95 | 49 | 32 | 17 | 15 | 0 |
| 96 | 48 | 31 | 15 | 16 | 0 |
| 97 | 50 | 33 | 16 | 17 | 0 |
| 98 | 49 | 32 | 17 | 15 | 0 |
| 99 | 51 | 33 | 17 | 16 | 0 |
| 100 | 50 | 33 | 16 | 17 | 0 |
| 101 | 52 | 34 | 17 | 17 | 0 |
| 102 | 51 | 33 | 17 | 16 | 0 |
| 103 | 53 | 35 | 18 | 17 | 0 |
| 104 | 52 | 34 | 17 | 17 | 0 |
| 105 | 54 | 35 | 17 | 18 | 0 |
| 106 | 53 | 35 | 18 | 17 | 0 |
| 107 | 55 | 36 | 19 | 17 | 0 |
| 108 | 54 | 35 | 17 | 18 | 0 |
| 109 | 56 | 37 | 18 | 19 | 0 |
| 110 | 55 | 36 | 19 | 17 | 0 |
| 111 | 57 | 37 | 19 | 18 | 0 |
| 112 | 56 | 37 | 18 | 19 | 0 |
| 113 | 58 | 38 | 19 | 19 | 0 |
| 114 | 57 | 37 | 19 | 18 | 0 |
| 115 | 59 | 39 | 20 | 19 | 0 |
| 116 | 58 | 38 | 19 | 19 | 0 |
| 117 | 60 | 39 | 19 | 20 | 0 |
| 118 | 59 | 39 | 20 | 19 | 0 |
| 119 | 61 | 40 | 21 | 19 | 0 |
| 120 | 60 | 39 | 19 | 20 | 0 |
| 121 | 62 | 41 | 20 | 21 | 0 |
| 122 | 61 | 40 | 21 | 19 | 0 |
| 123 | 63 | 41 | 21 | 20 | 0 |
| 124 | 62 | 41 | 20 | 21 | 0 |
| 125 | 64 | 42 | 21 | 21 | 0 |
| 126 | 63 | 41 | 21 | 20 | 0 |
| 127 | 65 | 43 | 22 | 21 | 0 |
| 128 | 64 | 42 | 21 | 21 | 0 |
| 129 | 66 | 43 | 21 | 22 | 0 |
| 130 | 65 | 43 | 22 | 21 | 0 |
| 131 | 67 | 44 | 23 | 21 | 0 |
| 132 | 66 | 43 | 21 | 22 | 0 |
| 133 | 68 | 45 | 22 | 23 | 0 |
| 134 | 67 | 44 | 23 | 21 | 0 |
| 135 | 69 | 45 | 23 | 22 | 0 |
| 136 | 68 | 45 | 22 | 23 | 0 |
| 137 | 70 | 46 | 23 | 23 | 0 |
| 138 | 69 | 45 | 23 | 22 | 0 |
| 139 | 71 | 47 | 24 | 23 | 0 |
| 140 | 70 | 46 | 23 | 23 | 0 |
| 141 | 72 | 47 | 23 | 24 | 0 |
| 142 | 71 | 47 | 24 | 23 | 0 |
| 143 | 73 | 48 | 25 | 23 | 0 |
| 144 | 72 | 47 | 23 | 24 | 0 |
| 145 | 74 | 49 | 24 | 25 | 0 |
| 146 | 73 | 48 | 25 | 23 | 0 |
| 147 | 75 | 49 | 25 | 24 | 0 |
| 148 | 74 | 49 | 24 | 25 | 0 |
| 149 | 76 | 50 | 25 | 25 | 0 |
| 150 | 75 | 49 | 25 | 24 | 0 |
| 151 | 77 | 51 | 26 | 25 | 0 |
| 152 | 76 | 50 | 25 | 25 | 0 |
| 153 | 78 | 51 | 25 | 26 | 0 |
| 154 | 77 | 51 | 26 | 25 | 0 |
| 155 | 79 | 52 | 27 | 25 | 0 |
| 156 | 78 | 51 | 25 | 26 | 0 |
| 157 | 80 | 53 | 26 | 27 | 0 |
| 158 | 79 | 52 | 27 | 25 | 0 |
| 159 | 81 | 53 | 27 | 26 | 0 |
| 160 | 80 | 53 | 26 | 27 | 0 |
| 161 | 82 | 54 | 27 | 27 | 0 |
| 162 | 81 | 53 | 27 | 26 | 0 |
| 163 | 83 | 55 | 28 | 27 | 0 |
| 164 | 82 | 54 | 27 | 27 | 0 |
| 165 | 84 | 55 | 27 | 28 | 0 |
| 166 | 83 | 55 | 28 | 27 | 0 |
| 167 | 85 | 56 | 29 | 27 | 0 |
| 168 | 84 | 55 | 27 | 28 | 0 |
| 169 | 86 | 57 | 28 | 29 | 0 |
| 170 | 85 | 56 | 29 | 27 | 0 |
| 171 | 87 | 57 | 29 | 28 | 0 |
| 172 | 86 | 57 | 28 | 29 | 0 |
| 173 | 88 | 58 | 29 | 29 | 0 |
| 174 | 87 | 57 | 29 | 28 | 0 |
| 175 | 89 | 59 | 30 | 29 | 0 |
| 176 | 88 | 58 | 29 | 29 | 0 |
| 177 | 90 | 59 | 29 | 30 | 0 |
| 178 | 89 | 59 | 30 | 29 | 0 |
| 179 | 91 | 60 | 31 | 29 | 0 |
| 180 | 90 | 59 | 29 | 30 | 0 |
| 181 | 92 | 61 | 30 | 31 | 0 |
| 182 | 91 | 60 | 31 | 29 | 0 |
| 183 | 93 | 61 | 31 | 30 | 0 |
| 184 | 92 | 61 | 30 | 31 | 0 |
| 185 | 94 | 62 | 31 | 31 | 0 |
| 186 | 93 | 61 | 31 | 30 | 0 |
| 187 | 95 | 63 | 32 | 31 | 0 |
| 188 | 94 | 62 | 31 | 31 | 0 |
| 189 | 96 | 63 | 31 | 32 | 0 |
| 190 | 95 | 63 | 32 | 31 | 0 |
| 191 | 97 | 64 | 33 | 31 | 0 |
| 192 | 96 | 63 | 31 | 32 | 0 |
| 193 | 98 | 65 | 32 | 33 | 0 |
| 194 | 97 | 64 | 33 | 31 | 0 |
| 195 | 99 | 65 | 33 | 32 | 0 |
| 196 | 98 | 65 | 32 | 33 | 0 |
| 197 | 100 | 66 | 33 | 33 | 0 |
| 198 | 99 | 65 | 33 | 32 | 0 |
| 199 | 101 | 67 | 34 | 33 | 0 |
| 200 | 100 | 66 | 33 | 33 | 0 |
| 201 | 102 | 67 | 33 | 34 | 0 |
| 202 | 101 | 67 | 34 | 33 | 0 |
| 203 | 103 | 68 | 35 | 33 | 0 |
| 204 | 102 | 67 | 33 | 34 | 0 |
| 205 | 104 | 69 | 34 | 35 | 0 |
| 206 | 103 | 68 | 35 | 33 | 0 |
| 207 | 105 | 69 | 35 | 34 | 0 |
| 208 | 104 | 69 | 34 | 35 | 0 |
| 209 | 106 | 70 | 35 | 35 | 0 |
| 210 | 105 | 69 | 35 | 34 | 0 |
| 211 | 107 | 71 | 36 | 35 | 0 |
| 212 | 106 | 70 | 35 | 35 | 0 |
| 213 | 108 | 71 | 35 | 36 | 0 |
| 214 | 107 | 71 | 36 | 35 | 0 |
| 215 | 109 | 72 | 37 | 35 | 0 |
| 216 | 108 | 71 | 35 | 36 | 0 |
| 217 | 110 | 73 | 36 | 37 | 0 |
| 218 | 109 | 72 | 37 | 35 | 0 |
| 219 | 111 | 73 | 37 | 36 | 0 |
| 220 | 110 | 73 | 36 | 37 | 0 |
| 221 | 112 | 74 | 37 | 37 | 0 |
| 222 | 111 | 73 | 37 | 36 | 0 |
| 223 | 113 | 75 | 38 | 37 | 0 |
| 224 | 112 | 74 | 37 | 37 | 0 |
| 225 | 114 | 75 | 37 | 38 | 0 |
| 226 | 113 | 75 | 38 | 37 | 0 |
| 227 | 115 | 76 | 39 | 37 | 0 |
| 228 | 114 | 75 | 37 | 38 | 0 |
| 229 | 116 | 77 | 38 | 39 | 0 |
| 230 | 115 | 76 | 39 | 37 | 0 |
| 231 | 117 | 77 | 39 | 38 | 0 |
| 232 | 116 | 77 | 38 | 39 | 0 |
| 233 | 118 | 78 | 39 | 39 | 0 |
| 234 | 117 | 77 | 39 | 38 | 0 |
| 235 | 119 | 79 | 40 | 39 | 0 |
| 236 | 118 | 78 | 39 | 39 | 0 |
| 237 | 120 | 79 | 39 | 40 | 0 |
| 238 | 119 | 79 | 40 | 39 | 0 |
| 239 | 121 | 80 | 41 | 39 | 0 |
| 240 | 120 | 79 | 39 | 40 | 0 |
| 241 | 122 | 81 | 40 | 41 | 0 |
| 242 | 121 | 80 | 41 | 39 | 0 |
| 243 | 123 | 81 | 41 | 40 | 0 |
| 244 | 122 | 81 | 40 | 41 | 0 |
| 245 | 124 | 82 | 41 | 41 | 0 |
| 246 | 123 | 81 | 41 | 40 | 0 |
| 247 | 125 | 83 | 42 | 41 | 0 |
| 248 | 124 | 82 | 41 | 41 | 0 |
| 249 | 126 | 83 | 41 | 42 | 0 |
| 250 | 125 | 83 | 42 | 41 | 0 |
| 251 | 127 | 84 | 43 | 41 | 0 |
| 252 | 126 | 83 | 41 | 42 | 0 |
| 253 | 128 | 85 | 42 | 43 | 0 |
| 254 | 127 | 84 | 43 | 41 | 0 |
| 255 | 129 | 85 | 43 | 42 | 0 |
| 256 | 128 | 85 | 42 | 43 | 0 |
| 257 | 130 | 86 | 43 | 43 | 0 |
| 258 | 129 | 85 | 43 | 42 | 0 |
| 259 | 131 | 87 | 44 | 43 | 0 |
| 260 | 130 | 86 | 43 | 43 | 0 |
| 261 | 132 | 87 | 43 | 44 | 0 |
| 262 | 131 | 87 | 44 | 43 | 0 |
| 263 | 133 | 88 | 45 | 43 | 0 |
| 264 | 132 | 87 | 43 | 44 | 0 |
| 265 | 134 | 89 | 44 | 45 | 0 |
| 266 | 133 | 88 | 45 | 43 | 0 |
| 267 | 135 | 89 | 45 | 44 | 0 |
| 268 | 134 | 89 | 44 | 45 | 0 |
| 269 | 136 | 90 | 45 | 45 | 0 |
| 270 | 135 | 89 | 45 | 44 | 0 |
| 271 | 137 | 91 | 46 | 45 | 0 |
| 272 | 136 | 90 | 45 | 45 | 0 |
| 273 | 138 | 91 | 45 | 46 | 0 |
| 274 | 137 | 91 | 46 | 45 | 0 |
| 275 | 139 | 92 | 47 | 45 | 0 |
| 276 | 138 | 91 | 45 | 46 | 0 |
| 277 | 140 | 93 | 46 | 47 | 0 |
| 278 | 139 | 92 | 47 | 45 | 0 |
| 279 | 141 | 93 | 47 | 46 | 0 |
| 280 | 140 | 93 | 46 | 47 | 0 |
| 281 | 142 | 94 | 47 | 47 | 0 |
| 282 | 141 | 93 | 47 | 46 | 0 |
| 283 | 143 | 95 | 48 | 47 | 0 |
| 284 | 142 | 94 | 47 | 47 | 0 |
| 285 | 144 | 95 | 47 | 48 | 0 |
| 286 | 143 | 95 | 48 | 47 | 0 |
| 287 | 145 | 96 | 49 | 47 | 0 |
| 288 | 144 | 95 | 47 | 48 | 0 |
| 289 | 146 | 97 | 48 | 49 | 0 |
| 290 | 145 | 96 | 49 | 47 | 0 |
| 291 | 147 | 97 | 49 | 48 | 0 |
| 292 | 146 | 97 | 48 | 49 | 0 |
| 293 | 148 | 98 | 49 | 49 | 0 |
| 294 | 147 | 97 | 49 | 48 | 0 |
| 295 | 149 | 99 | 50 | 49 | 0 |
| 296 | 148 | 98 | 49 | 49 | 0 |
| 297 | 150 | 99 | 49 | 50 | 0 |
| 298 | 149 | 99 | 50 | 49 | 0 |
| 299 | 151 | 100 | 51 | 49 | 0 |
| 300 | 150 | 99 | 49 | 50 | 0 |
| 301 | 152 | 101 | 50 | 51 | 0 |
| 302 | 151 | 100 | 51 | 49 | 0 |
| 303 | 153 | 101 | 51 | 50 | 0 |
| 304 | 152 | 101 | 50 | 51 | 0 |
| 305 | 154 | 102 | 51 | 51 | 0 |
| 306 | 153 | 101 | 51 | 50 | 0 |
| 307 | 155 | 103 | 52 | 51 | 0 |
| 308 | 154 | 102 | 51 | 51 | 0 |
| 309 | 156 | 103 | 51 | 52 | 0 |
| 310 | 155 | 103 | 52 | 51 | 0 |
| 311 | 157 | 104 | 53 | 51 | 0 |
| 312 | 156 | 103 | 51 | 52 | 0 |
| 313 | 158 | 105 | 52 | 53 | 0 |
| 314 | 157 | 104 | 53 | 51 | 0 |
| 315 | 159 | 105 | 53 | 52 | 0 |
| 316 | 158 | 105 | 52 | 53 | 0 |
| 317 | 160 | 106 | 53 | 53 | 0 |
| 318 | 159 | 105 | 53 | 52 | 0 |
| 319 | 161 | 107 | 54 | 53 | 0 |
| 320 | 160 | 106 | 53 | 53 | 0 |
| 321 | 162 | 107 | 53 | 54 | 0 |
| 322 | 161 | 107 | 54 | 53 | 0 |
| 323 | 163 | 108 | 55 | 53 | 0 |
| 324 | 162 | 107 | 53 | 54 | 0 |
| 325 | 164 | 109 | 54 | 55 | 0 |
| 326 | 163 | 108 | 55 | 53 | 0 |
| 327 | 165 | 109 | 55 | 54 | 0 |
| 328 | 164 | 109 | 54 | 55 | 0 |
| 329 | 166 | 110 | 55 | 55 | 0 |
| 330 | 165 | 109 | 55 | 54 | 0 |
| 331 | 167 | 111 | 56 | 55 | 0 |
| 332 | 166 | 110 | 55 | 55 | 0 |
| 333 | 168 | 111 | 55 | 56 | 0 |
| 334 | 167 | 111 | 56 | 55 | 0 |
| 335 | 169 | 112 | 57 | 55 | 0 |
| 336 | 168 | 111 | 55 | 56 | 0 |
| 337 | 170 | 113 | 56 | 57 | 0 |
| 338 | 169 | 112 | 57 | 55 | 0 |
| 339 | 171 | 113 | 57 | 56 | 0 |
| 340 | 170 | 113 | 56 | 57 | 0 |
| 341 | 172 | 114 | 57 | 57 | 0 |
| 342 | 171 | 113 | 57 | 56 | 0 |
| 343 | 173 | 115 | 58 | 57 | 0 |
| 344 | 172 | 114 | 57 | 57 | 0 |
| 345 | 174 | 115 | 57 | 58 | 0 |
| 346 | 173 | 115 | 58 | 57 | 0 |
| 347 | 175 | 116 | 59 | 57 | 0 |
| 348 | 174 | 115 | 57 | 58 | 0 |
| 349 | 176 | 117 | 58 | 59 | 0 |
| 350 | 175 | 116 | 59 | 57 | 0 |
| 351 | 177 | 117 | 59 | 58 | 0 |
| 352 | 176 | 117 | 58 | 59 | 0 |
| 353 | 178 | 118 | 59 | 59 | 0 |
| 354 | 177 | 117 | 59 | 58 | 0 |
| 355 | 179 | 119 | 60 | 59 | 0 |
| 356 | 178 | 118 | 59 | 59 | 0 |
| 357 | 180 | 119 | 59 | 60 | 0 |
| 358 | 179 | 119 | 60 | 59 | 0 |
| 359 | 181 | 120 | 61 | 59 | 0 |
| 360 | 180 | 119 | 59 | 60 | 0 |
| 361 | 182 | 121 | 60 | 61 | 0 |
| 362 | 181 | 120 | 61 | 59 | 0 |
| 363 | 183 | 121 | 61 | 60 | 0 |
| 364 | 182 | 121 | 60 | 61 | 0 |
| 365 | 184 | 122 | 61 | 61 | 0 |
| 366 | 183 | 121 | 61 | 60 | 0 |
| 367 | 185 | 123 | 62 | 61 | 0 |
| 368 | 184 | 122 | 61 | 61 | 0 |
| 369 | 186 | 123 | 61 | 62 | 0 |
| 370 | 185 | 123 | 62 | 61 | 0 |
| 371 | 187 | 124 | 63 | 61 | 0 |
| 372 | 186 | 123 | 61 | 62 | 0 |
| 373 | 188 | 125 | 62 | 63 | 0 |
| 374 | 187 | 124 | 63 | 61 | 0 |
| 375 | 189 | 125 | 63 | 62 | 0 |
| 376 | 188 | 125 | 62 | 63 | 0 |
| 377 | 190 | 126 | 63 | 63 | 0 |
| 378 | 189 | 125 | 63 | 62 | 0 |
| 379 | 191 | 127 | 64 | 63 | 0 |
| 380 | 190 | 126 | 63 | 63 | 0 |
| 381 | 192 | 127 | 63 | 64 | 0 |
| 382 | 191 | 127 | 64 | 63 | 0 |
| 383 | 193 | 128 | 65 | 63 | 0 |
| 384 | 192 | 127 | 63 | 64 | 0 |
| 385 | 194 | 129 | 64 | 65 | 0 |
| 386 | 193 | 128 | 65 | 63 | 0 |
| 387 | 195 | 129 | 65 | 64 | 0 |
| 388 | 194 | 129 | 64 | 65 | 0 |
| 389 | 196 | 130 | 65 | 65 | 0 |
| 390 | 195 | 129 | 65 | 64 | 0 |
| 391 | 197 | 131 | 66 | 65 | 0 |
| 392 | 196 | 130 | 65 | 65 | 0 |
| 393 | 198 | 131 | 65 | 66 | 0 |
| 394 | 197 | 131 | 66 | 65 | 0 |
| 395 | 199 | 132 | 67 | 65 | 0 |
| 396 | 198 | 131 | 65 | 66 | 0 |
| 397 | 200 | 133 | 66 | 67 | 0 |
| 398 | 199 | 132 | 67 | 65 | 0 |
| 399 | 201 | 133 | 67 | 66 | 0 |
| 400 | 200 | 133 | 66 | 67 | 0 |

Source: `noh_wt_certificate --emit-run render/examples-input/cert/run-certificate.json --source render/producers/noh_wt_certificate_emitrun.rs --record-id R:noh-wt-certificate --replay-seconds 1 --role production` (exit 0), 1 input(s) hashed.

</details>

*Figure (Two step plots against pole order k. The upper series, the weight a(k), rises in a sawtooth staircase. The lower series, the slack d(k), rises on average but repeatedly returns to 1, its universal floor.) -- data:*

```json
{
  "figure_type": "plot",
  "plot_type": "steps",
  "series": [
    {
      "label": "a(k), the weight",
      "points": [
        [
          1.0,
          0.0
        ],
        [
          2.0,
          0.0
        ],
        [
          3.0,
          0.0
        ],
        [
          4.0,
          1.0
        ],
        [
          5.0,
          2.0
        ],
        [
          6.0,
          1.0
        ],
        [
          7.0,
          3.0
        ],
        [
          8.0,
          2.0
        ],
        [
          9.0,
          3.0
        ],
        [
          10.0,
          3.0
        ],
        [
          11.0,
          4.0
        ],
        [
          12.0,
          3.0
        ],
        [
          13.0,
          5.0
        ],
        [
          14.0,
          4.0
        ],
        [
          15.0,
          5.0
        ],
        [
          16.0,
          5.0
        ],
        [
          17.0,
          6.0
        ],
        [
          18.0,
          5.0
        ],
        [
          19.0,
          7.0
        ],
        [
          20.0,
          6.0
        ],
        [
          21.0,
          7.0
        ],
        [
          22.0,
          7.0
        ],
        [
          23.0,
          8.0
        ],
        [
          24.0,
          7.0
        ],
        [
          25.0,
          9.0
        ],
        [
          26.0,
          8.0
        ],
        [
          27.0,
          9.0
        ],
        [
          28.0,
          9.0
        ],
        [
          29.0,
          10.0
        ],
        [
          30.0,
          9.0
        ],
        [
          31.0,
          11.0
        ],
        [
          32.0,
          10.0
        ],
        [
          33.0,
          11.0
        ],
        [
          34.0,
          11.0
        ],
        [
          35.0,
          12.0
        ],
        [
          36.0,
          11.0
        ],
        [
          37.0,
          13.0
        ],
        [
          38.0,
          12.0
        ],
        [
          39.0,
          13.0
        ],
        [
          40.0,
          13.0
        ],
        [
          41.0,
          14.0
        ],
        [
          42.0,
          13.0
        ],
        [
          43.0,
          15.0
        ],
        [
          44.0,
          14.0
        ],
        [
          45.0,
          15.0
        ],
        [
          46.0,
          15.0
        ],
        [
          47.0,
          16.0
        ],
        [
          48.0,
          15.0
        ]
      ],
      "style": "weight"
    },
    {
      "label": "d(k), the admissibility slack",
      "points": [
        [
          4.0,
          1.0
        ],
        [
          5.0,
          1.0
        ],
        [
          6.0,
          1.0
        ],
        [
          7.0,
          1.0
        ],
        [
          8.0,
          1.0
        ],
        [
          9.0,
          2.0
        ],
        [
          10.0,
          1.0
        ],
        [
          11.0,
          1.0
        ],
        [
          12.0,
          2.0
        ],
        [
          13.0,
          3.0
        ],
        [
          14.0,
          1.0
        ],
        [
          15.0,
          2.0
        ],
        [
          16.0,
          3.0
        ],
        [
          17.0,
          3.0
        ],
        [
          18.0,
          2.0
        ],
        [
          19.0,
          3.0
        ],
        [
          20.0,
          3.0
        ],
        [
          21.0,
          4.0
        ],
        [
          22.0,
          3.0
        ],
        [
          23.0,
          3.0
        ],
        [
          24.0,
          4.0
        ],
        [
          25.0,
          5.0
        ],
        [
          26.0,
          3.0
        ],
        [
          27.0,
          4.0
        ],
        [
          28.0,
          5.0
        ],
        [
          29.0,
          5.0
        ],
        [
          30.0,
          4.0
        ],
        [
          31.0,
          5.0
        ],
        [
          32.0,
          5.0
        ],
        [
          33.0,
          6.0
        ],
        [
          34.0,
          5.0
        ],
        [
          35.0,
          5.0
        ],
        [
          36.0,
          6.0
        ],
        [
          37.0,
          7.0
        ],
        [
          38.0,
          5.0
        ],
        [
          39.0,
          6.0
        ],
        [
          40.0,
          7.0
        ],
        [
          41.0,
          7.0
        ],
        [
          42.0,
          6.0
        ],
        [
          43.0,
          7.0
        ],
        [
          44.0,
          7.0
        ],
        [
          45.0,
          8.0
        ],
        [
          46.0,
          7.0
        ],
        [
          47.0,
          7.0
        ],
        [
          48.0,
          8.0
        ]
      ],
      "style": "slack"
    }
  ],
  "x_label": "pole order k",
  "y_label": "value"
}
```

*The weight $a(k)$ and the slack $d(k)$ it buys, over the first 48 pole orders. $a(k)$ is a staircase of slope $1/3$ with a parity indicator riding on it; $d(k)$ is the distance from the boundary of the truncated space, and the flat line at $d = 1$ that it keeps returning to is why the growth rate cannot exceed $k/6$.*

**Certificate -- report run**

7 of 7 checks of the p = 2 tame-point weight certificate passed; 0 assertion failures. The program is dependency-free and builds with a bare `rustc --edition 2024`, so the replay below needs no cargo, no workspace and no network. It is mutation-tested: all seven mutants in the paper repository's suite exit nonzero against this source, each with the catcher its `.expect` file records.

Artifacts:

- [run record](https://github.com/mjbommar/axeyum/blob/75663ef85c2dad4390a3b6d77361919a914642a9/render/examples-input/cert/run-certificate.json)
- [producer source](https://github.com/mjbommar/axeyum/blob/75663ef85c2dad4390a3b6d77361919a914642a9/render/producers/noh_wt_certificate_emitrun.rs)

Replay:

```sh
rustc --edition 2024 -O -o /tmp/noh_wt_cert render/producers/noh_wt_certificate_emitrun.rs && /tmp/noh_wt_cert --emit-run render/examples-input/cert/run-certificate.json --source render/producers/noh_wt_certificate_emitrun.rs --record-id R:noh-wt-certificate --replay-seconds 1 --role production
```

- Evidence `R:noh-wt-certificate` (primary): 7 of 7 checks of the p = 2 tame-point weight certificate passed; 0 assertion failures. -- `noh_wt_certificate --emit-run render/examples-input/cert/run-certificate.json --source render/producers/noh_wt_certificate_emitrun.rs --record-id R:noh-wt-certificate --replay-seconds 1 --role production` exited 0, 1 input(s) re-hashed.
  - replay: `rustc --edition 2024 -O -o /tmp/noh_wt_cert render/producers/noh_wt_certificate_emitrun.rs && /tmp/noh_wt_cert --emit-run render/examples-input/cert/run-certificate.json --source render/producers/noh_wt_certificate_emitrun.rs --record-id R:noh-wt-certificate --replay-seconds 1 --role production`

<details>
<summary>What the certificate binds, and what it does not</summary>

**What the certificate does and does not bind.** Its check [1] compares the closed-form product against a coefficient obtained by iterating the recurrence forced by the hypergeometric ODE, and the file originally called that an INDEPENDENT route. It is not one: the audit (`newton-over-hodge-char2/research-log/20-verify.md`, P2-8) established that the second route iterates the same product in a different association order, so check [1] verifies exact rational arithmetic and not the operator. The certificate's only binding to $U_2$ itself is the block of hard-coded coefficient rows recomputed independently by workstream 01 -- claim `c2` in the run record. Everything downstream (the valuation identity, Lemma A, the admissibility sweep, the sharpness witness) is arithmetic over the closed form that block pins. Widening that binding, by adding the series solve to the artifact, is the audit's open recommendation and is not done here.

</details>

*Archived -- [render/examples-input/cert/run-certificate.json](https://github.com/mjbommar/axeyum/blob/75663ef85c2dad4390a3b6d77361919a914642a9/render/examples-input/cert/run-certificate.json) (not shown here).*

*Archived -- [render/producers/noh_wt_certificate_emitrun.rs](https://github.com/mjbommar/axeyum/blob/75663ef85c2dad4390a3b6d77361919a914642a9/render/producers/noh_wt_certificate_emitrun.rs) (not shown here).*

---

Rendered from Doc-IR by `axeyum-render`. Epoch 1787307950 (2026-08-21T10:25:50Z, source `commit`), commit `75663ef85c2dad4390a3b6d77361919a914642a9`.
