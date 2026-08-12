# Route A lab notebook — proving the shell colouring solution-free

Append-only. Corrections are appended, never edited in place.

Author: Route-A agent. Task: prove that the shell colouring of `[1, N_shell(a,b,k)]`
contains no monochromatic solution of `a(x-y) = bz`, and prove the sharpness of
the hypothesis `b < a`.

---

## 2026-08-12T19:06:04-04:00 — NOTICE about the first three entries

The instruction to keep this notebook arrived after I had already done the
initial derivation and the first two computational runs. Entries
`[E1]`–`[E3]` below are therefore **back-filled within the same session**, from
my own working notes and from the scripts and outputs that are still on disk
(`shell.py`, `verify_bruteforce.py`, and the two runs quoted verbatim). I am
flagging this rather than presenting them as contemporaneous. Everything from
`[E4]` onward is written as it happens.

---

## [E1] Setup and first derivation (back-filled, ~19:00)

Read `PROOF-BRIEF.md`. Transcribed the construction into `shell.py` as
*definitions only* — no claims — so that every later claim is checked against a
single transcription rather than against my memory of the brief.

Notation fixed for the whole session:

- `v(j)` = a-adic valuation, `v(j) = 0` for units.
- `L_i = a^{i-1} b` (i = 2..k), `N = 2(L_2+...+L_{k-1}) + L_k`.
- `c_1 = 0`, `c_i = c_{i-1} + L_i` (i = 2..k-1). I immediately conjectured the
  closed forms `c_i = b S_{i-1}` and `N = b(a^{k-1} + 2 S_{k-2})` where
  `S_m = a + a^2 + ... + a^m`; both were later checked (see `[E5]`).
- `V_i` = valuation stratum, `shell_i` = the two-sided unit shell
  `[c_{i-1}+1, c_i] ∪ [N-c_i+1, N-c_{i-1}]`, `core` = the rest.

**Decision point 1 — what drives the case split.** Two candidates:

(a) split on the *positions* of x and y (which shell/core interval), or
(b) split on the *common colour* c and then on the type (multiple-of-a vs unit)
    of each of x and y.

I chose (b). Reason: `z = at` forces `a | z`, so `chi(z) = min(v(z), k)` *always*
— the colour of the solution is pinned by the valuation of `t` alone, with no
reference to position. That turns `c` into a hypothesis about `v(t)`:

- `c <= k-1`  =>  `v(z) = c`  =>  `v(t) = c - 1` exactly;
- `c = k`     =>  `v(z) >= k` =>  `v(t) >= k - 1`.

This is the whole engine. Route (a) has no comparable pin.

**Consequence I noticed immediately and used everywhere:** the *mixed* branches
(x a multiple of a, y a unit, or vice versa) die on valuation alone, with no
inequality: `v(x-y) = min(v(x), v(y)) = 0` when exactly one of them is a unit,
but `v(x-y) = v(bt) = v(t) >= 1` in every case with `c >= 2`. That kills 4 of
the 9 leaves of the case tree instantly. Confidence: high, this is elementary.

## [E2] The case tree as first written down (back-filled)

Solution form (Lemma 1, given in the brief and re-derived): `gcd(a,b) = 1`,
`a(x-y) = bz` => `a | bz` => `a | z`, write `z = at`, then `x - y = bt`, `t >= 1`.

Assume `chi(x) = chi(y) = chi(z) = c`.

- **c = 1.** Colour 1 contains *only* multiples of a with `v = 1` (shells are
  indexed 2..k-1, core is coloured k), so `v(x) = v(y) = 1`, hence `a | x-y`,
  hence `v(t) = v(bt) = v(x-y) >= 1`. But `c = 1` gives `v(z) = 1`, i.e.
  `v(t) = 0`. Contradiction. **Uses only gcd(a,b)=1.** No size hypothesis.
- **2 <= c <= k-1**, four leaves:
  - both `v = c`: `a^c | x-y` so `v(t) >= c`, but `v(t) = c-1`. Contradiction.
  - mixed: valuation, as in [E1].
  - both units in the *same* interval of shell_c: `|x-y| <= L_c - 1`, but
    `x-y = b a^{c-1} s >= L_c`. Contradiction.
  - both units in *opposite* intervals of shell_c: **this is the only hard
    leaf.** Needs an inequality. See [E3].
- **c = k**, three leaves:
  - both `v >= k`: `a^k | x` and `a^k | y`, so `x >= y + a^k >= 2a^k`; need
    `N < 2a^k`.
  - mixed: valuation.
  - both units in the core: core width is exactly `L_k = b a^{k-1}`, so
    `|x-y| <= L_k - 1`, but `v(t) >= k-1` gives `x-y = bt >= b a^{k-1} = L_k`.
    Contradiction.

At this point the proof was complete except for the one hard leaf and the
`N < 2a^k` bound.

## [E3] FAILED ATTEMPT — the naive inequality for the hard leaf (back-filled)

**Conjecture A (FALSE).** In the cross leaf, `x` is in the right interval and
`y` in the left, so `x - y >= N - 2c_c + 1`; and `z = at <= N` with
`x-y = (b/a) z` gives `x - y <= (b/a) N`. So it should suffice that
`N - 2c_c + 1 > (b/a) N`, i.e. `N(a-b) > 2 a b S_{c-1}`.

**Refuted by hand, then confirmed numerically.** With `b <= a-1` we have
`N(a-b) >= N`, and one computes

    2 a b S_{k-2} - N = a b (a^{k-2} - 2),

which is **positive** for all `a >= 2, k >= 4`. So Conjecture A is false for
every `k >= 4`. Concrete witness: `(a,b,k) = (3,2,4)`: `N = 102`,
`N(a-b) = 102`, `2 a b S_2 = 2*3*2*(3+9) = 144`. 102 < 144.

**Why it fails and what fixes it.** The real-number bound `x-y <= (b/a) N`
throws away integrality. The quantity that is actually integral is
`s = t / a^{c-1}`, and `s <= floor(N / a^c)`. Recovering the floor is worth a
factor that is exactly enough. At `(3,2,4), c=3`: real bound gives `s <= 3.77`,
but `s <= 3`, and `x-y = 18s <= 54 < 55 = N - 2c_3 + 1`. Closes.

**Decision point 2.** I kept the floor version (Lemma 4 below) rather than
trying to repair Conjecture A with a smarter real bound. Reason: the floor
version has a two-line proof once `N` is split along `a^c`, and it is *exactly*
tight in the sense that the same statement is what fails when `b > a` — so it
is the right statement to isolate, because it doubles as the sharpness engine.

**Lemma 4 (shell gap), as finally stated.** Let `a >= 2`, `1 <= b <= a-1`,
`2 <= c <= k-1`. Then for every integer `s >= 1` with `a^c s <= N`,

    b a^{c-1} s  <=  N - 2 c_c.

Proof sketch: write `S_{k-2} = S_{c-1} + a^c T` with
`T = 1 + a + ... + a^{k-2-c}` (`T = 0` when `c = k-1`); then
`N = b a^{k-1} + 2b S_{c-1} + 2b a^c T`, so `N - 2c_c = b a^{k-1} + 2b a^c T`
and `N/a^c = b a^{k-1-c} + 2bT + 2bS_{c-1}/a^c` with the last term in `(0,2)`
because `S_{c-1} = (a^c - a)/(a-1) < a^c/(a-1)` and `b <= a-1`. Hence
`s <= b a^{k-1-c} + 2bT + 1`, and

    (N - 2c_c) - b a^{c-1} s  >=  b [ a^{k-2}(a-b) + 2 a^{c-1} T (a-b) - a^{c-1} ]
                              >=  b [ a^{k-2} - a^{c-1} ]  >=  0,

using `a - b >= 1`, `T >= 0`, and `c - 1 <= k - 2`. **This is where `b < a` is
used, and it is used twice** (once to get the `(0,2)` bound, once for
`a - b >= 1`). Confidence: high — it is a finite chain of inequalities, and it
was then stress-tested (see [E6]).

## [E4] Computational run 1 — brute force, b < a

Command (from `route-a/`):

    python3 verify_bruteforce.py 8 5 12 blt

Range: `2 <= a <= 8`, `1 <= b <= min(a-1, 12)` with `gcd(a,b)=1`, `2 <= k <= 5`,
skipping any point with `N > 300000` (none were skipped in this range).
The script also re-derives `chi` from the scalar definition at up to 400 sample
points per `(a,b,k)` and asserts it agrees with the vectorised array, so the
fast path is checked against the transcription.

Verbatim tail of output:

    parameter points: 84
    solution triples examined: 287888880
    defective points: 0

    real	0m0.580s

So: **84 parameter points, 287,888,880 solution triples, zero monochromatic
solutions.** This is consistent with Theorem 1 and extends the brief's 24
points to 84.

## [E5] Computational run 2 — brute force, b > a (sharpness side)

Command:

    python3 verify_bruteforce.py 6 5 14 bgt

Result pattern, without exception in range:

- every `k = 2` point is **solution-free** (30 points listed, e.g. `(2,3,2)`,
  `(3,4,2)`, ..., `(6,13,2)`);
- every `k >= 3` point is **defective**.

Sample defects the harness found (it reports the one with smallest `y`, not
necessarily the one my closed form predicts):

    (2,3,3)  (19, 1, 12)   colour 2
    (2,3,4)  (43, 7, 24)   colour 3
    (3,5,3)  (61, 1, 36)   colour 2      <-- matches the brief's stated defect
    (4,5,3)  (101, 1, 80)  colour 2

`(3,5,3) -> (61,1,36)` reproduces the brief's independently-obtained defect
exactly, which is a useful cross-check that my transcription of `chi` is the
same object the brief was measuring.

## [E6] Next: per-lemma stress tests

Writing `verify_lemmas.py` now. Plan: check the structural identities, Lemma 2
(the colour classes really are `V_i ∪ shell_i` and `core` is the interval I
claim), Lemma 4 in both the `floor` form and the `for all admissible s` form,
and Lemma 5 (`N < 2a^k`). Plus a **negative** control: Lemma 4 must *fail* at
`c = 2` whenever `b > a, k >= 3`, since that is precisely the defect. A lemma
that passed on both sides of the `b < a` line would mean I had isolated the
wrong statement.

---

## 2026-08-12T19:1x — [E7] Lemma stress tests: first run crashed on my own harness

Ran `python3 verify_lemmas.py 40 10`. It **hung past 120s** and I killed it by
explicit PID (`kill 1562543`; the brief forbids `pkill -f`, which self-matches).

Cause, diagnosed: two checks enumerated `s` explicitly up to `floor(N/a^c)`. At
`a = 40, b = 122, k = 10` that is `N ≈ 6.4e15`, i.e. `~4e12` iterations. This was
a harness bug, not a mathematical problem. **Recording it because it is exactly
the class of thing the project's CLAUDE.md warns about: a "measurement" that
never returns tells you nothing, and one that silently truncates is worse.**

Fix: the statement `∀ s ≥ 1 with a^c s ≤ N : b a^{c-1} s ≤ N - 2c_c` is
equivalent to its value at `s = floor(N/a^c)` (the left side is increasing in
`s`), so the large grid uses the floor form and a small grid (`a ≤ 7, k ≤ 5`)
keeps the explicit-`s` form as a cross-check that the two forms agree. Both are
reported separately so neither can hide behind the other.

## [E8] Lemma stress tests — results

Command: `python3 verify_lemmas.py 80 14`  (4.7s)

Range: `2 ≤ a ≤ 80`, `1 ≤ b ≤ 242` with `gcd(a,b)=1` and `b < a` (or `b > a`
for the negative control), `2 ≤ k ≤ 14`, all `2 ≤ c ≤ k-1`.

Verbatim:

    === Structural identities (definition sanity), a<=80, k<=14 ===
      [PASS   ] N = b(a^{k-1} + 2 S_{k-2})                           cases=    25545
      [PASS   ] c_i = b*S_{i-1} for 1<=i<=k-1                        cases=    25545
      [PASS   ] (a-1) S_m = a^{m+1} - a                              cases=     1185
      [PASS   ] N - 2 c_{k-1} = b a^{k-1}  (core width = L_k)        cases=    25545
      [PASS   ] N - 2c_c = b a^{k-1} + 2 b a^c T,  T = (a^{k-1-c}-1)/(a-1) cases=   153270
      [PASS   ] T = 0 exactly when c = k-1; S_{k-2} = S_{c-1} + a^c T cases=   153270
    === Lemma 2 (the colour classes are what we claim), a<=8, k<=5 ===
      [PASS   ] chi_array == definition, pointwise on all of [1,N]   cases=       82
      [PASS   ] colour 1 = {v(j)=1} exactly; no unit is coloured 1   cases=       82
      [PASS   ] units coloured k  <=>  in core [c_{k-1}+1, N-c_{k-1}] cases=       82
    === Lemma 4 (shell gap), b < a,  a<=80, k<=14, 2<=c<=k-1 ===
      [PASS   ] 0 < 2 b S_{c-1} / a^c < 2   (so floor <= 1)          cases=   153270
      [PASS   ] b a^{c-1} * floor(N/a^c)  <=  N - 2 c_c              cases=   153270
      [PASS   ] for all s>=1 with a^c s <= N:  b a^{c-1} s <= N - 2c_c  (explicit s) cases=      102
      [PASS   ] Lemma 4 FAILS at c=2 when b>a, k>=3 (sharpness)      cases=   115440
    === Lemma 5 (size bound for colour k), b < a, a<=80, k<=14 ===
      [PASS   ] N <= a^k + a^{k-1} - 2a                              cases=    25545
      [PASS   ] N < 2 a^k                                            cases=    25545
      [PASS   ] N < a^k (1+b)                                        cases=    25545
      [PASS   ] k=2, ANY b coprime to a:  N = ab < a^2 b             cases=    11585
    all checks PASS

The **negative control matters most**: Lemma 4 fails at `c=2` in all 115440
tested `b > a, k ≥ 3` cases. If Lemma 4 had held on both sides of `b = a` I
would have isolated the wrong statement and the "sharpness" would be
unexplained. It fails exactly where the colouring fails.

## [E9] Case-tree exhaustiveness audit

This is the check I trust most, because it tests *the written proof*, not just
its conclusion. `verify_casetree.py` enumerates **every monochromatic pair**
`x > y` with `chi(x) = chi(y) = c`, classifies it into one of the seven branches
B1..B7 of the proof, asserts the fact that branch *claims* about that pair, and
independently checks that no admissible `t` exists. A pair no branch claims is
reported `UNCOVERED`.

Command: `python3 verify_casetree.py 7 5 1400`  (1.1s)

    parameter points audited     : 53
    monochromatic pairs examined : 1466700
    branch totals                : {'B1': 87914, 'B2': 4122, 'B3': 14446,
                                    'B4': 80358, 'B5': 81684, 'B7': 1198176}
    UNCOVERED pairs              : 0
    problems                     : 0

**Observation worth recording: branch B6 has count 0 at every point.** B6 is
"both x and y are multiples of a^k". The proof asserts this branch is *vacuous*
because `N < 2a^k` means `[1,N]` holds at most one multiple of `a^k`. The audit
independently confirms the branch is never entered. I then added an explicit
lemma check `#{j ≤ N : a^k | j} ≤ 1` so the vacuity is asserted, not merely
observed — a branch that is never exercised is a place where a wrong argument
could hide undetected.

Confidence after E8+E9: **high** on Theorem 1. The argument is a finite chain of
elementary steps; the two non-trivial inequalities are stress-tested at 153270
and 25545 points respectively, and the case analysis is confirmed exhaustive on
1.47M concrete pairs.

## [E10] Theorem 2 — a REFUTATION of the statement I was given

The task brief asked me to prove: *for `b = a+1` and `k ≥ 3`, the triple*
`(x,y,z) = (a b^2 + 1, 1, a^2 b)` *is a monochromatic solution.*

**This is false for `k ≥ 4`.** I found the counterexample by hand first, at
`(a,b,k) = (2,3,4)`: there `N = 60`, the cuts are `c_2 = 6, c_3 = 18`, so the
shells are `Sh_2 = [1,6] ∪ [55,60]`, `Sh_3 = [7,18] ∪ [43,54]`, and the core is
`[19,42]`. The point `x = a b^2 + 1 = 19` is the **first element of the core**,
so `chi(19) = 4`, whereas `chi(1) = 2` and `chi(12) = 2`. Not monochromatic.

Then confirmed by `python3 verify_theorem2.py 12 40 8`, Claim 3, verbatim:

              a   b   k         N          x   y        z  chi(x) chi(y) chi(z)  mono?
              2   3   3        24         19   1       12       2      2      2  True
              2   3   4        60         19   1       12       4      2      2  False
              2   3   5       132         19   1       12       4      2      2  False
              ...
              6   7   6     76188        295   1      252       4      2      2  False
              summary by k: {3: '5/5 mono', 4: '0/5 mono', 5: '0/5 mono', 6: '0/5 mono'}

So the brief's closed form is the **k = 3 case only**. The arithmetic identity
`a(x-y) = bz` does hold for all `a,b,k` (the script asserts it), which is
presumably why the family looked general; what fails is the *colour* claim, and
only the colour claim. The triple stays fixed while `N` grows, so it slides out
of the outer shell and into the core.

**What I proved instead — strictly stronger.** The defect is not at a fixed
point, it is at the *left endpoint of the right half of shell 2*:

    Y = 1,   X = N - ab + 1,   W = N/b - a,   Z = aW,

all of colour 2, for **every** `a ≥ 2`, `gcd(a,b)=1`, `b > a`, `k ≥ 3` — not
just `b = a+1`. Checked: 1290 cases, 0 failures. At `k = 3` it specialises to
`X = ab(a+1)+1`, `Z = a^2(a+1)`, and further to `(ab^2+1, 1, a^2 b)` when
`b = a+1`, recovering the brief's family exactly.

Independent cross-check: the brief separately reports that `(a,b,k) = (3,5,3)`
fails at `(61,1,36)` and notes this does *not* match `ab^2+1 = 76`. My formula
gives `X = N - ab + 1 = 75 - 15 + 1 = 61` and `Z = a(a+a^2) = 36`. **Exact
match** — so the general form explains the brief's own "anomalous" example, and
that example is now evidence for the general form rather than an exception.

## [E11] Why k = 2 escapes — and it is not a coincidence

Two independent reasons, both recorded because I initially thought only the
first was operative:

1. **There are no shells at k = 2.** The shell index runs `2 ≤ i ≤ k-1`, empty
   when `k = 2`. Every unit is coloured `k = 2` and the core is all of `[1,N]`.
   The two-sided geometry that `b > a` breaks is simply absent.
2. **The defect family degenerates.** At `k = 2`, `N = ab`, so
   `X = N - ab + 1 = 1 = Y`, i.e. `t = 0`. Checked: 260 cases, 0 failures.

And the `k = 2` colouring is solution-free for **every** `b` coprime to `a`, not
only `b < a`. The `c = k = 2` branch needs a different argument there than the
one Theorem 1 uses: instead of "at most one multiple of `a^k` fits in `[1,N]`"
(which needs `b < a`), use `a^2 | x - y = bt ⟹ a^2 | t ⟹ x - y ≥ a^2 b > ab = N`.
Recorded as a separate Proposition rather than folded into Theorem 1, because
the hypotheses genuinely differ.

**Resulting exact characterisation** (this is stronger than "b < a is
sufficient", which is all I was asked for): since `gcd(a,b)=1` and `a ≥ 2` make
`b = a` impossible, the shell colouring is solution-free **iff** `b < a` or
`k = 2`.

---

## 2026-08-12T19:3x — [E12] CORRECTION received from the orchestrator re: FACT 2

The orchestrator retracted the base case of its "recursive lifting" bound. Its
original message to me stated `f(k) = a^{k-1}(b+1) - 1`; the corrected version
is `f(k) = a^k - 1` uniformly in `b <= a-1`, which is exactly
Chang–De Loera–Wesley Lemma 4.1 and therefore **not new**. The retracted
expression `a^{k-1}(b+1)-1` is a real solution-free colouring but suboptimal.

I had already written a comparison section leaning on `a^{k-1}(b+1)-1` as a
second competing bound. **Recording this as an error in my draft, not just in
the input**: I took a supplied numeric claim into a paper section without
checking it against the source it was attributed to. Checked now:

    (i) lift <= pure, equality iff b=a-1 : 5203 cases, 0 failures

So `a^{k-1}(b+1)-1 <= a^k - 1` always (for `b < a`), with equality exactly at
`b = a-1`. The lifting bound is dominated and does not belong in the
comparison as a rival. Section 7 of `proof.tex` rewritten to use `a^k - 1` as
the sole baseline.

**Silver lining — the comparison gets sharper, not weaker.** Since the lifting
bound is dominated, "shell beats both rivals" collapses to "shell beats
`a^k - 1`", and I can now state and *prove* the exact condition rather than
report a grid observation:

    N + 1 > a^k   <=>   b = a-1 and k >= 3

Checked: 14105 cases, 0 failures (`a <= 59`, `b < a` coprime, `k <= 14`), in
both the direct and the algebraic form
`b(a^k + a^{k-1} - 2a) > (a-1)(a^k - 1)`. Proof of the `b <= a-2` direction:
bounding `b <= a-2` gives
`RHS - LHS >= 2a^{k-1} + 2a^2 - 5a + 1 > 0` for all `a >= 3, k >= 2`
(and `b <= a-2` forces `a >= 3`). Proof of the `b = a-1` direction: there
`N = a^k + a^{k-1} - 2a` exactly, so `N+1 > a^k` iff `a^{k-1} > 2a-1`, i.e.
iff `k >= 3`.

Earlier entry [E10]'s grid observation "shell strictly best in 184 of 184
points with b=a-1" is superseded by this proved statement. I am leaving [E10]
in place per the append-only rule.

**Provisional / uncertain:** I have not independently verified that `a^k - 1`
is due to Chang–De Loera–Wesley Lemma 4.1 — I am taking that attribution from
the brief and the orchestrator. The *mathematics* (that `min(v(j),k-1)` is
solution-free on `[1, a^k-1]`) I did check; the *citation* I did not.

---

## 2026-08-12T19:4x — [E13] Final sweep, `run_all.sh`

Wrote `run_all.sh` so every number in the paper and the report is reproducible
by one command. `REAL_EXIT=0`, ~10s wall on one core.

Widened the Theorem 1 brute force to `2 ≤ a ≤ 10`:

    parameter points: 124
    solution triples examined: 2329779230
    defective points: 0

That is **2.33 billion** solution triples across 124 parameter points with no
monochromatic solution. (Caveat on what this is worth: enumeration cannot prove
the theorem — that is the whole point of Route A — but it is the strongest
available check on whether the *written* proof is about the *same object* the
brief measured.)

`verify_lemmas.py 80 14` and `verify_casetree.py 7 5 1400` unchanged from
[E8]/[E9]; `verify_theorem2.py 12 40 8` unchanged from [E10].

## [E14] Late addition — Proposition 'beat' now proved, not observed

Following [E12] I replaced the grid observation with a proof. Statement: for
`a ≥ 2`, `1 ≤ b ≤ a-1`, `gcd(a,b)=1`, `k ≥ 2`,

    N + 1 > a^k   <=>   b = a-1 and k >= 3.

The pivot is the identity `(a-1)N = b(a^k + a^{k-1} - 2a)`, which reduces the
`b = a-1` case to `a^{k-2} ≥ 2` (clean: false at k=2, true at k≥3) and the
`b ≤ a-2` case to `2(a^{k-1} + a(a-2)) > 0` (note `b ≤ a-2` forces `a ≥ 3`, so
`a(a-2) > 0`). Both pivots checked at 14105 parameter points, 0 failures.

Decision point 3: I stated this as a proposition with proof rather than as a
computed table, because a table over `a ≤ 29` says nothing about `a = 30`, and
the whole premise of Route A is that finite checking is not proof. Consistency
demanded the same standard here.

## [E15] Honest status at close

**Proved, no gaps I am aware of:**
- Theorem 1 (`b < a`, `k ≥ 2`, `gcd(a,b)=1`, `a ≥ 2`) — solution-freeness.
- Theorem 2 (`b > a`, `k ≥ 3`) — explicit monochromatic solution.
- Proposition (`k = 2`, any `b` coprime to `a`) — solution-freeness.
- Corollary — solution-free **iff** `b < a` or `k = 2`.
- Proposition 'beat' — exactly when the bound improves on `a^k`.

**Not proved, and not claimed:**
- That `N+1` is the *true* Rado number for any parameter triple. The brief
  reports tightness at `(3,2,3)`, `(4,3,3)`, `(3,2,4)`, `(4,3,4)` and explicit
  failure at `(3,2,5)`. I did not attempt upper bounds; nothing here bears on
  them. The paper says so.
- The attribution of `a^k - 1` to Chang–De Loera–Wesley Lemma 4.1 (taken on
  trust from the brief; see [E12]).

**Where I would look first if something is wrong:** Lemma 4's step
`s ≤ b a^{k-1-c} + 2bT + 1`. It is the only place where an integrality argument
does real work, and it is the only inequality in the proof that is *tight* — the
`+1` is attained (`θ ∈ (1,2)` happens), so there is no slack absorbing an
algebra slip. It is checked at 153270 parameter points and the final chain has
slack `b(a^{k-2} - a^{c-1}) ≥ 0` which is **zero when c = k-1** — i.e. the
worst case is exactly `c = k-1`, and it closes with no room. That is either
elegant or fragile depending on taste; I checked it three times by hand and
once by machine.

## [E16] Correction/refinement to [E15]: Lemma 4's tightness, measured

In [E15] I wrote that Lemma 4's slack "is zero when c = k-1". That was
imprecise — appending the correction rather than editing it. Measured:

    Lemma4 instances: 12105  equality cases: 252
    equality outside (b=a-1, c=k-1): 0
    b=a-1, c=k-1 equality misses: 0
    instances with theta>=1 (the +1 in the floor bound is real): 6075 of 12105

So the correct statement is: the slack is `b a^{k-2} (a-b-1)` at `c = k-1`
(because `T = 0` there), which vanishes **iff additionally `b = a-1`**. Equality
in Lemma 4 holds at exactly the 252 points with `b = a-1` and `c = k-1`, and at
no others, over `a ≤ 29, k ≤ 11`. Concretely `(a,b,k,c) = (3,2,4,3)`:
`b a^2 ⌊102/27⌋ = 18·3 = 54 = 102 - 48`.

Two consequences worth stating in the paper (added as Remark 'gaptight'):
1. Lemma 4 cannot be weakened — the case `b = a-1`, `c = k-1` is exactly tight,
   and `b = a-1` is precisely the line where the shell bound beats `a^k`. The
   construction lives on the boundary of its own lemma.
2. The truncation `⌊θ⌋ ≤ 1` cannot be strengthened to `⌊θ⌋ = 0`: `θ ≥ 1` in
   6075 of 12105 instances. My failed Conjecture A ([E3]) died for exactly this
   reason — it implicitly wanted `θ` to be negligible.

## [E17] Close-out

Final state: `run_all.sh` exit 0; `latexmk` exit 0, 8 pages, 0 errors, 0
undefined references. `REPORT.md` written. Deliverables in `route-a/`:
`proof.tex`, `proof.pdf`, `REPORT.md`, `LOG.md`, `shell.py`,
`verify_bruteforce.py`, `verify_lemmas.py`, `verify_casetree.py`,
`verify_theorem2.py`, `compare_bounds.py`, `run_all.sh`.

No cargo was run and no axeyum component was invoked at any point in this task,
per the resource discipline in the brief. Nothing in the paper or the report is
attributed to axeyum.

---

## 2026-08-12T19:5x — [E18] Orchestrator's rigidity finding: cross-checked, and it EXPLAINS itself through my case tree

The orchestrator freed the cut vector and found: at `b = a-1` the canonical
vector is the *unique* feasible one at `N = N_shell` (and none is feasible at
`N+1`); for `b < a-1` the shape is slack. Advice attached: expect my inequality
to be exactly tight, and if it "goes through with room to spare" I may have
proved something weaker than the truth.

Wrote `verify_rigidity.py` and answered this properly rather than accepting it.

**Part 1 — independent reproduction.** I re-implemented the enumeration from my
own definitions (arbitrary cut vector, valuation strata fixed) and reproduced
the orchestrator's table on the 6 entries I could afford, plus its three
slack rows:

     (a,b,k)      N          canonical    tested  feas@N  feas@N+1
     (3,2,3)     30               (6,)        14       1         0
     (4,3,3)     72              (12,)        35       1         0
     (5,4,3)    140              (20,)        69       1         0
     (6,5,3)    240              (30,)       119       1         0
     (3,2,4)    102            (6, 24)      1225       1         0
     (4,3,4)    312           (12, 60)     11935       1         0
     (5,3,4)    555           (15, 90)     38226    1125      1125
     (4,1,4)    104            (4, 20)      1275      64        64
     (3,1,3)     15               (3,)         7       3         3

Every count matches the orchestrator's independently. (I skipped `(5,4,4)` and
`(3,2,5)`; at 67896 and 644956 vectors they exceed my budget on a shared box.)

**Part 2 — the actual answer to "which inequality is tight".** For each
canonical vector I moved one cut by ±1 and asked *which branch of my case tree*
refutes the result. Over all 20 legal perturbations:

    branch histogram: {'B4': 14, 'B7': 6}

**B5 — the Lemma 4 branch — never fires.** The rigidity is governed entirely by
the *width* branches B4 (two units in the same interval of a shell) and B7 (two
units in the core), each of which is tight by exactly one:
`x-y <= L_c - 1` versus `x-y >= L_c`.

So the orchestrator's inference was directionally right but pointed at the
wrong inequality. My Lemma 4 *should* have slack for `c < k-1`, and does; it
constrains the cross-shell distance, not the individual widths. The equalities
the rigidity demands live in B4/B7, and those are tight for every `c` and every
`b < a` by construction. Nothing here indicates I proved something weaker than
the truth.

**Part 3/4 — why rigidity is a `b = a-1` phenomenon, proved not observed.**
A width constraint at colour `c` only bites if its minimal witness fits: take
`s = 1`, giving the pair at distance `L_c` with `z = a^c`, which is a real
solution iff `a^c <= N`.

- For `2 <= c <= k-1` this is automatic: `N >= b a^{k-1} >= a^{k-1} >= a^c`
  (checked, 26015 cases, 0 failures). All inner widths are always pinned.
- For `c = k` it reads `a^k <= N` — and `a^k <= N  <=>  b = a-1 and k >= 3`
  (checked, 14105 cases, 0 failures). **This is exactly Proposition 'beat'.**

So for `b <= a-2` the core-width constraint is *vacuous*, the core can grow, and
the shape deforms; at `b = a-1` it bites and every width is pinned. The
orchestrator's rigidity phenomenon and my Proposition 'beat' are the same
statement. Confirmed on all 9 enumerated points:
`B7-active == (b=a-1 and k>=3) == (unique feasible vector)`, 0 mismatches.

**A structural detail worth recording — this is what the two-sidedness is for.**
The offending pair must consist of *units*. Since `a | N` and `a | c_i`
(checked, 2152 points, 0 failures), the interval endpoints `c_{i-1}+1` and
`N-c_i+1` are `≡ 1 mod a`, hence units. Widening a shell exposes the bad unit
pair in its **left** interval; narrowing a cut exposes one in the **right**
interval of the next shell (the left one would start at `c_i ≡ 0 mod a`, a
non-unit, and fail to produce a monochromatic pair). Both directions are
refuted only because the shells are two-sided. Added to the paper as
Remark 'rigid'.

**What I did NOT prove.** The orchestrator's `feasible @ N+1 = 0` — that the
shape cannot be stretched past `N_shell` — is an upper-bound-flavoured claim
about the family of shell shapes. I reproduced it at 6 points; I did not prove
it and it is not in the paper as a theorem. It is the natural next result and I
am flagging it as open, not quietly implying Theorem 1 covers it. Note also it
is a statement about *this shape only*: the brief records a solution-free
5-colouring of `[1,350]` at `(3,2,5)` where `N_shell = 318`, so shape-optimality
is not global optimality.

---

## 2026-08-12T20:0x — [E19] Rigidity Theorem: the orchestrator's strategy works, and the gap CLOSES

The orchestrator proposed a pigeonhole on widths and flagged one gap: proving
`w_c > L_c => monochromatic solution` needs a *unit* pair at distance `L_c`, and
when `w_c = L_c + 1` there is only one candidate start, which might be a
multiple of `a`. Verdict: **the strategy is sound and the gap closes.** Both
halves are now proved for all `a >= 2`, and the theorem is in the paper
(Section 'Rigidity of the shape', Lemma 'width' + Theorem 'rigid').

**Closing the gap, part 1 — the residue computation.** With `w_c = L_c + 1` there
are two candidate starts, not one, because the shell is two-sided:
`y_L = c_{c-1}+1` and `y_R = M - c_c + 1`. Both fail only if `a` divides both.
Since `c_c = c_{c-1} + L_c + 1` and `a | L_c`, `M - c_c + 1 = M - c_{c-1} (mod a)`,
and `a | c_{c-1}+1` gives `c_{c-1} = -1`, so the obstruction **forces
`M = -1 (mod a)`**. Same for the core: `W = L_k+1` and `a | c_{k-1}+1` give
`M = 2c_{k-1} + W = -2 + L_k + 1 = -1 (mod a)`.

Consequences, immediately:
- `M = N`: `a | N`, so `M = 0 (mod a)`; the obstruction would need `a | 1`.
  Impossible. So **no obstruction ever occurs at `M = N`**, every width bound
  holds, the pigeonhole closes, and equality forces the canonical vector.
  **Part (1) done, all `a >= 2`.**
- `M = N+1`: `M = 1 (mod a)`; obstruction needs `1 = -1 (mod a)`, i.e. `a | 2`,
  i.e. **`a = 2` only**. So part (2) is immediate for `a >= 3`.

**Closing the gap, part 2 — a = 2.** This case is real, not hypothetical: my
width-lemma audit found the obstruction occurring **117 times, every one of them
at `a = 2, M = N+1`**, and zero times anywhere else. Neither my earlier
enumeration nor the orchestrator's table contained a single `a = 2` point
(`b = a-1 = 1`), so this was an untested corner of the claim on both sides.

Closed by a defect induction. Put `e_c = w_c - L_c`, `e_K = W - L_k`,
`E_j = e_2 + ... + e_j`, `E_1 = 0`; then `2E_{k-1} + e_K = M - N`. Since
`c_{c-1} = b*Sigma_{c-2} + E_{c-1}` and `a | b*Sigma_{c-2}`, we get
`c_{c-1} = E_{c-1} (mod a)`, so the trigger condition becomes purely
combinatorial: `e_c = 1` only if `E_{c-1} = -1 (mod a)`.

  *Claim: `E_j <= 0` for all j.* Induction. `E_1 = 0`. If `e_j <= 0`, done. If
  `e_j = 1` then `E_{j-1} = -1 (mod a)`, which for `a >= 2` rules out
  `E_{j-1} = 0`; with `E_{j-1} <= 0` that gives `E_{j-1} <= -1`, so `E_j <= 0`.

Then at `M = N+1`, `2E_{k-1} + e_K = 1`: if `e_K <= 0` then `E_{k-1} >= 1`,
contradicting the claim; if `e_K = 1` then `E_{k-1} = 0`, but the trigger
demands `E_{k-1} = -1 (mod a)`, i.e. `a | 1`. Contradiction either way.
**Part (2) done, all `a >= 2`** — and uniformly, so the `a >= 3` residue
shortcut is not even needed for part (2).

**Verification (this is the part I would not skip).**

1. *Constructive content of the width lemma*, `verify_width_lemma.py`: over every
   cut vector at `M in {N, N+1}` for `2<=a<=7`, `3<=k<=6`, whenever the lemma
   claims a witness, exhibit it and check it really is a monochromatic solution.

       total witness claims verified: 44611
       total residue obstructions   : 117  (each must have M = -1 mod a)
       failures                     : 0

   The 117 obstructions break down exactly as predicted: `(2,1,4)` at `M=21`: 3;
   `(2,1,5)` at `M=45`: 114; **zero at `M=N` for any `a`, zero at `M=N+1` for
   `a>=3`.** That distribution is the theory's fingerprint, and it matched.
2. *The combinatorial core*, `verify_defect_induction.py`: brute-force all
   admissible defect sequences.

       admissible defect sequences examined            : 114031
       sequences with some E_j > 0 (lemma says 0)      : 0
       solutions of 2E + e_K = 1  (M=N+1; says 0)      : 0
       non-canonical 2E + e_K = 0, all e<=0 (says 0)   : 0
3. *The conclusion itself*, `verify_rigidity_theorem.py`: full cut-vector
   enumeration at 8 points, now **including `a=2`, `k=3,4,5`** which nobody had
   enumerated. All `M=N`: unique = canonical. All `M=N+1`: infeasible.
4. *Off the line*: at `(4,1,4)`, 64 feasible vectors of which 63 violate a width
   bound — the core bound is vacuous there because `a^k = 256 > 104 = N`.
   Theorem is false off the line, exactly as Proposition 'beat' predicts.

**Correction to my own [E18].** There I called this "the natural next result"
and listed it as open. It is now closed. I also wrote in [E18] that the
two-sidedness matters because "narrowing a cut exposes a unit pair in the right
interval" — that is true but is not the sharpest statement. The sharper one,
used in the proof: two-sidedness gives **two** candidate starts when
`w_c = L_c+1`, and the obstruction needs *both* to be multiples of `a`, which
is what forces `M = -1 (mod a)`. With one-sided shells the residue argument
loses the constraint `a | M - c_c + 1` and part (1) would not go through.

**Scope, stated precisely.** Theorem 'rigid' is about the *shell shape only*:
valuation strata fixed, cuts free. It does **not** say `R_k = N+1`. At
`(3,2,5)` the brief records a solution-free 5-colouring of `[1,350]` while
`N = 318`; that colouring is simply not of this shape. Shape-optimality is not
global optimality and the paper says so.
