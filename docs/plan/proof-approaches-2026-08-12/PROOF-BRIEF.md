# Ground truth brief — the theorem we are trying to PROVE

Verified by the orchestrator on 2026-08-12 by direct enumeration. Do not
re-derive these from memory or from any summary; they are measured.

## The equation and its solutions

E(a,b):  a(x - y) = b z,  with x, y, z in [1, n], a >= 2, b >= 1, gcd(a,b) = 1.

With gcd(a,b) = 1 the solution set is exactly

    x - y = b t,   z = a t,   t >= 1.

(z may coincide with x or y; coincidences are allowed and ARE counted as
monochromatic if the colours agree. x = y is excluded since t >= 1.)

R_k(E) = least n such that EVERY k-colouring of [n] has a monochromatic
solution. So exhibiting a solution-free k-colouring of [N] proves R_k > N.

## The shell construction (the object to be proved correct)

Parameters a >= 2, b >= 1, gcd(a,b) = 1, k >= 2. Let v(j) = a-adic valuation
of j (largest e with a^e | j).

    Level capacities   L_i = a^(i-1) * b          for i = 2..k
    N = N_shell(a,b,k) = 2*(L_2 + ... + L_{k-1}) + L_k
                       = b * ( a^(k-1) + 2*(a^(k-2) + ... + a) )

    Cumulative cuts:   c_1 = 0,  c_i = c_{i-1} + L_i   (i = 2..k-1)

    Colouring chi of [1, N] with colours 1..k:
      * if a | j :      chi(j) = min(v(j), k)
      * else ("unit"):  chi(j) = i  if j in [c_{i-1}+1, c_i] U [N-c_i+1, N-c_{i-1}]
                                    for some 2 <= i <= k-1   (a two-sided shell)
                        chi(j) = k  otherwise (the "core")

So colour 1 = exactly the j with v(j) = 1, and nothing else.
Colour i (2 <= i <= k-1) = {v(j) = i} U shell_i.
Colour k = {v(j) >= k} U core.

Competing construction: the pure a-adic colouring chi(j) = min(v(j), k-1),
solution-free on [1, a^k - 1]  (this is Chang-De Loera-Wesley Lemma 4.1;
NOT ours). The claimed bound is the max of the two.

## MEASURED FACTS (enumerated, not recalled)

Over all (a,b) with 2 <= a <= 6, 1 <= b <= 6, gcd(a,b) = 1, and k = 2..5:

**b < a  ->  the shell colouring is solution-free in ALL 24 tested triples.**
   (a,b) in {(2,1),(3,1),(3,2),(4,1),(4,3),(5,1),(5,2),(5,3),(5,4),(6,1),(6,5)}

**b > a  ->  solution-free at k = 2, DEFECTIVE at every k >= 3.**

The defects for b = a+1 have a CLOSED FORM (verified at a = 2,3,4,5):

       y = 1,   x = a*b^2 + 1,   z = a^2*b

   check:  a(x-y) = a * a*b^2 = a^2 b^2 = b * a^2 b = b z.  Identity holds
   for ALL a,b -- so this is a candidate *provable* infinite counterexample
   family, superseding the "19 of 19 parameter triples defective" sweep.
   (For general b > a the defect exists but does NOT follow this form: e.g.
   (a,b,k) = (3,5,3) fails at (61,1,36), and a*b^2+1 = 76 there. Only the
   b = a+1 subfamily is known to follow the closed form.)

Selected values of N+1 = N_shell + 1 versus a^k:

    (a,b,k)      N+1      a^k     winner
    (3,2,3)       31       27     shell
    (4,3,3)       73       64     shell
    (3,2,4)      103       81     shell
    (4,3,4)      313      256     shell
    (5,4,4)      741      625     shell
    (6,5,4)     1501     1296     shell
    (3,2,5)      319      243     shell
    (3,1,3)       16       27     a^k
    (5,2,4)      371      625     a^k
    (5,3,4)      556      625     a^k

For b = a-1 the shell bound always exceeds a^k in the tested range.

## Status of the mathematics (BE HONEST ABOUT THIS)

- The shell colouring's solution-freeness is **verified at 24+ points and
  NOT PROVED**. There is no written proof anywhere in this project. The
  construction source asserts it.
- TIGHTNESS (that R_k equals N+1) holds at (3,2,3)=31, (4,3,3)=73,
  (3,2,4)=103, (4,3,4)=313 -- all confirmed by refutation -- and **FAILS at
  (3,2,5)**: the shell gives 319 but a solution-free 5-colouring of [350]
  exists and is verified. So any tightness claim is scoped to k <= 4.
- b = a-1, k = 4 has two further predicted-exact values with verified lower
  bounds already in hand: R_4(5(x-y)=4z) = 741 and R_4(6(x-y)=5z) = 1501.

## What "true proof" means here, and why it is the point

Everything this project has produced for these numbers is **verification**:
a DRAT certificate answers "is THIS formula unsatisfiable?" for one n, in
~100M opaque steps, and says nothing about n+1 and nothing about why.

A **proof** of the construction is a single finite argument covering
infinitely many (a,b,k). No amount of instance-checking can produce one.
That is the gap these three routes attack.

Precedent inside this project: the solution-form lemma above (x-y = bt,
z = at) was NOT checked at finitely many points -- it was put to axeyum's
arithmetic layer as two refutations and came back unsat **unbounded over
Z^3**. That is a true proof, machine-produced, and it is the existence proof
that route B is not fantasy.

## Resource discipline (READ THIS -- a previous session crashed this machine)

This box has **4 cores**. Three agents are running concurrently.

- Export `CARGO_BUILD_JOBS=1` before any cargo command. Never use
  `--all-targets` or a workspace-wide build.
- The crates you are likely to need are ALREADY BUILT (axeyum-lean-kernel,
  axeyum-solver, axeyum-cas, all-features). Use `cargo test -p <crate>`
  narrowly; do NOT run `just check`, `cargo clippy --workspace`, or
  `cargo test --workspace`.
- Never run `pkill -f <pattern>` -- it self-matches and has killed the
  session twice. Use explicit PIDs.
- If you need heavy enumeration, prefer Python over building Rust.

## Honesty requirements

This project's CLAUDE.md records that **its tools have lied more often than
its solver has been weak**: a gate that ran zero tests for 15 days while
exiting 0, a checker whose diagnostic named the wrong cause, a doc comment
that misdescribed what it bound. Therefore:

- Report a NONZERO test count or the measurement is not evidence.
- If you prove less than the full theorem, say exactly what you proved and
  exactly what remains assumed. A correct partial result is worth far more
  than an overclaimed whole one.
- If a route fails, report the failure and WHY. A negative result here is a
  genuine finding and will be recorded, not held against you.
- Do not claim anything is "verified by axeyum" unless you ran it and can
  paste the command and its output.
