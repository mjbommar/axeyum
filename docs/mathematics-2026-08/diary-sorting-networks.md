# Diary — optimal-size sorting networks (lanes `sorting-networks`, `sorting-networks-2`), 2026-08-14

A new domain for the fact ledger: **algorithms**. `S(n)` is the minimum number
of comparators in a sorting network on `n` channels, and its optimality is two
claims that need no optimizer:

* **upper bound** — an explicit network of size `S` sorts. By the 0-1 principle
  it is enough to run all `2^n` binary inputs through it, which the example does
  in plain Rust, sharing no code with the encoder.
* **lower bound** — *no* network of size `S - 1` sorts. That is a plain UNSAT,
  and its DRAT certificate is re-derived by this repository's own backward
  checker.

So the encoder is parameterised by `(n, size)` and answers sat/unsat. No MaxSAT,
no optimization search, no trusted "best found" value.

Everything lives in `crates/axeyum-cnf/examples/sorting_network.rs`.

---

## Where the values stand

| `n` | `S(n)` | established here | how |
| --- | --- | --- | --- |
| 3 | 3 | yes | monolithic, both bounds |
| 4 | 5 | yes | monolithic, both bounds |
| 5 | 9 | yes | monolithic, both bounds |
| 6 | 12 | yes | **lower bound by three independent routes** (below) |
| 7 | 16 | in progress | `size 15` refutation running |

All match Knuth. That is the point: this lane deliberately started at values the
literature already knows, so the encoder is validated against ground truth
*before* any frontier claim.

---

## The finding that mattered: the lower bound is where the whole thing can go wrong

The upper bound cannot lie — a network either sorts all `2^n` inputs or it does
not, and the replay is 40 lines of Rust that never sees a CNF. Every risk in
this lane is on the lower-bound side, and specifically in **symmetry breaking**:

> An unsound symmetry break does not produce a wrong `sat`. It produces a wrong
> **UNSAT** — it deletes the network that would have been the counterexample,
> and the solver truthfully reports that nothing is left.

That failure mode is invisible to every check that only looks at satisfiable
cases. So each break carries its argument in the module header, and `--sym none`
exists so every verdict can be re-derived with none of them. `n=5 size=8`
refutes in 0.81 s with the breaks and 14.97 s without — **same verdict**, which
is the measurement that makes the 0.81 s trustworthy.

The same discipline is now on the cube route (`--cube-sym none|full|subsume`),
which had no such control until this session.

---

## S(6) = 12, by three routes that do not share a search

The lower bound `S(6) >= 12` is the claim "no 11-comparator network sorts 6
channels". It was established three ways:

| route | symmetry assumed | wall clock |
| --- | --- | --- |
| monolithic, `--sym full` | `first` + `commute` | 1195 s (single core, s5) |
| cube split, depth 3, `--cube-sym full` | `first` + `second` + `commute` | 151 s (51 branches, 16 cores, s6) |
| cube split, depth 4, `--cube-sym full` | same | 138 s (322 branches, 16 cores, s7) |

Every cube branch streams its own DRAT proof to disk and is then **read back and
re-checked** by the backward checker, so the peak memory stays bounded and no
branch is believed on the solver's say-so. The depth-3 and depth-4 splits
partition the search differently, so their agreement is not a re-run.

The upper bound is the Knuth 12-comparator network, replayed over all 64 binary
inputs by the independent checker, and separately *rediscovered* by the SAT
search at `size 12` under all three cube modes.

---

## What the prefix/suffix reduction bought

The cube route fixes a prefix `P` of comparators, computes `outputs(P)` — the
distinct not-yet-ascending images of all `2^n` inputs — and encodes only the
remaining `k - |P|` comparators against that reduced vector set. `P ++ suffix`
sorts everything exactly when `suffix` sorts `outputs(P)`, so this removes the
prefix's comparator variables *and* collapses inputs the prefix has already
mapped together.

That alone took `n=6 size 11` from 1195 s to 151 s. The second reduction is
**permutation subsumption**, added this session:

> `R1` subsumes `R2` when some channel relabelling `pi` has `pi(R1) ⊆ R2`. Then
> `R2` `k`-sortable implies `R1` `k`-sortable, so **refuting `R1` refutes every
> `R2` it subsumes** — only the subsumption-minimal branches need solving.

Proof of the lemma is in the doc comment on `subsumption_reduce`. It relabels a
network sorting `R2` into a *generalized* one that drives `R1` into a fixed
permuted order, then untangles (Knuth TAOCP vol. 3, 5.3.4 ex. 16, in the form
Codish–Cruz-Filipe–Schneider-Kamp state it for arbitrary input sets). Since it
rests on the same untangling step as the `first`/`second` breaks, it is **off by
default**.

Branch counts, equality-dedup versus subsumption:

| | `--cube-sym none` | `full` | `subsume` |
| --- | --- | --- | --- |
| `n=6` depth 4 | 1441 | 322 | **156** |
| `n=6` depth 5 | 4058 | 1342 | **392** |
| `n=7` depth 4 | 5502 | 696 | **380** |

Implementation note: for `n <= 7` an output set is a set of `n`-bit vectors, so
it fits a `u128` bitmask and "is some relabelling of `R1` a subset of `R2`" is a
single `&`. Precomputing all `n!` relabelled masks per prefix once turns the
whole pairwise reduction into a few hundred million `u128` tests.

---

## The controls, and why each exists

* **Every upper bound** is replayed over all `2^n` inputs by
  `sorts_all`, which shares no code with the encoder. A SAT model is never
  itself the evidence.
* **Every lower bound** is repeated at a weaker symmetry setting. Monolithic:
  `--sym none`. Cube route: `--cube-sym none`, where every prefix position ranges
  over every comparator and the suffix gets no break, leaving output-set
  *equality* as the only reduction — and equality needs no argument at all, since
  two prefixes with the same output set pose a literally identical question.
* **The satisfiable side is the real test of a reduction.** At `n=4 size=5`,
  `n=5 size=9` and `n=6 size=12`, all three cube modes return `sat` with networks
  that pass the 0-1 replay. A reduction that had deleted a real network would
  show up here as a `sat` cell turning `unsat`.
* **`--sweep`** runs every `n` with a known `S(n)` at both `S(n)-1` and `S(n)`
  under several symmetry modes and requires agreement with the published value.

`axiom_footprint` on the facts is deliberately not empty. It names
`sortnet.encoder-faithfulness`, `sortnet.zero-one-principle` and
`sortnet.symmetry-breaking-soundness` — the last of which is exactly the
untangling theorem the breaks and the subsumption reduction both consume.

---

## A literature correction this lane had to make about itself

The `KNOWN_S` comment in the example said:

> `S(11)` is open (`33 <= S(11) <= 35`).

**It is not open.** Harder (2020, [arXiv:2012.04400](https://arxiv.org/abs/2012.04400))
settled `S(11) = 35` and `S(12) = 39`, generalizing a result of Van Voorhis from
sorting networks to a wider class of comparator networks and deriving a dynamic
programming algorithm for optimal size; the lower bounds were formally verified
in Isabelle/HOL. That moves the smallest genuinely open cell for optimal **size**
to `S(13)`.

The confusion is easy and worth naming: **optimal depth and optimal size are
settled to different `n`**, and a bound quoted for one is routinely misread as a
bound for the other. Anything this lane produces at `n <= 12` is *validation*,
not a frontier result, and the comment now says so in place of the stale claim.

Sources:
- Jannis Harder, *An Answer to the Bose-Nelson Sorting Problem for 11 and 12
  Channels*, arXiv:2012.04400 — <https://arxiv.org/abs/2012.04400>
- Codish, Cruz-Filipe, Frank, Schneider-Kamp, *Twenty-Five Comparators is
  Optimal when Sorting Nine Inputs (and Twenty-Nine for Ten)*, arXiv:1405.5754
- Codish, Cruz-Filipe, Schneider-Kamp, *Sorting networks: to the end and back
  again*, J. Comput. Syst. Sci. 2016

---

## Operational notes

`systemd-oomd` killed this box's entire session cgroup during this work (68.36%
pressure over 20 s, 27 processes, 83.6 GB peak), taking a 2¼-hour solve with it.
It kills by **cgroup**, so `nohup` does not help. Long runs belong on an idle
host inside a memory-bounded transient unit:

```sh
ssh s6 "systemd-run --user --unit=<name> -p MemoryHigh=18G -p MemoryMax=22G \
  -p StandardOutput=append:/nas3/data/axeyum/<dir>/<log> \
  -p WorkingDirectory=/tmp /nas3/data/axeyum/bin/sorting_network --n 7 --size 15 \
  --cubes <dir> --depth 4 --jobs 16 --cube-sym subsume"
```

The cube route is what makes this practical: each branch's proof is streamed to
disk rather than accumulated, so a 16-worker run stays comfortably inside the
memory cap even when individual certificates reach 100 MB.
