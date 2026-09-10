# cvc5 Seq-theory regression slice

30 files vendored from cvc5's own strings/seq regression suite (`test/regress/cli/*/strings`, `*/seq`), 2026-09-09, roadmap item P2.5 (`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`).

New family: zero `Seq`-theory files existed in this corpus before P2.5. Files here declare a mix of upstream logics (`QF_SLIA`, `ALL`, ...) but share `Seq` sort content; bucketed by family (the `axeyum-smtlib` `Sort::Seq` path) rather than by declared logic string, since the declared logic is not diagnostic for this family upstream.

## Provenance

- Upstream repository: https://github.com/cvc5/cvc5 (cloned into `references/cvc5/`, gitignored; `scripts/fetch-references.sh`).
- Clone commit at vendoring time: `1689f13331f7543801f82d9dcbcaac2f70a26781`.
- Each file carries a header comment with its exact upstream path (`test/regress/cli/...`) and this commit SHA. Where upstream stated no `(set-info :status ...)`, the header says so and names the `; EXPECT: sat|unsat` comment line the `:status` was derived from — this happened only when the file had exactly one such line and it was unambiguously `sat` or `unsat` (never inferred, never guessed).
- Excluded from selection: any file using `push`/`pop`/`reset`/`reset-assertions` (scoped scripts — the flat assertion view the sweep checks against `:status` is not faithful for those), more than one `(check-sat)`, `forall`/`exists`, or a status that was ambiguous/absent (no `:status` and no single clean `EXPECT` line).

## Licence

cvc5 is modified BSD (BSD-3-Clause). These files are redistributed source-code test data; the obligation is to retain the copyright notice, the list of conditions, and the disclaimer. Reproduced in full:

```
cvc5 is copyright (C) 2009-2026 by its authors and contributors (see the
`AUTHORS` file in the cvc5 repository) and their institutional affiliations.
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice,
   this list of conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.
3. Neither the name of the copyright holder nor the names of its
   contributors may be used to endorse or promote products derived from
   this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT OWNERS AND CONTRIBUTORS ''AS IS''
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNERS OR CONTRIBUTORS BE
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.

(Full text: `references/cvc5/COPYING` at the pinned clone commit, or
https://github.com/cvc5/cvc5/blob/main/COPYING upstream.)
```

## Soundness result (P2.5 exit criterion)

Run: `cargo test -p axeyum-solver --features full --test corpus_regression`. Of these 30 files: **27 decided correctly** against `:status`, **3 returned `unknown`** (a coverage gap, not a soundness bug), **0 wrong verdicts**.

## Operator coverage

16 distinct `str.*`/`seq.*`/`re.*` operators in this directory:

`seq.at`, `seq.contains`, `seq.empty`, `seq.extract`, `seq.len`, `seq.nth`, `seq.prefixof`, `seq.replace`, `seq.replace_all`, `seq.rev`, `seq.suffixof`, `seq.unit`, `seq.update`, `str.contains`, `str.len`, `str.update`

## Per-file status

| File | Logic | `:status` | source | verdict | operators |
|---|---|---|---|---|---|
| `cvc5__cli__regress0__seq__array__model-dd-1220.smt2` | ALL | sat | set-info | decided (agrees) | `seq.len`, `seq.unit`, `seq.update` |
| `cvc5__cli__regress0__seq__issue5543-unit-cmv.smt2` | ALL | sat | expect-comment | decided (agrees) | `seq.unit` |
| `cvc5__cli__regress0__seq__issue5547-small-seq-len-unit.smt2` | ALL | sat | expect-comment | decided (agrees) | `seq.len`, `seq.unit` |
| `cvc5__cli__regress0__seq__issue6005-no-strings-exp.smt2` | ALL | sat | expect-comment | decided (agrees) | `seq.extract` |
| `cvc5__cli__regress0__seq__nested-const-unsat.smt2` | ALL | unsat | expect-comment | decided (agrees) | `seq.suffixof`, `seq.unit`, `str.len` |
| `cvc5__cli__regress0__seq__proj-issue384-subtypes.smt2` | ALL | unsat | set-info | decided (agrees) | `seq.len`, `seq.suffixof`, `seq.unit`, `seq.update` |
| `cvc5__cli__regress0__seq__proj-issue559-unit-inj.smt2` | ALL | unsat | set-info | decided (agrees) | `seq.prefixof`, `seq.suffixof`, `seq.unit` |
| `cvc5__cli__regress0__seq__proj-issue586-nth-update-no-fact-2.smt2` | ALL | sat | expect-comment | decided (agrees) | `seq.nth`, `seq.unit`, `seq.update` |
| `cvc5__cli__regress0__seq__proj-issue586-nth-update-no-fact.smt2` | ALL | sat | expect-comment | decided (agrees) | `seq.nth`, `seq.unit`, `seq.update` |
| `cvc5__cli__regress0__seq__proj-issue653.smt2` | ALL | sat | set-info | decided (agrees) | `seq.unit` |
| `cvc5__cli__regress0__seq__proj-issue665-nested-const.smt2` | ALL | sat | expect-comment | decided (agrees) | `seq.contains`, `seq.replace`, `seq.suffixof`, `seq.unit` |
| `cvc5__cli__regress0__seq__proj-issue708-explain.smt2` | ALL | sat | expect-comment | decided (agrees) | `seq.contains`, `seq.rev`, `seq.unit` |
| `cvc5__cli__regress0__seq__proj-issue747-cmi-len-split.smt2` | ALL | sat | expect-comment | decided (agrees) | `seq.replace_all`, `seq.suffixof`, `seq.unit` |
| `cvc5__cli__regress0__seq__query0-subtype-skel.smt2` | ALL | sat | set-info | decided (agrees) | `str.update` |
| `cvc5__cli__regress0__seq__query1-subtype.smt2` | ALL | sat | expect-comment | decided (agrees) | `seq.empty`, `seq.unit`, `str.update` |
| `cvc5__cli__regress0__seq__query2-subtype.smt2` | ALL | sat | expect-comment | decided (agrees) | `seq.nth`, `seq.unit`, `str.update` |
| `cvc5__cli__regress0__seq__seq-eval-bug.smt2` | ALL | unsat | expect-comment | decided (agrees) | `seq.unit`, `str.contains` |
| `cvc5__cli__regress0__seq__seq-eval-contains.smt2` | ALL | unsat | expect-comment | decided (agrees) | `seq.contains`, `seq.unit` |
| `cvc5__cli__regress0__seq__seq-eval-extract.smt2` | ALL | unsat | expect-comment | decided (agrees) | `seq.empty`, `seq.extract`, `seq.unit` |
| `cvc5__cli__regress0__seq__seq-eval-replace-all.smt2` | ALL | unsat | expect-comment | unknown | `seq.empty`, `seq.replace_all`, `seq.unit` |
| `cvc5__cli__regress0__seq__seq-ex1.smt2` | QF_UFSLIA | sat | set-info | decided (agrees) | — |
| `cvc5__cli__regress0__seq__seq-nth.smt2` | ALL | sat | expect-comment | decided (agrees) | `seq.len`, `seq.nth` |
| `cvc5__cli__regress0__seq__seq-types.smt2` | ALL | unsat | expect-comment | unknown | `seq.at`, `seq.len`, `seq.nth`, `seq.unit` |
| `cvc5__cli__regress0__seq__seqa-model-unsound-dd.smt2` | ALL | unsat | expect-comment | decided (agrees) | `seq.len`, `seq.nth`, `seq.unit` |
| `cvc5__cli__regress0__seq__update-eq-unsat.smt2` | ALL | unsat | expect-comment | decided (agrees) | `seq.unit`, `seq.update`, `str.len` |
| `cvc5__cli__regress0__seq__update-eq.smt2` | QF_UFSLIA | unsat | set-info | decided (agrees) | `seq.nth`, `seq.unit`, `seq.update` |
| `cvc5__cli__regress0__seq__wrong-model-020322.smt2` | ALL | sat | set-info | decided (agrees) | `seq.nth`, `seq.unit`, `str.update` |
| `cvc5__cli__regress1__seq__issue8148-const-mv.smt2` | ALL | sat | set-info | decided (agrees) | `seq.empty`, `seq.nth` |
| `cvc5__cli__regress1__seq__issue8936-nth-eager-red.smt2` | ALL | unsat | expect-comment | unknown | `seq.nth` |
| `cvc5__cli__regress1__seq__proj-issue733-mbqi-w.smt2` | ALL | sat | expect-comment | decided (agrees) | `seq.at`, `seq.rev` |
