# cvc5 QF_SLIA regression slice

36 files vendored from cvc5's own strings/seq regression suite (`test/regress/cli/*/strings`, `*/seq`), 2026-09-09, roadmap item P2.5 (`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`).

Directory name matches the roadmap's exit criterion (`corpus/regression/cvc5/qf_slia/` exists) and cvc5's own `(set-logic QF_SLIA)` tag; files were bucketed here by their upstream declared logic, not by their upstream subdirectory (several originated in cvc5's `seq/` folder but declare `QF_SLIA`).

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

Run: `cargo test -p axeyum-solver --features full --test corpus_regression`. Of these 36 files: **30 decided correctly** against `:status`, **6 returned `unknown`** (a coverage gap, not a soundness bug), **0 wrong verdicts**.

## Operator coverage

40 distinct `str.*`/`seq.*`/`re.*` operators in this directory:

`re.all`, `re.allchar`, `re.comp`, `re.diff`, `re.inter`, `re.loop`, `re.none`, `re.opt`, `re.range`, `re.union`, `seq.empty`, `seq.len`, `seq.replace`, `seq.rev`, `seq.suffixof`, `seq.unit`, `str.++`, `str.at`, `str.contains`, `str.from_code`, `str.from_int`, `str.in_re`, `str.indexof`, `str.indexof_re`, `str.is_digit`, `str.len`, `str.prefixof`, `str.replace`, `str.replace_all`, `str.replace_re`, `str.replace_re_all`, `str.rev`, `str.substr`, `str.suffixof`, `str.to_code`, `str.to_int`, `str.to_lower`, `str.to_re`, `str.to_upper`, `str.update`

## Per-file status

| File | Logic | `:status` | source | verdict | operators |
|---|---|---|---|---|---|
| `cvc5__cli__regress0__seq__issue5547-seq-len-unit.smt2` | QF_SLIA | sat | expect-comment | decided (agrees) | `seq.len`, `seq.rev`, `seq.suffixof`, `seq.unit` |
| `cvc5__cli__regress0__seq__seq-2var.smt2` | QF_SLIA | sat | set-info | decided (agrees) | — |
| `cvc5__cli__regress0__seq__seq-ex5.smt2` | QF_SLIA | sat | set-info | decided (agrees) | `seq.replace`, `seq.unit` |
| `cvc5__cli__regress0__seq__seq-nemp.smt2` | QF_SLIA | sat | set-info | unknown | `seq.empty`, `seq.len` |
| `cvc5__cli__regress0__strings__code-sat-neg-one.smt2` | QF_SLIA | sat | set-info | decided (agrees) | `str.to_code` |
| `cvc5__cli__regress0__strings__indexof_re-start-index.smt2` | QF_SLIA | unsat | set-info | decided (agrees) | `str.indexof_re`, `str.to_re` |
| `cvc5__cli__regress0__strings__issue12322-pf-eager-len-re.smt2` | QF_SLIA | unsat | expect-comment | decided (agrees) | `str.in_re`, `str.len`, `str.to_re` |
| `cvc5__cli__regress0__strings__issue6643-ctn-decompose-conflict.smt2` | QF_SLIA | sat | set-info | decided (agrees) | `str.contains`, `str.replace` |
| `cvc5__cli__regress0__strings__issue6681-split-eq-strip-l.smt2` | QF_SLIA | sat | set-info | decided (agrees) | `str.++` |
| `cvc5__cli__regress0__strings__issue6834-str-eq-const-nhomog.smt2` | QF_SLIA | sat | set-info | decided (agrees) | `str.++`, `str.substr` |
| `cvc5__cli__regress0__strings__proj-issue409-re-loop-none.smt2` | QF_SLIA | unsat | set-info | unknown | `re.all`, `re.loop`, `str.from_code`, `str.in_re` |
| `cvc5__cli__regress0__strings__re-in-rewrite.smt2` | QF_SLIA | unsat | set-info | unknown | `re.allchar`, `re.comp`, `re.inter`, `str.in_re`, `str.to_re` |
| `cvc5__cli__regress0__strings__re.all.smt2` | QF_SLIA | unsat | set-info | unknown | `re.all`, `str.in_re`, `str.prefixof`, `str.to_re` |
| `cvc5__cli__regress0__strings__repl-all-non-const-range.smt2` | QF_SLIA | sat | expect-comment | decided (agrees) | `str.replace_all` |
| `cvc5__cli__regress0__strings__replace-find-base.smt2` | QF_SLIA | unsat | set-info | decided (agrees) | `str.++`, `str.replace` |
| `cvc5__cli__regress0__strings__rw_508_suffixof.smt2` | QF_SLIA | unsat | expect-comment | decided (agrees) | `str.replace`, `str.suffixof` |
| `cvc5__cli__regress0__strings__rw_555.smt2` | QF_SLIA | unsat | expect-comment | decided (agrees) | `str.replace` |
| `cvc5__cli__regress0__strings__rw_65.smt2` | QF_SLIA | unsat | expect-comment | decided (agrees) | `str.at`, `str.indexof` |
| `cvc5__cli__regress0__strings__simple-nth-fail.smt2` | QF_SLIA | sat | set-info | decided (agrees) | `str.from_code`, `str.to_int` |
| `cvc5__cli__regress0__strings__str-pred-small-rw_429.smt2` | QF_SLIA | unsat | expect-comment | decided (agrees) | `str.from_int` |
| `cvc5__cli__regress0__strings__str-pred-small-rw_538.smt2` | QF_SLIA | unsat | expect-comment | decided (agrees) | `str.replace` |
| `cvc5__cli__regress0__strings__strip-endpoint-itos.smt2` | QF_SLIA | sat | set-info | decided (agrees) | `str.contains`, `str.from_int` |
| `cvc5__cli__regress1__strings__issue10195.smt2` | QF_SLIA | sat | set-info | decided (agrees) | `re.allchar`, `re.none`, `str.contains`, `str.from_int`, `str.indexof_re`, `str.replace_re_all`, `str.update` |
| `cvc5__cli__regress1__strings__issue6057-replace-re-all-jiwonparc.smt2` | QF_SLIA | unsat | set-info | decided (agrees) | `re.opt`, `str.++`, `str.contains`, `str.in_re`, `str.replace_re_all`, `str.to_re` |
| `cvc5__cli__regress1__strings__issue6057-replace-re.smt2` | QF_SLIA | sat | set-info | decided (agrees) | `re.union`, `str.in_re`, `str.replace_re`, `str.suffixof`, `str.to_re` |
| `cvc5__cli__regress1__strings__issue6203-6-replace-re.smt2` | QF_SLIA | sat | set-info | decided (agrees) | `re.diff`, `re.range`, `re.union`, `str.in_re`, `str.replace_re`, `str.to_re` |
| `cvc5__cli__regress1__strings__issue8944-sygus-inst.smt2` | QF_SLIA | sat | expect-comment | unknown | `re.range`, `str.at`, `str.from_code`, `str.in_re`, `str.is_digit`, `str.len`, `str.replace_all`, `str.rev`, `str.substr` |
| `cvc5__cli__regress1__strings__issue9269-rei-nconst.smt2` | QF_SLIA | sat | set-info | decided (agrees) | `str.++`, `str.in_re`, `str.replace_all`, `str.to_re` |
| `cvc5__cli__regress1__strings__simple-re-consume.smt2` | QF_SLIA | sat | set-info | decided (agrees) | `str.++`, `str.in_re`, `str.to_re` |
| `cvc5__cli__regress1__strings__str-code-unsat-2.smt2` | QF_SLIA | unsat | set-info | decided (agrees) | `str.len`, `str.to_code` |
| `cvc5__cli__regress1__strings__to_upper_12.smt2` | QF_SLIA | sat | expect-comment | decided (agrees) | `str.len`, `str.to_lower`, `str.to_upper` |
| `cvc5__cli__regress2__strings__issue6636-replace-re-all.smt2` | QF_SLIA | unsat | set-info | decided (agrees) | `re.allchar`, `str.replace_re_all`, `str.to_re` |
| `cvc5__cli__regress2__strings__issue6637-replace-re-all.smt2` | QF_SLIA | unsat | set-info | decided (agrees) | `str.len`, `str.replace_re_all`, `str.to_re` |
| `cvc5__cli__regress2__strings__issue6639-replace-re-all.smt2` | QF_SLIA | unsat | set-info | unknown | `re.comp`, `str.in_re`, `str.replace_re_all`, `str.to_re` |
| `cvc5__cli__regress2__strings__range-perf.smt2` | QF_SLIA | sat | expect-comment | decided (agrees) | `re.allchar`, `re.loop`, `re.range`, `str.in_re`, `str.to_re` |
| `cvc5__cli__regress3__strings__issue8926-sygus-inst.smt2` | QF_SLIA | sat | expect-comment | decided (agrees) | `str.len`, `str.prefixof`, `str.rev`, `str.substr`, `str.to_code`, `str.to_int` |
