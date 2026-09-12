# Lane: binder-alias — a quantifier binder sort could not be a `define-sort` alias

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, binder-alias, 2026-09-11).** `queue_quantifier`
parsed every quantifier binder sort against a freshly built EMPTY alias map,
with a comment asserting that sort aliases are resolved at declaration sites
only. Every other `parse_sort` call site passed the script's real
`sort_aliases`. So `(define-sort MyInt () Int)` + `(exists ((y MyInt)) …)`
failed at PARSE while the same alias on a `declare-fun` worked.
`apply_parameterized` had the identical empty map for `(as const S)`.

Measured on a pinned 200-file sample of the SMT-LIB `FP` division
(`bench-results/parity-lists/FP.txt`, stride 13 over 2,669 files, committed
before the run): **parse 15/200 → 193/200**. The 185 recovered files are
exactly the 185 that carry both a `define-sort` and a quantifier. The 7 still
failing are `fp.rem` on the unvalidated (3,5) float format — unrelated, and
a deliberate decline.

**Decide-rate 0/200 → 46/200** at 24 s / 8 GiB, same binary settings both
sides, all 46 `unsat`. 199 of the 200 files carry `:status unknown`, so the
declared statuses cross-check nothing; the one declared `sat` file we return
`unknown` on, which is not a disagreement. I predicted zero here and was
wrong — do not repeat that guess.

**Zero disagreements**, checked rather than assumed: all 46 unsats re-run
against z3 (unsat on 45, undecided on 1) and cvc5 (declines the format outright
without `--fp-exp`). But all 46 are the (3,5) float format: we take 46 of the
list's 62 `3_5` files and **none** of its 62 `8_24` or 61 `11_53`. This is not
"23 % of `FP`" — it is most of the smallest format and none of the two real
ones. Full record in
[bench-results/fp-binder-alias-20260911/](../../../bench-results/fp-binder-alias-20260911/README.md).

Two findings beyond the brief. (1) The committed corpus is structurally blind
to this shape: 25 files use `define-sort`, 90 use a quantifier, and **none use
both** — no corpus entry could have caught it. (2) The `(as const S)` half was
first pinned by a VACUOUS test: `reduce_const_array_sexpr` rewrites `select`
and const-array `=` at the s-expression level before any sort is parsed, so
the obvious script parses with or without the fix. `distinct` is not a reduced
head; both tests now use that shape and a mutation control kills exactly one
test per reverted half.

Still open, same family, NOT fixed: `(as seq.empty S)` reads its element width
structurally from a literal `(Seq E)` (`seq_decl_elem_width`), so an alias
there still declines. `Seq` is a non-standard extension with no SMT-LIB
division, and the packed representation loses the element width, so this one
is genuinely harder than a threading change.

<!-- plan-section: landed-changes -->

| 2026-09-11 | `7777570d0` | `fix(smtlib)`: thread `sort_aliases` into term conversion — quantifier binder sorts and `(as const S)` could not be `define-sort` aliases; the SMT-LIB `FP` division went 15/200 → 193/200 parsed |
| 2026-09-11 | `35a912c01` | `bench(parity)`: pin `bench-results/parity-lists/FP.txt`, the 200-file `FP` sample, before measuring it |
| 2026-09-11 | `e14283a77` | `test(smtlib)`: mutation control found the `as const` test was vacuous; replaced with a `distinct` shape that reaches term conversion, plus `examples/parse_rate.rs` (parse rate per division, exit status depends on the finding) |
