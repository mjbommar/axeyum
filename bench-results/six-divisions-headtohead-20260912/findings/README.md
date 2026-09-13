# Findings — defects this board found, none of them fixed here

This is a **measurement lane**. Nothing below is fixed in this branch: a board
row and a behaviour change in one branch cannot be told apart afterwards. Each
finding carries a repro so it can be its own lane.

---

## 1. `(declare-sort Set 0)` is refused, and the error names `_` instead of `Set`

**Repro — two lines, committed as `declare-sort-Set.smt2`:**

```smt2
(declare-sort Set 0)
(declare-fun insert (Set Int) Set)
(check-sat)
```

```
; route-trail … {"route":"fd:parse","outcome":"declined","reason":"unsupported",
                 "detail":"unsupported: sort `_`"}
unknown
```

The front door declines at `fd:parse`, `attempts=2`, `bound_by=fd:parse`,
`total_ms=0`. Declaring an uninterpreted sort named `Set` is **legal SMT-LIB
2.6** — `Set` is not a standard builtin sort; sets are a cvc5 extension — so
this is a refusal of a valid input, not a strictness choice.

**The message is the worse half.** It names ``sort `_` ``, a sort that does not
occur anywhere in the file: the 29-line benchmark that surfaced this
(`AUFLIA/misc/set3.smt2`) contains no `_` character at all. Nobody reading that
error could find the cause. The finding took a line-by-line delta-minimisation
to locate, on a file small enough to read in full.

**It is the NAME, not the shape.** Same file with the sort renamed decides `sat`
in milliseconds. Probing 17 sort names through the identical two-line template:

| name | result |
|---|---|
| `Set` | `unknown` — ``unsupported: sort `_` `` |
| `Seq` | `unknown` — ``syntax error: declare-sort: `Seq` is a builtin …`` |
| `String` | `unknown` — ``syntax error: declare-sort: `String` is a builtin …`` |
| `Array` `RegLan` `Bag` `List` `U` `Elem` `Pair` `Tuple` `Relation` `Heap` `Map` `Field` `Ref` `Obj` | `sat` |

`Seq` and `String` are genuine SMT-LIB builtins and refusing to redeclare them
is defensible. `Set` is not, and it is the only one of the three whose message
does not say which sort it means.

**Size it honestly: this is a bug, not a coverage lever.** Across all 27,201
files of the six divisions on this board, `declare-sort` of a colliding name
appears in **3 files, all in `AUFLIA/misc`** — `set1`/`set2`/`set3`. One of them
landed in the pinned 200 and is this board's single terminal internal error. Fix
it because a wrong error message on legal input costs future diagnosis time, not
because it moves a row.

**Soundness: not affected.** It returns `unknown`.

---

## 2. `mbqi` hands an uninterpreted sort to the BV backend and declines there

24 of AUFLIA's 79 winnable files end on:

```
give-up kind=Incomplete detail=mbqi declined an unsupported fragment:
  term #173 has sort (Uninterpreted 1) that the pure-Rust BV backend cannot bit-blast
```

These rows are **classified** under ADR-1941 — no `route-open` segment,
`attempts=19` — so the reason is real, not an artifact of a truncated dispatch.
It is the second-largest single reason in the division after e-matching round
exhaustion, and it is a different kind of thing: the query reached a model-based
quantifier-instantiation route, and that route declined because a *model
construction step* routed an uninterpreted sort into a bit-blaster.

Not investigated further here. The pinned population is
`winnable/AUFLIA.txt`, and the 24 rows are greppable out of
`census/AUFLIA.tsv` by that detail string.
