# Source Clauses

These clauses are invented example policy text. They are intentionally small so
that every formalized obligation can cite a source sentence.

## Rule 6(a): Equivalent Local Categories

Applicants in the `resident` category and applicants in the `in_state` category
are treated as the same local category for priority-review decisions.

## Rule 6(b): Nonlocal Category

Applicants in the `nonresident` category are not in the local category.

## Rule 6(c): Priority Program

An applicant receives priority review exactly when the applicant is in a local
category and the program is `emergency_housing`.

## Rule 6(d): Category Uniformity

Equivalent applicant categories must receive the same priority-review result
for the same program.

## Rule 6(e): Implementation

An implementation of this rule computes:

```text
canonical_category(resident) = local
canonical_category(in_state) = local
canonical_category(nonresident) = nonlocal

priority_review(category, program) =
  canonical_category(category) == local
  and program == emergency_housing
```
