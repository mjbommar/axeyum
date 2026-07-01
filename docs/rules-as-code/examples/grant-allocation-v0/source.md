# Source Clauses

These clauses are invented example policy text. They are intentionally small so
that every formalized obligation can cite a source sentence.

## Rule 5(a): Total Allocation Balance

The shelter share, clinic share, and administrative share must sum to exactly
one unit of available grant funding.

## Rule 5(b): Shelter Minimum

The shelter bucket must receive at least one half of the available funding.

## Rule 5(c): Clinic Minimum

The clinic bucket must receive at least one quarter of the available funding.

## Rule 5(d): Administrative Cap

The administrative bucket must receive no more than one quarter of the
available funding.

## Rule 5(e): Nonnegative Shares

No allocation bucket may receive a negative share.

## Rule 5(f): Implementation

An implementation of this rule computes:

```text
balanced = shelter_share + clinic_share + admin_share == 1
compliant = balanced
            && shelter_share >= 1/2
            && clinic_share >= 1/4
            && admin_share <= 1/4
            && shelter_share >= 0
            && clinic_share >= 0
            && admin_share >= 0
```
