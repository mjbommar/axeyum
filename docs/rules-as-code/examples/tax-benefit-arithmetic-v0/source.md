# Example Rule 3: Tax Benefit Arithmetic

This is a toy rule set for solver and replay examples. It is not a real tax
rule and is not legal or financial advice.

## Rule 3(a): Household Credit

An eligible household has a starting credit of 20 units. Each additional
household member, up to a household size of 3, adds 5 units.

## Rule 3(b): Credit Cap

The final benefit may never exceed 30 units.

## Rule 3(c): Phase-Out

If income is above the active phase-out threshold, the benefit is reduced by 2
units for each income unit above that threshold. The benefit may not go below 0.

## Rule 3(d): Effective Date

Before 2026-07-01, the active phase-out threshold is 40 income units. On and
after 2026-07-01, the active phase-out threshold is 45 income units.

## Rule 3(e): Implementation

A bounded implementation must compute the same benefit as the formal rule model
for household sizes 1 through 3 and nonnegative income in the sampled domain.
