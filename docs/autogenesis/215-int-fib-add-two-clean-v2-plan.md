# Clean `Int.fib_add_two` V2 plan

Date: 2026-08-21

V1 already selected the right mathematical cases. V2 changes only the two
normalization steps exposed by the compiler: it presents negative integer
addition directly as the three neighboring `negSucc` constructors, and it
normalizes the chosen mod-two hypothesis before simplifying the recurrence.

No new tactic search, theorem premise, representation, or target authority is
introduced. One new compile is allowed; failure again stops before export or
ledger credit.
