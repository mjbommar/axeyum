# ADR-0521: Do not take Cauchy across the connected top characters

Status: accepted
Date: 2026-08-19
Index-summary: Retain phase correlation across the connected top Hayes characters because their exact second moment is far too large for direct Cauchy

## Context

ADR-0518 leaves one signed sum over the top exact-conductor characters.  A
single Cauchy--Schwarz inequality would prove (CRT) if

```text
(number of top characters) sum_top |S_chi(n)|^2 <= 2^(4ell-4).
```

Axeyum already computes the exact second moment of each conductor family, so
this possibility can be tested without approximating individual characters.

## Decision

Add `connected_top_second_moment_cauchy`, summing the exact conductor moments
before applying Cauchy and reporting the exact maximum moment and saving factor
required by (CRT).  Do not use direct family `L2` as the selected proof route
unless a new theorem supplies that full saving.

## Evidence

At `ell=12`, the connected family has 4032 characters.  For degree 25 its
exact second moment is `1326053720064`; Cauchy's squared bound exceeds the
connected allowance squared by about `303.92`, requiring an integral moment
saving of `304`.  At degree 26 the exact moment is `2759328661504`, the square
ratio is about `632.42`, and the required saving is `633`.

The actual connected traces at these endpoints satisfy (CRT), so this loss is
created by discarding phase alignment, not by a large observed trace.

## Alternatives

- Characterwise Weil was already rejected by ADR-0518; it loses a factor
  asymptotic to `8ell` in amplitude.
- Direct Cauchy replaces that loss by a large second-moment loss but still
  erases the signs that make the connected trace small.
- A higher-moment inequality without a phase-sensitive structural lemma has
  the same defect and is not selected merely for producing a larger table.

## Consequences

- The next argument must preserve signed correlation between characters or
  between centered convolution orders.
- The exact second-moment report remains useful as a stopping test for future
  proposed family estimates; finite failure is not extrapolated into a
  universal asymptotic theorem.
- With the blanket supersingular Heisenberg route also refuted, the connected
  fourth-cumulant/gcd stratification is the selected fallback.
