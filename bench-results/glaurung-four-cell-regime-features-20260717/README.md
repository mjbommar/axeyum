# Glaurung four-cell query-feature attribution

- Date: 2026-07-17
- Input: the accepted DptfDevGen, vwififlt, IntcSST, and SurfacePen N=5
  four-cell reports
- Analysis unit: 9,526 stable ordered check occurrences
- Tool: `scripts/analyze-glaurung-regime-features.py`

This artifact is the first descriptive explanation pass over ADR-0217's two
Axeyum wins, one tie, and one Z3 win. The analyzer revalidates all 20 raw
ordered traces, verifies fixed-work identity and every hash-addressed SMT-LIB
query, and joins each occurrence's paired cold/warm ratio to its outcome,
purpose, warm execution class, active constraints, query reuse frequency, and
bounded lexical formula-shape features.

It does not fit a classifier or claim causality. Ratios remain paired geometric
means across five repetitions; values greater than one favor Axeyum.

## Main result

Formula size is not the regime boundary. Median query size ranges from 4.8 KiB
on the winning IntcSST driver through 27.5 KiB on parity vwififlt, while the
losing Dptf driver sits between them at 6.1 KiB. Within every driver, larger
queries correlate negatively with Axeyum's warm ratio (Spearman -0.15 to
-0.73), but size does not explain the cross-driver reversal.

Outcome and check purpose are materially more informative:

| Driver | SAT warm Z3/Axeyum | UNSAT warm Z3/Axeyum | Retained-only warm Z3/Axeyum |
|---|---:|---:|---:|
| DptfDevGen | 1.5297x | 0.3324x | 0.7552x |
| vwififlt | 1.1634x | 0.7887x | 0.9937x |
| IntcSST | 1.7693x | 0.9707x | 1.4763x |
| SurfacePen | 1.5098x | 2.0382x | 1.4883x |

Every driver favors Axeyum on SAT occurrences. UNSAT behavior ranges from a
strong Z3 advantage on Dptf to a strong Axeyum advantage on SurfacePen. The
IntcSST and SurfacePen wins survive after excluding the small warm-created
population, so they are not session-creation artifacts.

Address-concretization checks favor Axeyum on all four drivers (1.47x--3.76x).
Value-witness checks favor Z3 on Dptf, vwififlt, and IntcSST (0.31x--0.70x),
but favor Axeyum on SurfacePen (1.75x). Exact-query occurrence frequency has a
positive within-driver Spearman correlation with warm Axeyum advantage in all
four drivers (+0.32 to +0.63), consistent with—but not proving—a reuse effect.

Marginal standardization makes the composition effect visible. Reweighting
each driver's SAT/UNSAT strata to the pooled 71.4%/28.6% distribution moves
Dptf from 0.7875x observed to 0.9884x. Reweighting its six purpose strata to
the pooled purpose mix moves it to 1.1529x. The corresponding purpose-adjusted
ratios are 1.2183x vwififilt, 1.4898x IntcSST, and 1.7484x SurfacePen. These are
descriptive reweighted geometric means without confidence intervals; they do
not establish a counterfactual or independent causal effect.

## Consequence

The honest publication regime is currently:

- Axeyum has a measured warm advantage on retained IntcSST and SurfacePen;
- query outcome, consumer purpose, and exact-query reuse composition explain a
  material part of aggregate driver behavior;
- lexical size/operator counts alone do not provide a stable causal boundary;
  and
- the next attribution must record per-check rewrite/AIG/CNF/SAT work and
  timing, then compare like outcome/purpose/reuse strata across drivers.

`report.json` contains driver and pooled feature distributions, Spearman
correlations, tie-preserving quantile bins, outcome/purpose/reuse partitions,
and marginal composition controls. `occurrences.csv` contains the complete
9,526-row joined table without raw formulas.

Artifact SHA-256 values:

- `report.json`:
  `aa47bddb1c27a3f45b7c22868ed3fd5d43062b20931c4e9a7afb56f276c2d50a`
- `occurrences.csv`:
  `4dcf2b05e7157f262cafb338fb33183d8d63829ae406fe1d86fc13c6394187a7`

The restricted raw traces remain outside git at the paths recorded by the
four input reports.
