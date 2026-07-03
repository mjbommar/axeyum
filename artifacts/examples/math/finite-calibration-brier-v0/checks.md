# Checks

All replay rows are deterministic over the committed exact rational table.

- `probability-forecast-table-witness`: replays the six probability forecasts
  and recomputes class counts.
- `calibration-bin-witness`: applies the fixed `p < 1/2` / `p >= 1/2` split
  and recomputes average prediction, observed positive rate, absolute gap, and
  weighted gap for each bin.
- `expected-calibration-error-witness`: sums the weighted gaps to obtain
  expected calibration error `1/10`.
- `brier-score-witness`: recomputes per-row residuals, squared errors, the
  total squared error `71/50`, and mean Brier score `71/300`.
- `bad-brier-score-rejected`: replay-only rejection of the malformed claim
  that the Brier score is `1/5`.
- `qf-lra-bad-brier-score`: checked QF_LRA/Farkas rejection of the scalar
  contradiction `300*brier = 71` and `5*brier = 1`.
- `general-calibration-brier-theory-lean-horizon`: boundary row for calibration
  theory, binning policy, scoring-rule theorems, statistical uncertainty, and
  floating-point implementations.

## Trust Boundary

Trusted:

- exact replay of the committed probability/label table;
- exact rational replay of the fixed calibration-bin and Brier-score
  definitions;
- independent checking of the Farkas certificate for the malformed scalar row.

Not trusted by this pack:

- calibration of any model family;
- optimal or canonical bin selection;
- proper-scoring-rule theorem coverage;
- confidence intervals or sampling guarantees;
- floating-point classifier or metric implementation behavior.
