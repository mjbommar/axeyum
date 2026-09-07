"""MEASUREMENT-ONLY second patch on the throwaway snapshot.

`probe_budget` currently hands the pure-UF finite-model PROBE rung HALF the
remaining wall budget, and that rung runs BEFORE mbqi-quick / egraph / mbqi.
This makes the divisor settable so one binary can measure the cost/benefit of a
tighter probe:  AXEYUM_UF_FMF_PROBE_DIVISOR=<n>, default 2 (= shipped).
"""

import sys

path = sys.argv[1]
src = open(path).read()

OLD = """fn probe_budget(config: &SolverConfig) -> SolverConfig {
    let mut probe = config.clone();
    if let Some(t) = probe.timeout {
        probe.timeout = Some(t / 2);
    }
    probe
}"""
NEW = """fn probe_budget(config: &SolverConfig) -> SolverConfig {
    let mut probe = config.clone();
    let divisor: u32 = std::env::var("AXEYUM_UF_FMF_PROBE_DIVISOR")
        .ok()
        .and_then(|v| v.parse().ok())
        .filter(|d| *d > 0)
        .unwrap_or(2);
    if let Some(t) = probe.timeout {
        probe.timeout = Some(t / divisor);
    }
    probe
}"""

assert src.count(OLD) == 1, "probe_budget anchor matched %d times" % src.count(OLD)
open(path, "w").write(src.replace(OLD, NEW))
print("patched", path)
