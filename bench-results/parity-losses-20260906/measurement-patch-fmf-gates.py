"""MEASUREMENT-ONLY patch, applied to a throwaway snapshot, never to the repo.

Adds two env gates to the quantified ladder so ONE binary can run both arms of
the A/B interleaved on the same machine load:

  AXEYUM_NO_UF_FMF_PROBE=1  skips the EARLY pure-UF finite-model probe rung
                            (which runs BEFORE mbqi-quick / egraph / mbqi and
                            takes up to half the remaining budget).
  AXEYUM_NO_UF_FMF_FULL=1   skips the TERMINAL finite-model rung (which runs
                            after every refuter has declined).

Unset, the binary is behaviourally identical to the shipped one.
"""

import sys

path = sys.argv[1]
src = open(path).read()

PROBE_OLD = """            if let Some(probe_config) = config_with_remaining_timeout(config, deadline)
                && let Some(model) = crate::uf_fmf::find_uf_finite_model("""
PROBE_NEW = """            if std::env::var_os("AXEYUM_NO_UF_FMF_PROBE").is_none()
                && let Some(probe_config) = config_with_remaining_timeout(config, deadline)
                && let Some(model) = crate::uf_fmf::find_uf_finite_model("""

FULL_OLD = """                    if matches!(other, CheckResult::Unknown(_))
                        && let Some(fmf_config) = config_with_remaining_timeout(config, deadline)"""
FULL_NEW = """                    if std::env::var_os("AXEYUM_NO_UF_FMF_FULL").is_none()
                        && matches!(other, CheckResult::Unknown(_))
                        && let Some(fmf_config) = config_with_remaining_timeout(config, deadline)"""

for old, new, name in ((PROBE_OLD, PROBE_NEW, "probe"), (FULL_OLD, FULL_NEW, "full")):
    n = src.count(old)
    assert n == 1, "%s anchor matched %d times, expected 1" % (name, n)
    src = src.replace(old, new)

open(path, "w").write(src)
print("patched", path)
