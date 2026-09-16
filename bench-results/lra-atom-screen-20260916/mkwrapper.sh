#!/usr/bin/env bash
# Emits a tiny wrapper binary (shell script) that execs the real
# `smtcomp_cli` with `AXEYUM_LRA_ATOM_SCREEN` fixed to one value, so
# `scripts/route-ownership-20260915/recheck-movers.sh` (which takes two
# BINARIES and refuses if their sha256 matches) can be pointed at the two
# arms of this lane's env-var lever. Two wrappers with different baked-in
# values necessarily have different sha256, satisfying that guard for real
# (not by coincidence -- it is the mechanism-liveness check screen-ab.sh
# also performs, just expressed as a distinct-file check instead of a
# distinct-config-digest check).
#
# Usage: mkwrapper.sh <real_bin> <screen_value> <out_path>
set -eu
REAL="$1"; VAL="$2"; OUT="$3"
cat > "$OUT" <<EOF
#!/usr/bin/env bash
exec env AXEYUM_LRA_ATOM_SCREEN=$VAL "$REAL" "\$@"
EOF
chmod +x "$OUT"
