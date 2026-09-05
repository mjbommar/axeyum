#!/bin/sh
# A mutation-battery stub sidecar: ignores its request, prints one fixed
# response. Generated; see Tests/Mutations.lean for what each one proves.
cat >/dev/null
cat <<'AXEYUM_STUB_EOF'
{"protocol":"axeyum-tactic-v1","status":"accepted","environment_id":"lean-4.34.0-rc1:axeyum-tactic-v1","term":"@Axeyum.Shim.natAddComm a b"}
AXEYUM_STUB_EOF
