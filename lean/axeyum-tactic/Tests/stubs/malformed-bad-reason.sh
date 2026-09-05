#!/bin/sh
# A mutation-battery stub sidecar: ignores its request, prints one fixed
# response. Generated; see Tests/Mutations.lean for what each one proves.
cat >/dev/null
cat <<'AXEYUM_STUB_EOF'
{"protocol":"axeyum-tactic-v1","status":"declined","reason":"because-i-said-so"}
AXEYUM_STUB_EOF
