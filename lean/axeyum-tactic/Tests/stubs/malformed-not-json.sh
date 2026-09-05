#!/bin/sh
# A mutation-battery stub sidecar: ignores its request, prints one fixed
# response. Generated; see Tests/Mutations.lean for what each one proves.
cat >/dev/null
printf '%s\n' 'not json at all'
