# Attempt 1: source-identity drift

The first exact ADR-0239 campaign attempt stopped after the arbitrary-model
and minimum-policy controls. The arbitrary-model control reproduced its
expected rejected result. All six minimum-policy processes reproduced 110
findings, ordered-list SHA-256
`e65723913d7c627e47c483848178ed122f7cfe2808f866c584bf35c943620dd3`,
80,563 solves, and the exact preregistered canonical telemetry.

The minimum report nevertheless records `accepted: false` because a concurrent
tracked edit to the main Axeyum planning documentation changed source identity
during measurement. The runner failed closed before maximum, site-hash-zero,
or site-hash-one was observed. This attempt is therefore inadmissible campaign
evidence; its exact outputs are retained only as provenance for the stopped
attempt.

The unchanged protocol is rerun from a detached Axeyum worktree at preregistration
commit `57ee6720`. This isolates source identity from unrelated workspace writes;
it does not change source, input, policies, seeds, order, fixed work, or resource
bounds.

## Retained file hashes

```text
0aafd490e96e8ff22c4a5f0bbb34f006bcd7431498f3f057750ace83b0d99434  any-model-report.json
510f43fb30c4a86f64578d275fc22d25e975409a8f455e9b9315b1c370037f8f  any-model.stderr.log
e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  any-model.stdout.log
c1519b06437c89756b6d2fc02070a0f6043165d8bd30c1b8622875c50fe2d8b6  min-unsigned-report.json
fb805f19ac3eea4aeff329f458483aeb1b96059518f090b414e29f360ba3fa97  min-unsigned.stderr.log
e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  min-unsigned.stdout.log
```
