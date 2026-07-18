# Preregistered tcpip extremal coverage-union campaign

ADR-0238 fixes this experiment before its full results are observed.

- Glaurung base: `4fce79fccd167c898fa5acad24f4b8b947ba7daa`
- Glaurung experiment: `e5622623ba8d8679d7e4530ff34212a5d993f030`
- Five-patch mbox SHA-256:
  `7916ff88bfc96b7aee6d9f1e23d73632b9712469e96c811edbf8ce970196a4a2`
- tcpip SHA-256:
  `ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea`
- Fixed work: first 15 of 338 reachable functions
- Policies: arbitrary model, least unsigned, greatest unsigned
- Authorities: sole Z3 and sole Axeyum binaries
- Repetitions: three per policy and authority, order balanced
- Common check wall: 250 ms
- Solve/process bounds: 300,000 solves, 1,800 seconds

Acceptance requires exact reproduction of the rejected arbitrary-model and
accepted least-model controls, exact within-policy authority parity, identical
work and canonical-choice telemetry, and an identical least/greatest finding
union. Union size and its relationship to the arbitrary-model union are not
preselected.

The maximum-policy implementation has only completed focused engineering
tests at preregistration time. No full maximum or union result is claimed here.
