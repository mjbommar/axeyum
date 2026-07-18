# Preregistered tcpip site-schedule authority-union campaign

ADR-0239 fixes this experiment before any full site-hash result is observed.

- Glaurung base: `4fce79fccd167c898fa5acad24f4b8b947ba7daa`
- Glaurung experiment: `e98c0902d8f232dee8cd6348cffab79dade3eec7`
- Six-patch mbox SHA-256:
  `934c1d82428f840711e9358d59afd526cbfed7547627ea1b62a6969b7656eb98`
- tcpip SHA-256:
  `ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea`
- Fixed work: first 15 of 338 reachable functions
- Policies: arbitrary, least unsigned, greatest unsigned, site-hash zero, and
  complementary site-hash one
- Authorities: sole Z3 and sole Axeyum binaries
- Repetitions: three per policy and authority, order balanced
- Common check wall: 250 ms
- Solve/process bounds: 300,000 solves, 1,800 seconds

Acceptance requires exact reproduction of the rejected arbitrary-model and
accepted minimum/maximum controls, exact within-policy authority parity,
identical work and canonical-choice telemetry, and an identical four-policy
finding union. Every incremental and arbitrary-model overlap partition remains
explicit.

No favorable site-policy population, union growth, recovery of prior
arbitrary-only rows, or preservation result is preselected. No full site-hash
campaign has been run at preregistration time.
