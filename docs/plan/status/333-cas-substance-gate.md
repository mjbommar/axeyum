# Lane 333 — CAS substance gate

<!-- plan-section: lane-status -->

**Status: IN PROGRESS (first commit, incomplete).**

Deficiency: `scripts/validate-facts.py`'s `classify_cas_certificate_checker`
returns `kernel-reconstructed` when an executed `cargo test`/`cargo run`
segment merely NAMES `axeyum-lean-kernel`. It never inspects what the kernel
was asked to check, so the headline
`cas-certificate: 42 total -- kernel-reconstructed 14, cas-internal 28`
moves for a reconstruction with no discriminating content.

Work in progress; measurement table and gate to follow in later commits.
