# Attempt 1: corpus-membership rejection

The first ADR-0251 execution stopped before reading or solving any selected
query. `axeyum-bench` correctly requires the corpus root's complete `.smt2`
membership to equal the supplied manifest. The command paired the 1,024-row
holdout manifest with the 30,628-query corrected full corpus root, leaving
29,604 unlisted files. The benchmark exited 1, wrote no result artifact, and
did not observe a proof or solver outcome from the holdout.

An exact reproduction from the clean detached preregistration commit produced
byte-identical stdout and stderr. The 2,397,983-byte stderr is not committed
because it is a single diagnostic line enumerating every unlisted path; its
SHA-256 and the complete reproducing command are retained in `failure.json`.

This is a packaging/protocol rejection, not holdout evidence. The selected
manifest, its 1,024 content hashes, the two-repetition protocol, and all
resource and acceptance bounds remain unchanged. A separately preregistered
materialization step must first build a corpus root containing exactly those
selected query files and the byte-identical holdout manifest.
