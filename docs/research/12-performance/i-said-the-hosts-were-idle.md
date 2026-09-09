# I said the compute hosts were idle. They were not, because of me.

Recorded 2026-09-08.

## What I told two lanes

"s5, s6 and s7 are idle 16-core hosts" — written into several briefs, and
repeated to the user, as the reason to measure there instead of on the dev box.

It was true when I first checked. It stopped being true the moment I dispatched
four lanes and told each of them to use those hosts. **I never re-checked, and
I kept quoting the original reading.**

## What it cost

A lane took me at my word, ran the control anyway, and found a wall-clock noise
floor **worse than the box I had told it to avoid**:

| instance | min | max | spread |
|---|---:|---:|---:|
| bitblast_20x14 | 0.220 | 0.560 | **+154.5%** |
| rado-r4-a3-b1 | 0.989 | 1.714 | +73.3% |
| rado-r4-a2-b2 | 0.981 | 1.673 | +70.5% |
| vdw-2-3-10 | 1.566 | 2.249 | +43.6% |

Same binary, same arm, nothing changed between samples. s5/s6/s7 were running
2, 6 and 4 `smtcomp_cli` processes at 100% CPU — all of them mine.

The lane quoted **no wall clock anywhere** in its result and reported the
deterministic counters instead, which were bit-identical across all five
repetitions. That is the only reason the sweep is usable.

## The rules

- **A host's load is a reading, not a property.** Re-measure it at dispatch
  time, in the same command that starts the work, and put the number in the
  report rather than the adjective "idle".
- **I am the largest source of contention on my own fleet.** Every brief that
  says "use the idle host" makes that host less idle. Track what I have
  dispatched where, or stop making the claim.
- **Tell lanes to run the control regardless of what I claim about the host.**
  This one did and caught me; a lane that believed me would have shipped a
  wall-clock number with a 154% noise floor under it.
