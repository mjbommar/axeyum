#!/usr/bin/env bash
# SILENT-HANG -- re-run the two representatives whose FIRST profile recorded
# zero samples ("Permission error mapping pages" against `perf_event_mlock_kb`,
# hit because five `perf record`s ran at once).  Two at a time, with `-m 256`.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
bash "$W/perf-fp.sh" 'UFNIA/lahiri-cav09-storm-queries/mqueue_example_2_2_2_4.smt2' fp-mqueue 9 60 > "$W/prof/fp-mqueue.log" 2>&1 &
bash "$W/perf-fp.sh" 'UFNIA/spec_sharp/test14-DafnyAst.ssc.30.Microsoft.Dafny.ClassType.Boogie.ContractConsistencyCheck.ToString.smt2' fp-dafny 10 60 > "$W/prof/fp-dafny.log" 2>&1 &
wait
echo RETRY-DONE
