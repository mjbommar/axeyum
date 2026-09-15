#!/usr/bin/env bash
# SILENT-HANG -- profile ONE representative of each mechanism the phase census
# split out, all at once on pinned distinct cores.
#
# These are ATTRIBUTION runs -- the question is WHICH CODE, not how fast -- so
# running five at once on five pinned cores is acceptable and is stated here
# rather than left for a reader to assume.  No timing number is quoted from
# these runs, and the binary is the frame-pointer one, which is not the binary
# any verdict in this lane comes from.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
run() { bash "$W/perf-fp.sh" "$1" "$2" "$3" "${4:-60}" > "$W/prof/$2.log" 2>&1 & }
mkdir -p "$W/prof"

#    file                                                                                     tag            core
run 'UFNIA/vcc-havoc/havoc-bench_sum.1.bar.smt2'                                               fp-havoc-sum    8
run 'UFNIA/lahiri-cav09-storm-queries/mqueue_example_2_2_2_4.smt2'                             fp-mqueue       9
run 'UFNIA/spec_sharp/test14-DafnyAst.ssc.30.Microsoft.Dafny.ClassType.Boogie.ContractConsistencyCheck.ToString.smt2' fp-dafny 10
run 'UFNIA/2019-Zohar-ic/full/int_check_bvsgt_bvadd_ltr_inv_r.smt2'                            fp-zohar       11
run 'UFNIA/sledgehammer/Hoare/z3.850818.smt2'                                                  fp-hoare       12
wait
echo ALLPROFILED
