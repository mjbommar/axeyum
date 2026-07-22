class Track:
    SingleQuery = "SingleQuery"
    Parallel = "Parallel"


class Division:
    QF_Bitvec = "QF_Bitvec"
    QF_LinearIntArith = "QF_LinearIntArith"


class Logic:
    QF_AUFBVLIA = "QF_AUFBVLIA"
    QF_BV = "QF_BV"
    QF_IDL = "QF_IDL"
    QF_LIA = "QF_LIA"


class Config:
    removed_benchmarks = [
        {
            "logic": int(Logic.QF_BV),
            "family": "2024-old/nested",
            "name": "removed.smt2",
        }
    ]


tracks: dict[Track, dict[Division, set[Logic]]] = {
    Track.SingleQuery: {
        Division.QF_Bitvec: {Logic.QF_BV},
        Division.QF_LinearIntArith: {Logic.QF_IDL, Logic.QF_LIA},
    },
    Track.Parallel: {
        Division.QF_Bitvec: {Logic.QF_AUFBVLIA, Logic.QF_BV},
    },
}
