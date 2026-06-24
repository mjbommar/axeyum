(set-logic QF_S)
(set-info :status unsat)
(assert (not (= (str.replace_re_all "a1b2c" (re.range "0" "9") "X") "aXbXc")))
(check-sat)
