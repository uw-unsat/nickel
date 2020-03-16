; example from https://emina.github.io/rosette/

(set-logic QF_BV)
(declare-fun r () Bool)
(declare-fun o () Bool)
(declare-fun s () Bool)
(declare-fun e () Bool)
(declare-fun t () Bool)

(assert (and r o (or s e (not t)) (not e)))
(check-sat)

(exit)
