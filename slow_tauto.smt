(declare-const x1 Bool)
(declare-const x2 Bool)
(declare-const x3 Bool)
(declare-const x4 Bool)
(assert (or x1 x2 (not x3)))
(assert (or (not x1) (not x2) x3))
(assert (or x2 x3 (not x4)))
(assert (or (not x2) (not x3) x4))
(assert (or x1 x3 x4))
(assert (or (not x1) (not x3) (not x4)))
(assert (or (not x1) x2 x4))
(assert (or x1 (not x2) (not x4)))
(check-sat)
