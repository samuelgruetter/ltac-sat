(set-info :smt-lib-version 2.6)
(set-logic UFLIA)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/sls/sls_concat.spl:36:4-19:Possible heap access through null or dangling reference
  |)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort SetInt 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-sort FldInt 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldInt Loc) Int)
(declare-fun read$1 (FldLoc Loc) Loc)
(declare-fun ep$0 (FldLoc SetLoc Loc) Loc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun Frame$0 (SetLoc SetLoc FldLoc FldLoc) Bool)
(declare-fun Frame$1 (SetLoc SetLoc FldInt FldInt) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Axiom_13$0 () Bool)
(declare-fun Axiom_14$0 () Bool)
(declare-fun Axiom_15$0 () Bool)
(declare-fun Axiom_16$0 () Bool)
(declare-fun Axiom_17$0 () Bool)
(declare-fun Axiom_18$0 () Bool)
(declare-fun Axiom_19$0 () Bool)
(declare-fun Axiom_20$0 () Bool)
(declare-fun Axiom_21$0 () Bool)
(declare-fun Axiom_22$0 () Bool)
(declare-fun Axiom_23$0 () Bool)
(declare-fun Axiom_24$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun a$0 () Loc)
(declare-fun a_1$0 () Loc)
(declare-fun b$0 () Loc)
(declare-fun curr_2$0 () Loc)
(declare-fun curr_3$0 () Loc)
(declare-fun data$0 () FldInt)
(declare-fun lslseg_domain$0 (FldInt FldLoc Loc Loc Int) SetLoc)
(declare-fun lslseg_struct$0 (SetLoc FldInt FldLoc Loc Loc Int) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun sk_?X_11$0 () SetLoc)
(declare-fun sk_?X_12$0 () SetLoc)
(declare-fun sk_?X_13$0 () SetLoc)
(declare-fun sk_?X_14$0 () SetLoc)
(declare-fun sk_?X_15$0 () SetLoc)
(declare-fun sk_?X_16$0 () SetLoc)
(declare-fun sk_?X_17$0 () SetLoc)
(declare-fun sk_?X_18$0 () SetLoc)
(declare-fun sk_?X_19$0 () SetLoc)
(declare-fun sk_?X_20$0 () SetLoc)
(declare-fun sk_?X_21$0 () SetLoc)
(declare-fun t$0 () Loc)
(declare-fun t_1$0 () Loc)
(declare-fun t_2$0 () Loc)
(declare-fun t_3$0 () Loc)
(declare-fun t_4$0 () Loc)
(declare-fun t_5$0 () Loc)
(declare-fun uslseg_domain$0 (FldInt FldLoc Loc Loc Int) SetLoc)
(declare-fun uslseg_struct$0 (SetLoc FldInt FldLoc Loc Loc Int) Bool)
(declare-fun x$0 () Int)
(declare-fun x_5$0 () Int)

(assert (= (ep$0 next$0 FP_1$0 curr_3$0) t_5$0))

(assert (= (ep$0 next$0 FP_1$0 curr_2$0) t_4$0))

(assert (= (ep$0 next$0 FP_1$0 b$0) t_3$0))

(assert (= (ep$0 next$0 FP_1$0 a_1$0) t_2$0))

(assert (= (ep$0 next$0 FP_1$0 a$0) t_1$0))

(assert (= (ep$0 next$0 FP_1$0 null$0) t$0))

(assert (forall ((?f FldLoc)) (= (read$1 ?f null$0) null$0)))

(assert (forall ((x Loc) (y Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))))

(assert (forall ((X SetLoc) (Y SetLoc) (x Loc))
        (or (and (in$0 x X) (in$0 x (setminus$0 X Y)) (not (in$0 x Y)))
            (and (or (in$0 x Y) (not (in$0 x X)))
                 (not (in$0 x (setminus$0 X Y)))))))

(assert (forall ((X SetLoc) (Y SetLoc) (x Loc))
        (or (and (in$0 x X) (in$0 x Y) (in$0 x (intersection$0 X Y)))
            (and (or (not (in$0 x X)) (not (in$0 x Y)))
                 (not (in$0 x (intersection$0 X Y)))))))

(assert (forall ((X SetLoc) (Y SetLoc) (x Loc))
        (or (and (in$0 x (union$0 X Y)) (or (in$0 x X) (in$0 x Y)))
            (and (not (in$0 x X)) (not (in$0 x Y))
                 (not (in$0 x (union$0 X Y)))))))

(assert (forall ((x Loc)) (not (in$0 x emptyset$0))))

(assert (or (and (Btwn$0 next$0 a$0 null$0 null$0) Axiom_14$0 Axiom_13$0)
    (not (lslseg_struct$0 sk_?X_21$0 data$0 next$0 a$0 null$0 x$0))))

(assert (or (not Axiom_15$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (<= (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next$0 l1 l2 curr_2$0))
                (not (in$0 l1 sk_?X_18$0)) (not (in$0 l2 sk_?X_18$0))))))

(assert (or (not Axiom_16$0)
    (forall ((l1 Loc))
            (or (<= (read$0 data$0 l1) (read$0 data$0 curr_2$0))
                (not (in$0 l1 sk_?X_18$0))))))

(assert (or (and (Btwn$0 next$0 a_1$0 curr_3$0 curr_3$0) Axiom_18$0 Axiom_17$0)
    (not
         (lslseg_struct$0 sk_?X_11$0 data$0 next$0 a_1$0 curr_3$0
           (read$0 data$0 curr_3$0)))))

(assert (or (not Axiom_19$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (<= (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next$0 l1 l2 null$0)) (not (in$0 l1 sk_?X_20$0))
                (not (in$0 l2 sk_?X_20$0))))))

(assert (or (not Axiom_20$0)
    (forall ((l1 Loc))
            (or (<= x$0 (read$0 data$0 l1)) (not (in$0 l1 sk_?X_20$0))))))

(assert (or (and (Btwn$0 next$0 curr_2$0 null$0 null$0) Axiom_22$0 Axiom_21$0)
    (not (lslseg_struct$0 sk_?X_16$0 data$0 next$0 curr_2$0 null$0 x$0))))

(assert (or (not Axiom_23$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (<= (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next$0 l1 l2 null$0)) (not (in$0 l1 sk_?X_13$0))
                (not (in$0 l2 sk_?X_13$0))))))

(assert (or (not Axiom_24$0)
    (forall ((l1 Loc))
            (or (<= (read$0 data$0 l1) x_5$0) (not (in$0 l1 sk_?X_13$0))))))

(assert (= (read$1 next$0 curr_3$0) null$0))

(assert (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= curr_2$0 a$0))

(assert (Frame$1 FP_1$0 Alloc$0 data$0 data$0))

(assert (= Alloc$0 (union$0 FP_2$0 Alloc$0)))

(assert (= emptyset$0 emptyset$0))

(assert (= sk_?X_11$0
  (lslseg_domain$0 data$0 next$0 a_1$0 curr_3$0 (read$0 data$0 curr_3$0))))

(assert (= sk_?X_13$0 (lslseg_domain$0 data$0 next$0 curr_3$0 null$0 x_5$0)))

(assert (= sk_?X_14$0 (union$0 sk_?X_12$0 sk_?X_13$0)))

(assert (lslseg_struct$0 sk_?X_13$0 data$0 next$0 curr_3$0 null$0 x_5$0))

(assert (= emptyset$0 emptyset$0))

(assert (= sk_?X_15$0 (union$0 sk_?X_17$0 sk_?X_16$0)))

(assert (= sk_?X_16$0 (lslseg_domain$0 data$0 next$0 curr_2$0 null$0 x$0)))

(assert (= sk_?X_18$0
  (lslseg_domain$0 data$0 next$0 a$0 curr_2$0 (read$0 data$0 curr_2$0))))

(assert (lslseg_struct$0 sk_?X_16$0 data$0 next$0 curr_2$0 null$0 x$0))

(assert (not (= curr_2$0 null$0)))

(assert (= sk_?X_19$0 (union$0 sk_?X_21$0 sk_?X_20$0)))

(assert (= sk_?X_20$0 (uslseg_domain$0 data$0 next$0 b$0 null$0 x$0)))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (uslseg_struct$0 sk_?X_20$0 data$0 next$0 b$0 null$0 x$0))

(assert (not (in$0 null$0 Alloc$0)))

(assert (not (in$0 curr_3$0 FP_2$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 curr_2$0)
                 (in$0 l1
                   (lslseg_domain$0 data$0 next$0 a$0 curr_2$0
                     (read$0 data$0 curr_2$0)))
                 (not (= l1 curr_2$0)))
            (and (or (= l1 curr_2$0) (not (Btwn$0 next$0 a$0 l1 curr_2$0)))
                 (not
                      (in$0 l1
                        (lslseg_domain$0 data$0 next$0 a$0 curr_2$0
                          (read$0 data$0 curr_2$0))))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 b$0 l1 null$0)
                 (in$0 l1 (uslseg_domain$0 data$0 next$0 b$0 null$0 x$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 b$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (uslseg_domain$0 data$0 next$0 b$0 null$0 x$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_3$0 l1 null$0)
                 (in$0 l1
                   (lslseg_domain$0 data$0 next$0 curr_3$0 null$0 x_5$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_3$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (lslseg_domain$0 data$0 next$0 curr_3$0 null$0 x_5$0)))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (or (in$0 (ep$0 ?f ?X ?x) ?X) (= ?x (ep$0 ?f ?X ?x)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) (ep$0 ?f ?X ?x))))

(assert (or (not Axiom_13$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (<= (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next$0 l1 l2 null$0)) (not (in$0 l1 sk_?X_21$0))
                (not (in$0 l2 sk_?X_21$0))))))

(assert (or (not Axiom_14$0)
    (forall ((l1 Loc))
            (or (<= (read$0 data$0 l1) x$0) (not (in$0 l1 sk_?X_21$0))))))

(assert (or (and (Btwn$0 next$0 a$0 curr_2$0 curr_2$0) Axiom_16$0 Axiom_15$0)
    (not
         (lslseg_struct$0 sk_?X_18$0 data$0 next$0 a$0 curr_2$0
           (read$0 data$0 curr_2$0)))))

(assert (or (not Axiom_17$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (<= (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next$0 l1 l2 curr_3$0))
                (not (in$0 l1 sk_?X_11$0)) (not (in$0 l2 sk_?X_11$0))))))

(assert (or (not Axiom_18$0)
    (forall ((l1 Loc))
            (or (<= (read$0 data$0 l1) (read$0 data$0 curr_3$0))
                (not (in$0 l1 sk_?X_11$0))))))

(assert (or (and (Btwn$0 next$0 b$0 null$0 null$0) Axiom_20$0 Axiom_19$0)
    (not (uslseg_struct$0 sk_?X_20$0 data$0 next$0 b$0 null$0 x$0))))

(assert (or (not Axiom_21$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (<= (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next$0 l1 l2 null$0)) (not (in$0 l1 sk_?X_16$0))
                (not (in$0 l2 sk_?X_16$0))))))

(assert (or (not Axiom_22$0)
    (forall ((l1 Loc))
            (or (<= (read$0 data$0 l1) x$0) (not (in$0 l1 sk_?X_16$0))))))

(assert (or (and (Btwn$0 next$0 curr_3$0 null$0 null$0) Axiom_24$0 Axiom_23$0)
    (not (lslseg_struct$0 sk_?X_13$0 data$0 next$0 curr_3$0 null$0 x_5$0))))

(assert (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))))

(assert (= a_1$0 a$0))

(assert (= x_5$0 x$0))

(assert (Frame$0 FP_1$0 Alloc$0 next$0 next$0))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= emptyset$0 (intersection$0 sk_?X_12$0 sk_?X_13$0)))

(assert (= sk_?X_12$0 sk_?X_11$0))

(assert (= sk_?X_14$0
  (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0))))

(assert (lslseg_struct$0 sk_?X_11$0 data$0 next$0 a_1$0 curr_3$0
  (read$0 data$0 curr_3$0)))

(assert (not (= curr_3$0 null$0)))

(assert (= emptyset$0 (intersection$0 sk_?X_17$0 sk_?X_16$0)))

(assert (= sk_?X_15$0 FP_1$0))

(assert (= sk_?X_17$0 sk_?X_18$0))

(assert (= FP$0 (union$0 FP_1$0 FP$0)))

(assert (lslseg_struct$0 sk_?X_18$0 data$0 next$0 a$0 curr_2$0
  (read$0 data$0 curr_2$0)))

(assert (= emptyset$0 (intersection$0 sk_?X_21$0 sk_?X_20$0)))

(assert (= sk_?X_19$0 FP$0))

(assert (= sk_?X_21$0 (lslseg_domain$0 data$0 next$0 a$0 null$0 x$0)))

(assert (lslseg_struct$0 sk_?X_21$0 data$0 next$0 a$0 null$0 x$0))

(assert (not (= a$0 null$0)))

(assert (not (in$0 null$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1 (lslseg_domain$0 data$0 next$0 a$0 null$0 x$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (lslseg_domain$0 data$0 next$0 a$0 null$0 x$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a_1$0 l1 curr_3$0)
                 (in$0 l1
                   (lslseg_domain$0 data$0 next$0 a_1$0 curr_3$0
                     (read$0 data$0 curr_3$0)))
                 (not (= l1 curr_3$0)))
            (and (or (= l1 curr_3$0) (not (Btwn$0 next$0 a_1$0 l1 curr_3$0)))
                 (not
                      (in$0 l1
                        (lslseg_domain$0 data$0 next$0 a_1$0 curr_3$0
                          (read$0 data$0 curr_3$0))))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_2$0 l1 null$0)
                 (in$0 l1
                   (lslseg_domain$0 data$0 next$0 curr_2$0 null$0 x$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_2$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (lslseg_domain$0 data$0 next$0 curr_2$0 null$0 x$0)))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) ?y) (not (Btwn$0 ?f ?x ?y ?y))
            (not (in$0 ?y ?X)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (in$0 ?y ?X))
            (in$0 (ep$0 ?f ?X ?x) ?X))))

(assert (forall ((?f FldLoc) (?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?z)) (not (Btwn$0 ?f ?x ?u ?y))
            (and (Btwn$0 ?f ?x ?u ?z) (Btwn$0 ?f ?u ?y ?z)))))

(assert (forall ((?f FldLoc) (?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?z)) (not (Btwn$0 ?f ?y ?u ?z))
            (and (Btwn$0 ?f ?x ?y ?u) (Btwn$0 ?f ?x ?u ?z)))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (Btwn$0 ?f ?y ?z ?z))
            (Btwn$0 ?f ?x ?z ?z))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?z))
            (and (Btwn$0 ?f ?x ?y ?y) (Btwn$0 ?f ?y ?z ?z)))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (Btwn$0 ?f ?x ?z ?z))
            (Btwn$0 ?f ?x ?y ?z) (Btwn$0 ?f ?x ?z ?y))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (= ?x ?y)
            (Btwn$0 ?f ?x (read$1 ?f ?x) ?y))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc))
        (or (not (= (read$1 ?f ?x) ?x)) (not (Btwn$0 ?f ?x ?y ?y)) (= ?x ?y))))

(assert (forall ((?f FldLoc) (?x Loc)) (Btwn$0 ?f ?x (read$1 ?f ?x) (read$1 ?f ?x))))

(assert (forall ((?f FldLoc) (?x Loc)) (Btwn$0 ?f ?x ?x ?x)))

(check-sat)
(exit)
