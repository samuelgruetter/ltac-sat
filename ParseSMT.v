Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import Coq.micromega.Lia.

(* Structure *)
Notation "'(check-sat)'" := False (only parsing).
Notation "'(assert' P ')' Q" := (P -> Q) (only parsing, at level 10).
Notation "'(declare-fun' f '()' T ')' Q" := (forall (f: T), Q)
  (only parsing, at level 10, T at level 0, Q at level 0).
(* TODO a recursive notation over nat could also support "Type -> Type -> Type -> ..." etc *)
Notation "'(declare-sort' T '0' ')' Q" := (forall (T: Type), Q)
  (only parsing, at level 10, Q at level 0, T at level 0).


(* Operations *)
Notation "'(<=' a b ')'" := (a <= b) (only parsing, a at level 0, b at level 0).
Notation "'(=' a b ')'" := (a = b) (only parsing, a at level 0, b at level 0).
Notation "'(+' a b ')'" := (a + b) (only parsing, a at level 0, b at level 0).
(* Note: if we omit the space, it becomes a Coq comment! *)
Notation "'(' '*' a b ')'" := (a * b) (only parsing, a at level 0, b at level 0).

(* Datatypes *)
Notation Int := Z (only parsing).

Goal
  (* from https://www.starexec.org/starexec/secure/details/benchmark.jsp?id=7239749 *)
  (declare-sort S1 0)
  (declare-fun f1 () S1)
  (declare-fun f2 () S1)
  (declare-fun f3 () Int)
  (assert (not (= f1 f2)))
  (assert (not (<= (+ ( * 4 f3) 1) 1)))
  (assert (<= f3 0))
  (assert (<= f3 0))
  (check-sat)
.
Proof.
  intros.
  lia.
Qed.

(* https://www.starexec.org/starexec/secure/details/benchmark.jsp?id=6920515
(amortized queues in leon) declares datatypes, and these cannot be parsed as a goal

UFLIA example from boogie from SMT competition

https://www.starexec.org/starexec/services/benchmarks/7158337/contents?limit=-1

*)
