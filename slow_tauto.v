Definition mygoal :=
  forall x1 x2 x3 x4 : Prop,
    x1 \/ x2 \/ ~ x3 ->
    ~ x1 \/ ~ x2 \/ x3 ->
    x2 \/ x3 \/ ~ x4 ->
    ~ x2 \/ ~ x3 \/ x4 ->
    x1 \/ x3 \/ x4 ->
    ~ x1 \/ ~ x3 \/ ~ x4 ->
    ~ x1 \/ x2 \/ x4 ->
    x1 \/ ~ x2 \/ ~ x4 ->
    False.

Goal mygoal.
Proof.
  unfold mygoal.
  intros *. intros H1 H2 H3 H4 H5 H6 H7 H8.
  assert (H9: x1 \/ x2) by (clear -H1 H3 H5; tauto).
  assert (H10: x1) by (clear -H9 H4 H5 H8; tauto).
  assert (H11: x2) by (clear -H9 H3 H6 H7; tauto).
  assert (H12: False) by (clear -H10 H11 H2 H4 H6; tauto).
  exact H12.
Qed.

Require Import Btauto.
Open Scope bool_scope.

Definition mygoal' :=
  forall x1 x2 x3 x4 : bool,
    (x1 || x2 || negb x3) &&
    (negb x1 || negb x2 || x3) &&
    (x2 || x3 || negb x4) &&
    (negb x2 || negb x3 || x4) &&
    (x1 || x3 || x4) &&
    (negb x1 || negb x3 || negb x4) &&
    (negb x1 || x2 || x4) &&
    (x1 || negb x2 || negb x4)
    = false.

Goal mygoal'.
Proof.
  unfold mygoal'.
  intros *.
  Time btauto. (* Finished transaction in 0.012 secs (0.011u,0.s) (successful) *)
Qed.

Goal mygoal.
Proof.
  unfold mygoal.
  intros *. intros H1 H2 H3 H4 H5 H6 H7 H8.
  Time tauto. (* Finished transaction in 40.578 secs (40.323u,0.052s) (successful) *)
Qed.
