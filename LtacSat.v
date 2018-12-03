Require Import Coq.ZArith.ZArith Coq.ZArith.Zcomplements. Open Scope Z_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Logic.Classical.
Require Import Coq.micromega.Lia.

Set Implicit Arguments.

Definition Znth{T: Type}(l: list T)(i: Z)(default: T): T := nth (Z.to_nat i) l default.

Parameter Error: Prop.

(* number of variables and list of clauses *)
Definition Input: Type := Z * list (list Z).

Example test1 := (5, [
  [1; -5; 4];
  [-1; 5; 3; 4];
  [-3; -4]
]).

Definition interp_lit(env: list Prop)(l: Z): Prop :=
  let x := Znth env (Z.abs l) Error in
  match l with
  | Z0 => Error
  | Zpos _ => x
  | Zneg _ => ~ x
  end.

Fixpoint interp_clause(env: list Prop)(c: list Z): Prop :=
  match c with
  | nil => False
  | [x] => interp_lit env x
  | x :: rest => interp_lit env x \/ interp_clause env rest
  end.

Fixpoint interp_formula(env: list Prop)(f: list (list Z)): Prop :=
  match f with
  | nil => True
  | [c] => interp_clause env c
  | c :: rest => interp_clause env c /\ interp_formula env rest
  end.

Eval cbv -[not] in (forall (x1 x2 x3 x4 x5: Prop),
                       interp_formula [Error; x1; x2; x3; x4; x5] (snd test1)).

Fixpoint foralls(n: nat)(acc: list Prop)(body: list Prop -> Prop): Prop :=
  match n with
  | O => body (rev acc)
  | S n' => forall (x: Prop), foralls n' (x :: acc) body
  end.

Definition claim_unsat(inp: Input): Prop :=
  let '(nvars, clauses) := inp in
  forall (x x0: Prop), (* dummy vars to make Coq's auto naming scheme match *)
    foralls (Z.to_nat nvars) [x0]
            (fun env =>
               forall e, e = env -> (* dummy equation to easily get env later *)
               True -> (* dummy hypothesis to get auto naming of hypotheses match *)
               interp_formula env clauses -> False).

Eval cbv -[not] in (claim_unsat test1).

Lemma resolution: forall x1 A B,
    x1 \/ A ->
    ~ x1 \/ B ->
    A \/ B.
Proof. tauto. Qed.

Lemma resolution1: forall C1 A1 D,
    C1 \/ A1 ->
    ~A1 \/ D ->
    C1 \/ D.
Proof. tauto. Qed.

Lemma resolution2: forall C1 A1 C2 A2 D,
    C1 \/ A1 ->
    C2 \/ A2 ->
    ~A1 \/ ~A2 \/ D ->
    C1 \/ C2 \/ D.
Proof. tauto. Qed.

Lemma resolution3: forall C1 A1 C2 A2 C3 A3 D,
    C1 \/ A1 ->
    C2 \/ A2 ->
    C3 \/ A3 ->
    ~A1 \/ ~A2 \/ ~A3 \/ D ->
    C1 \/ C2 \/ C3 \/ D.
Proof. tauto. Qed.

Lemma resolution4: forall C1 A1 C2 A2 C3 A3 C4 A4 D,
    C1 \/ A1 ->
    C2 \/ A2 ->
    C3 \/ A3 ->
    C4 \/ A4 ->
    ~A1 \/ ~A2 \/ ~A3 \/ ~A4 \/ D ->
    C1 \/ C2 \/ C3 \/ C4 \/ D.
Proof. tauto. Qed.

Lemma resolution5: forall C1 A1 C2 A2 C3 A3 C4 A4 C5 A5 D,
    C1 \/ A1 ->
    C2 \/ A2 ->
    C3 \/ A3 ->
    C4 \/ A4 ->
    C5 \/ A5 ->
    ~A1 \/ ~A2 \/ ~A3 \/ ~A4 \/ ~A5 \/ D ->
    C1 \/ C2 \/ C3 \/ C4 \/ C5 \/ D.
Proof. tauto. Qed.

Ltac indexOf firstIndex default e l :=
  match l with
  | nil => default
  | e :: _ => firstIndex
  | _ :: ?rest => indexOf (firstIndex + 1) default e rest
  end.

Ltac reify_lit env l :=
  lazymatch l with
  | ~ ?x => let r := indexOf 0 0 x env in constr:(-r)
  | ?x => indexOf 0 0 x env
  end.

Ltac reify_clause env c :=
  lazymatch c with
  | ?c1 \/ ?c2 =>
    let r1 := reify_clause env c1 in
    let r2 := reify_clause env c2 in
    constr:(r1 ++ r2)
  | ?l =>
    let r := reify_lit env l in
    constr:([r])
  end.

Fixpoint insert(lit: Z)(c: list Z): list Z :=
  match c with
  | nil => [lit]
  | h :: t => match Z.compare (Z.abs lit) (Z.abs h) with
              | Eq => if h =? lit then c (* x \/ x \/ rest *) else lit :: h :: nil (* x \/ ~x *)
              | Gt => h :: (insert lit t)
              | Lt => lit :: h :: t
              end
  end.

Lemma interp_lit_neg: forall env l,
    interp_lit env (- l) <-> ~ interp_lit env l.
Proof.
  unfold interp_lit.
  split; intros; destruct l; simpl in *; auto.
  - admit.
  - admit.
  - apply NNPP. assumption.
Admitted.

Lemma insert_sound: forall env l c,
    interp_clause env (insert l c) ->
    interp_lit env l \/ interp_clause env c.
Proof.
  induction c; intros; simpl in *; auto.
  destruct (Z.abs l ?= Z.abs a) eqn: E.
  - apply Z.compare_eq in E.
    destruct (a =? l) eqn: F.
    + apply Z.eqb_eq in F. subst a. simpl in *.
      right. exact H.
    + apply Z.eqb_neq in F. assert (a = -l) by lia. subst a.
      destruct c; rewrite interp_lit_neg;
      destruct (classic (interp_lit env l)); auto.
  - simpl in *.  exact H.
  - simpl in *.
    destruct (insert l c) eqn: F.
    + destruct c eqn: G; auto.
    + destruct c eqn: G.
      * intuition idtac. simpl in *. contradiction.
      * intuition idtac.
Qed.

Lemma insert_complete: forall env l c,
    interp_lit env l \/ interp_clause env c ->
    interp_clause env (insert l c).
Proof.
  induction c; intros; simpl in *; try solve [intuition idtac].
  destruct (Z.abs l ?= Z.abs a) eqn: E.
  - apply Z.compare_eq in E.
    destruct (a =? l) eqn: F.
    + apply Z.eqb_eq in F. subst a. simpl in *.
      destruct c; tauto.
    + apply Z.eqb_neq in F. assert (a = -l) by lia. subst a.
      destruct c.  simpl in *. (*[simpl in *; contradiction|].
      rewrite interp_lit_neg.
      destruct (classic (interp_lit env l)); auto.
  - simpl in *.  exact H.
  - simpl in *.
    destruct (insert l c) eqn: F.
    + destruct c eqn: G; auto.
    + destruct c eqn: G.
      * intuition idtac. simpl in *. contradiction.
      * intuition idtac.
Qed.
*)
Abort.

Goal claim_unsat test1.
  cbv -[not].
  intros.
  repeat match goal with
         | H: _ /\ _ |- _ => destruct H
         end.
  destruct (classic (x1 = True)).
  - subst.
    destruct (classic (x5 = True)).
    + subst.
      destruct (classic (x4 = False)).
      * subst.
        (* SAT *)
Abort.


(* TODO claim_sat *)

Goal claim_unsat test1.
  cbv -[not].
  intros.
  repeat match goal with
         | H: _ /\ _ |- _ => destruct H
         end.
  pose proof (resolution H1 H2). (* contains x5 and ~x5, so it's useless *) clear H4.
  assert (H1': x4 \/ x1 \/ ~ x5) by tauto. clear H1.
  assert (H3': ~x4 \/ ~x3) by tauto. clear H3.
  pose proof (resolution H1' H3') as H4.

  match goal with
  | H: _ = ?l |- _ => let res := indexOf 0 0 x4 l in let res' := eval cbv in res in idtac res'
  end.

  match goal with
  | H: _ = ?env |- _ => let res := reify_lit env (~x3) in let res' := eval cbv in res in idtac res'
  end.

  match goal with
  | H: _ = ?env |- _ =>
    let T := type of H4 in
    let res := reify_clause env T in let r := eval cbv in res in idtac r
  end.
Abort.

Example test2 := (4, [
  [ 1;  2; -3];
  [-1; -2;  3];
  [ 2;  3; -4];
  [-2; -3;  4];
  [ 1;  3;  4];
  [-1; -3; -4];
  [-1;  2;  4];
  [ 1; -2; -4]
]).

(* from https://www.satcompetition.org/2013/certunsat.shtml *)

(* resolution proof *)
Goal claim_unsat test2.
  cbv -[not].
  intros.
  repeat match goal with
         | H: _ /\ _ |- _ => destruct H
         end.

  (* 9  1  2  0 1 3 5 0 *)
  assert (H9: x1 \/ x2) by (clear -H1 H3 H5; tauto).
  (* 10  1  0  9 4 5 8 0 *)
  assert (H10: x1) by (clear -H9 H4 H5 H8; tauto).
  (* 11  2  0  9 3 6 7 0 *)
  assert (H11: x2) by (clear -H9 H3 H6 H7; tauto).
  (* 12  0 10 11 2 4 6 0 *)
  assert (H12: False) by (clear -H10 H11 H2 H4 H6; tauto).

  exact H12.
Qed.

(* RUP proof: would have to delete the "clear" clauses but then tauto is too slow *)
Goal claim_unsat test2.
  cbv -[not].
  intros.
  repeat match goal with
         | H: _ /\ _ |- _ => destruct H
         end.
  (* 1 2 0 *)
  assert (H9: x1 \/ x2) by (clear -H1 H3 H5; tauto).
  (* 1 0 *)
  assert (H10: x1) by (clear -H9 H4 H5 H8; tauto).
  (* 2 0 *)
  assert (H11: x2) by (clear -H9 H3 H6 H7; tauto).
  (* 0 *)
  assert (H12: False) by (clear -H10 H11 H2 H4 H6; tauto).

  exact H12.
Qed.


(* DRUP proof: deletion & reverse unit progagation (should not need the "clear -..." but tauto is too slow otherwise) *)
Goal claim_unsat test2.
  cbv -[not].
  intros.
  repeat match goal with
         | H: _ /\ _ |- _ => destruct H
         end.
  (*    1  2  0 *)
  assert (H9: x1 \/ x2) by (clear -H1 H3 H5; tauto).
  (* d  1  2 -3 0 *)
  clear H1.
  (*    1  0 *)
  assert (H10: x1) by (clear -H9 H4 H5 H8; tauto).
  (* d  1  2  0 *)
  (* clear H9. not sure if we can really clear that one?? *)
  (* d  1  3  4 0 *)
  clear H5.
  (* d  1 -2 -4 0 *)
  clear H8.
  (*    2  0 *)
  assert (H11: x2) by (clear -H9 H3 H6 H7; tauto).
  (*    0 *)
  assert (H12: False) by (clear -H10 H11 H2 H4 H6; tauto).

  exact H12.
Qed.

(* details of how resolution works *)
Goal claim_unsat test2.
  cbv -[not].
  intros.
  repeat match goal with
         | H: _ /\ _ |- _ => destruct H
         end.

  (* 9  1  2  0 1 3 5 0 *)
  assert (H9: x1 \/ x2). {
    clear -H1 H3 H5.

    assert (H1': ~x3 \/ x1 \/ x2) by (clear -H1; tauto).
    assert (H3': x3 \/ x2 \/ ~ x4) by (clear -H3; tauto).
    pose proof (resolution H3' H1') as H_1_3'. clear H1' H3'.
    assert (H_1_3: x1 \/ x2 \/ ~x4) by (clear -H_1_3'; tauto). clear H_1_3'.

    assert (H1': ~x3 \/ x1 \/ x2) by (clear -H1; tauto).
    assert (H5': x3 \/ x1 \/ x4) by (clear -H5; tauto).
    pose proof (resolution H5' H1') as H_1_5'. clear H1' H5'.
    assert (H_1_5: x1 \/ x2 \/ x4) by (clear -H_1_5'; tauto). clear H_1_5'.

    assert (H_1_3': ~x4 \/ x1 \/ x2) by (clear -H_1_3; tauto).
    assert (H_1_5': x4 \/ x1 \/ x2) by (clear -H_1_5; tauto).
    pose proof (resolution H_1_5' H_1_3') as H_1_3_5.
    clear -H_1_3_5.
    tauto.
  }

  (* 10  1  0  9 4 5 8 0 *)
  assert (H10: x1). {
    clear -H9 H4 H5 H8.
    tauto.
  }

  (* 11  2  0  9 3 6 7 0 *)
  assert (H11: x2) by (clear -H9 H3 H6 H7; tauto).
  (* 12  0 10 11 2 4 6 0 *)
  assert (H12: False) by (clear -H10 H11 H2 H4 H6; tauto).

  exact H12.
Qed.

(*
Ltac resolvent allvars on acc cl1 cl2 :=
  match allvars with
  | nil => acc
  | on :: ?rest => resolvent rest on acc cl1 cl2
  | ?v :: ?rest =>
    lazymatch cl1 with
    | context [~v] => resolvent rest on (~v \/ acc) cl1 cl2
    | context [ v] => resolvent rest on ( v \/ acc) cl1 cl2
    | _ => lazymatch cl2 with
           | context [~v] => resolvent rest on (~v \/ acc) cl1 cl2
           | context [ v] => resolvent rest on ( v \/ acc) cl1 cl2
           | _ => resolvent rest on acc cl1 cl2
           end
    end
  end.
*)
Ltac resolvent allvars on cl1 cl2 :=
  match allvars with
  | nil => constr:(False)
  | on :: ?rest => resolvent rest on cl1 cl2
  | ?v :: ?rest =>
    let r := resolvent rest on cl1 cl2 in
    lazymatch cl1 with
    | context [~v] => constr:(~v \/ r)
    | context [ v] => constr:( v \/ r)
    | _ => lazymatch cl2 with
           | context [~v] => constr:(~v \/ r)
           | context [ v] => constr:( v \/ r)
           | _ => constr:(r)
           end
    end
  end.

Ltac do_one_resolution :=
  match goal with
      | A: context[?X1], B: context[~?X1] |- _ =>
        is_var X1;
        (*idtac "----" A B "on" X1;*)
        tryif (match type of A with
               | context[?X2] =>
                 is_var X2;
                 tryif (unify X1 X2) then fail else
                 (match type of B with
                  | context[~ X2] => idtac (* "no because" X2 *)
                  end)
               end)
        then fail
        else
          (tryif (match type of B with
                  | context[?X2] =>
                    is_var X2;
                    tryif (unify X1 X2) then fail else
                      (match type of A with
                       | context[~ X2] => idtac (* "no because" X2 *)
                       end)
                  end)
            then fail
            else (idtac "yes" A B;
                  lazymatch goal with
                  | H: _ = ?env |- _ =>
                    let P1 := type of A in
                    let P2 := type of B in
                    let res := resolvent env X1 P1 P2 in idtac res;
                    lazymatch goal with
                    | _: res |- _ => fail
                    | |- _ => assert res by (clear -A B; tauto)
                    end
                  end))
      end.


Goal claim_unsat test2.
  cbv -[not].
  intros.
  repeat match goal with
         | H: _ /\ _ |- _ => destruct H
         end.
  repeat do_one_resolution.
  assumption.
Qed.
