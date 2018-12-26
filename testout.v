Require Import Coq.ZArith.ZArith.
Definition Int := Z.
Definition Bool := Prop.
Open Scope Z_scope.

Section Test.
(*set-info :smt-lib-version 2.6*)

(*set-logic UFLIA*)

(*set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/sls/sls_concat.spl:36:4-19:Possible heap access through null or dangling reference
  |*)

(*set-info :category "crafted"*)

(*set-info :status unsat*)

Variable Loc : Type.

Variable SetLoc : Type.

Variable SetInt : Type.

Variable FldBool : Type.

Variable FldLoc : Type.

Variable FldInt : Type.

Variable null_0 : Loc.

Variable read_0 : FldInt -> Loc -> Int.

Variable read_1 : FldLoc -> Loc -> Loc.

Variable ep_0 : FldLoc -> SetLoc -> Loc -> Loc.

Variable emptyset_0 : SetLoc.

Variable setenum_0 : Loc -> SetLoc.

Variable union_0 : SetLoc -> SetLoc -> SetLoc.

Variable intersection_0 : SetLoc -> SetLoc -> SetLoc.

Variable setminus_0 : SetLoc -> SetLoc -> SetLoc.

Variable Btwn_0 : FldLoc -> Loc -> Loc -> Loc -> Bool.

Variable Frame_0 : SetLoc -> SetLoc -> FldLoc -> FldLoc -> Bool.

Variable Frame_1 : SetLoc -> SetLoc -> FldInt -> FldInt -> Bool.

Variable in_0 : Loc -> SetLoc -> Bool.

Variable Alloc_0 : SetLoc.

Variable Axiom_13_0 : Bool.

Variable Axiom_14_0 : Bool.

Variable Axiom_15_0 : Bool.

Variable Axiom_16_0 : Bool.

Variable Axiom_17_0 : Bool.

Variable Axiom_18_0 : Bool.

Variable Axiom_19_0 : Bool.

Variable Axiom_20_0 : Bool.

Variable Axiom_21_0 : Bool.

Variable Axiom_22_0 : Bool.

Variable Axiom_23_0 : Bool.

Variable Axiom_24_0 : Bool.

Variable FP_0 : SetLoc.

Variable FP_1_0 : SetLoc.

Variable FP_2_0 : SetLoc.

Variable FP_Caller_0 : SetLoc.

Variable FP_Caller_1_0 : SetLoc.

Variable a_0 : Loc.

Variable a_1_0 : Loc.

Variable b_0 : Loc.

Variable curr_2_0 : Loc.

Variable curr_3_0 : Loc.

Variable data_0 : FldInt.

Variable lslseg_domain_0 : FldInt -> FldLoc -> Loc -> Loc -> Int -> SetLoc.

Variable lslseg_struct_0 : SetLoc -> FldInt -> FldLoc -> Loc -> Loc -> Int -> Bool.

Variable next_0 : FldLoc.

Variable sk__X_11_0 : SetLoc.

Variable sk__X_12_0 : SetLoc.

Variable sk__X_13_0 : SetLoc.

Variable sk__X_14_0 : SetLoc.

Variable sk__X_15_0 : SetLoc.

Variable sk__X_16_0 : SetLoc.

Variable sk__X_17_0 : SetLoc.

Variable sk__X_18_0 : SetLoc.

Variable sk__X_19_0 : SetLoc.

Variable sk__X_20_0 : SetLoc.

Variable sk__X_21_0 : SetLoc.

Variable t_0 : Loc.

Variable t_1_0 : Loc.

Variable t_2_0 : Loc.

Variable t_3_0 : Loc.

Variable t_4_0 : Loc.

Variable t_5_0 : Loc.

Variable uslseg_domain_0 : FldInt -> FldLoc -> Loc -> Loc -> Int -> SetLoc.

Variable uslseg_struct_0 : SetLoc -> FldInt -> FldLoc -> Loc -> Loc -> Int -> Bool.

Variable x_0 : Int.

Variable x_5_0 : Int.

Hypothesis A0 : (ep_0 next_0 FP_1_0 curr_3_0) = t_5_0.

Hypothesis A1 : (ep_0 next_0 FP_1_0 curr_2_0) = t_4_0.

Hypothesis A2 : (ep_0 next_0 FP_1_0 b_0) = t_3_0.

Hypothesis A3 : (ep_0 next_0 FP_1_0 a_1_0) = t_2_0.

Hypothesis A4 : (ep_0 next_0 FP_1_0 a_0) = t_1_0.

Hypothesis A5 : (ep_0 next_0 FP_1_0 null_0) = t_0.

Hypothesis A6 : forall (_f : FldLoc), (read_1 _f null_0) = null_0.

Hypothesis A7 : forall (x : Loc)(y : Loc), ((x = y) /\ (in_0 x (setenum_0 y))) \/ ((not (x = y)) /\ (not (in_0 x (setenum_0 y)))).

Hypothesis A8 : forall (X : SetLoc)(Y : SetLoc)(x : Loc), ((in_0 x X) /\ (in_0 x (setminus_0 X Y)) /\ (not (in_0 x Y))) \/ (((in_0 x Y) \/ (not (in_0 x X))) /\ (not (in_0 x (setminus_0 X Y)))).

Hypothesis A9 : forall (X : SetLoc)(Y : SetLoc)(x : Loc), ((in_0 x X) /\ (in_0 x Y) /\ (in_0 x (intersection_0 X Y))) \/ (((not (in_0 x X)) \/ (not (in_0 x Y))) /\ (not (in_0 x (intersection_0 X Y)))).

Hypothesis A10 : forall (X : SetLoc)(Y : SetLoc)(x : Loc), ((in_0 x (union_0 X Y)) /\ ((in_0 x X) \/ (in_0 x Y))) \/ ((not (in_0 x X)) /\ (not (in_0 x Y)) /\ (not (in_0 x (union_0 X Y)))).

Hypothesis A11 : forall (x : Loc), not (in_0 x emptyset_0).

Hypothesis A12 : ((Btwn_0 next_0 a_0 null_0 null_0) /\ Axiom_14_0 /\ Axiom_13_0) \/ (not (lslseg_struct_0 sk__X_21_0 data_0 next_0 a_0 null_0 x_0)).

Hypothesis A13 : (not Axiom_15_0) \/ (forall (l1 : Loc)(l2 : Loc), ((read_0 data_0 l1) <= (read_0 data_0 l2)) \/ (not (Btwn_0 next_0 l1 l2 curr_2_0)) \/ (not (in_0 l1 sk__X_18_0)) \/ (not (in_0 l2 sk__X_18_0))).

Hypothesis A14 : (not Axiom_16_0) \/ (forall (l1 : Loc), ((read_0 data_0 l1) <= (read_0 data_0 curr_2_0)) \/ (not (in_0 l1 sk__X_18_0))).

Hypothesis A15 : ((Btwn_0 next_0 a_1_0 curr_3_0 curr_3_0) /\ Axiom_18_0 /\ Axiom_17_0) \/ (not (lslseg_struct_0 sk__X_11_0 data_0 next_0 a_1_0 curr_3_0 (read_0 data_0 curr_3_0))).

Hypothesis A16 : (not Axiom_19_0) \/ (forall (l1 : Loc)(l2 : Loc), ((read_0 data_0 l1) <= (read_0 data_0 l2)) \/ (not (Btwn_0 next_0 l1 l2 null_0)) \/ (not (in_0 l1 sk__X_20_0)) \/ (not (in_0 l2 sk__X_20_0))).

Hypothesis A17 : (not Axiom_20_0) \/ (forall (l1 : Loc), (x_0 <= (read_0 data_0 l1)) \/ (not (in_0 l1 sk__X_20_0))).

Hypothesis A18 : ((Btwn_0 next_0 curr_2_0 null_0 null_0) /\ Axiom_22_0 /\ Axiom_21_0) \/ (not (lslseg_struct_0 sk__X_16_0 data_0 next_0 curr_2_0 null_0 x_0)).

Hypothesis A19 : (not Axiom_23_0) \/ (forall (l1 : Loc)(l2 : Loc), ((read_0 data_0 l1) <= (read_0 data_0 l2)) \/ (not (Btwn_0 next_0 l1 l2 null_0)) \/ (not (in_0 l1 sk__X_13_0)) \/ (not (in_0 l2 sk__X_13_0))).

Hypothesis A20 : (not Axiom_24_0) \/ (forall (l1 : Loc), ((read_0 data_0 l1) <= x_5_0) \/ (not (in_0 l1 sk__X_13_0))).

Hypothesis A21 : (read_1 next_0 curr_3_0) = null_0.

Hypothesis A22 : FP_Caller_1_0 = (setminus_0 FP_Caller_0 FP_0).

Hypothesis A23 : curr_2_0 = a_0.

Hypothesis A24 : Frame_1 FP_1_0 Alloc_0 data_0 data_0.

Hypothesis A25 : Alloc_0 = (union_0 FP_2_0 Alloc_0).

Hypothesis A26 : emptyset_0 = emptyset_0.

Hypothesis A27 : sk__X_11_0 = (lslseg_domain_0 data_0 next_0 a_1_0 curr_3_0 (read_0 data_0 curr_3_0)).

Hypothesis A28 : sk__X_13_0 = (lslseg_domain_0 data_0 next_0 curr_3_0 null_0 x_5_0).

Hypothesis A29 : sk__X_14_0 = (union_0 sk__X_12_0 sk__X_13_0).

Hypothesis A30 : lslseg_struct_0 sk__X_13_0 data_0 next_0 curr_3_0 null_0 x_5_0.

Hypothesis A31 : emptyset_0 = emptyset_0.

Hypothesis A32 : sk__X_15_0 = (union_0 sk__X_17_0 sk__X_16_0).

Hypothesis A33 : sk__X_16_0 = (lslseg_domain_0 data_0 next_0 curr_2_0 null_0 x_0).

Hypothesis A34 : sk__X_18_0 = (lslseg_domain_0 data_0 next_0 a_0 curr_2_0 (read_0 data_0 curr_2_0)).

Hypothesis A35 : lslseg_struct_0 sk__X_16_0 data_0 next_0 curr_2_0 null_0 x_0.

Hypothesis A36 : not (curr_2_0 = null_0).

Hypothesis A37 : sk__X_19_0 = (union_0 sk__X_21_0 sk__X_20_0).

Hypothesis A38 : sk__X_20_0 = (uslseg_domain_0 data_0 next_0 b_0 null_0 x_0).

Hypothesis A39 : FP_Caller_0 = (union_0 FP_0 FP_Caller_0).

Hypothesis A40 : uslseg_struct_0 sk__X_20_0 data_0 next_0 b_0 null_0 x_0.

Hypothesis A41 : not (in_0 null_0 Alloc_0).

Hypothesis A42 : not (in_0 curr_3_0 FP_2_0).

Hypothesis A43 : forall (l1 : Loc), ((Btwn_0 next_0 a_0 l1 curr_2_0) /\ (in_0 l1 (lslseg_domain_0 data_0 next_0 a_0 curr_2_0 (read_0 data_0 curr_2_0))) /\ (not (l1 = curr_2_0))) \/ (((l1 = curr_2_0) \/ (not (Btwn_0 next_0 a_0 l1 curr_2_0))) /\ (not (in_0 l1 (lslseg_domain_0 data_0 next_0 a_0 curr_2_0 (read_0 data_0 curr_2_0))))).

Hypothesis A44 : forall (l1 : Loc), ((Btwn_0 next_0 b_0 l1 null_0) /\ (in_0 l1 (uslseg_domain_0 data_0 next_0 b_0 null_0 x_0)) /\ (not (l1 = null_0))) \/ (((l1 = null_0) \/ (not (Btwn_0 next_0 b_0 l1 null_0))) /\ (not (in_0 l1 (uslseg_domain_0 data_0 next_0 b_0 null_0 x_0)))).

Hypothesis A45 : forall (l1 : Loc), ((Btwn_0 next_0 curr_3_0 l1 null_0) /\ (in_0 l1 (lslseg_domain_0 data_0 next_0 curr_3_0 null_0 x_5_0)) /\ (not (l1 = null_0))) \/ (((l1 = null_0) \/ (not (Btwn_0 next_0 curr_3_0 l1 null_0))) /\ (not (in_0 l1 (lslseg_domain_0 data_0 next_0 curr_3_0 null_0 x_5_0)))).

Hypothesis A46 : forall (_X : SetLoc)(_f : FldLoc)(_x : Loc), (in_0 (ep_0 _f _X _x) _X) \/ (_x = (ep_0 _f _X _x)).

Hypothesis A47 : forall (_X : SetLoc)(_f : FldLoc)(_x : Loc), Btwn_0 _f _x (ep_0 _f _X _x) (ep_0 _f _X _x).

Hypothesis A48 : (not Axiom_13_0) \/ (forall (l1 : Loc)(l2 : Loc), ((read_0 data_0 l1) <= (read_0 data_0 l2)) \/ (not (Btwn_0 next_0 l1 l2 null_0)) \/ (not (in_0 l1 sk__X_21_0)) \/ (not (in_0 l2 sk__X_21_0))).

Hypothesis A49 : (not Axiom_14_0) \/ (forall (l1 : Loc), ((read_0 data_0 l1) <= x_0) \/ (not (in_0 l1 sk__X_21_0))).

Hypothesis A50 : ((Btwn_0 next_0 a_0 curr_2_0 curr_2_0) /\ Axiom_16_0 /\ Axiom_15_0) \/ (not (lslseg_struct_0 sk__X_18_0 data_0 next_0 a_0 curr_2_0 (read_0 data_0 curr_2_0))).

Hypothesis A51 : (not Axiom_17_0) \/ (forall (l1 : Loc)(l2 : Loc), ((read_0 data_0 l1) <= (read_0 data_0 l2)) \/ (not (Btwn_0 next_0 l1 l2 curr_3_0)) \/ (not (in_0 l1 sk__X_11_0)) \/ (not (in_0 l2 sk__X_11_0))).

Hypothesis A52 : (not Axiom_18_0) \/ (forall (l1 : Loc), ((read_0 data_0 l1) <= (read_0 data_0 curr_3_0)) \/ (not (in_0 l1 sk__X_11_0))).

Hypothesis A53 : ((Btwn_0 next_0 b_0 null_0 null_0) /\ Axiom_20_0 /\ Axiom_19_0) \/ (not (uslseg_struct_0 sk__X_20_0 data_0 next_0 b_0 null_0 x_0)).

Hypothesis A54 : (not Axiom_21_0) \/ (forall (l1 : Loc)(l2 : Loc), ((read_0 data_0 l1) <= (read_0 data_0 l2)) \/ (not (Btwn_0 next_0 l1 l2 null_0)) \/ (not (in_0 l1 sk__X_16_0)) \/ (not (in_0 l2 sk__X_16_0))).

Hypothesis A55 : (not Axiom_22_0) \/ (forall (l1 : Loc), ((read_0 data_0 l1) <= x_0) \/ (not (in_0 l1 sk__X_16_0))).

Hypothesis A56 : ((Btwn_0 next_0 curr_3_0 null_0 null_0) /\ Axiom_24_0 /\ Axiom_23_0) \/ (not (lslseg_struct_0 sk__X_13_0 data_0 next_0 curr_3_0 null_0 x_5_0)).

Hypothesis A57 : FP_2_0 = (union_0 (setminus_0 FP_0 FP_1_0) (union_0 (intersection_0 Alloc_0 FP_1_0) (setminus_0 Alloc_0 Alloc_0))).

Hypothesis A58 : a_1_0 = a_0.

Hypothesis A59 : x_5_0 = x_0.

Hypothesis A60 : Frame_0 FP_1_0 Alloc_0 next_0 next_0.

Hypothesis A61 : Alloc_0 = (union_0 FP_Caller_0 Alloc_0).

Hypothesis A62 : emptyset_0 = (intersection_0 sk__X_12_0 sk__X_13_0).

Hypothesis A63 : sk__X_12_0 = sk__X_11_0.

Hypothesis A64 : sk__X_14_0 = (union_0 (intersection_0 Alloc_0 FP_1_0) (setminus_0 Alloc_0 Alloc_0)).

Hypothesis A65 : lslseg_struct_0 sk__X_11_0 data_0 next_0 a_1_0 curr_3_0 (read_0 data_0 curr_3_0).

Hypothesis A66 : not (curr_3_0 = null_0).

Hypothesis A67 : emptyset_0 = (intersection_0 sk__X_17_0 sk__X_16_0).

Hypothesis A68 : sk__X_15_0 = FP_1_0.

Hypothesis A69 : sk__X_17_0 = sk__X_18_0.

Hypothesis A70 : FP_0 = (union_0 FP_1_0 FP_0).

Hypothesis A71 : lslseg_struct_0 sk__X_18_0 data_0 next_0 a_0 curr_2_0 (read_0 data_0 curr_2_0).

Hypothesis A72 : emptyset_0 = (intersection_0 sk__X_21_0 sk__X_20_0).

Hypothesis A73 : sk__X_19_0 = FP_0.

Hypothesis A74 : sk__X_21_0 = (lslseg_domain_0 data_0 next_0 a_0 null_0 x_0).

Hypothesis A75 : lslseg_struct_0 sk__X_21_0 data_0 next_0 a_0 null_0 x_0.

Hypothesis A76 : not (a_0 = null_0).

Hypothesis A77 : not (in_0 null_0 Alloc_0).

Hypothesis A78 : forall (l1 : Loc), ((Btwn_0 next_0 a_0 l1 null_0) /\ (in_0 l1 (lslseg_domain_0 data_0 next_0 a_0 null_0 x_0)) /\ (not (l1 = null_0))) \/ (((l1 = null_0) \/ (not (Btwn_0 next_0 a_0 l1 null_0))) /\ (not (in_0 l1 (lslseg_domain_0 data_0 next_0 a_0 null_0 x_0)))).

Hypothesis A79 : forall (l1 : Loc), ((Btwn_0 next_0 a_1_0 l1 curr_3_0) /\ (in_0 l1 (lslseg_domain_0 data_0 next_0 a_1_0 curr_3_0 (read_0 data_0 curr_3_0))) /\ (not (l1 = curr_3_0))) \/ (((l1 = curr_3_0) \/ (not (Btwn_0 next_0 a_1_0 l1 curr_3_0))) /\ (not (in_0 l1 (lslseg_domain_0 data_0 next_0 a_1_0 curr_3_0 (read_0 data_0 curr_3_0))))).

Hypothesis A80 : forall (l1 : Loc), ((Btwn_0 next_0 curr_2_0 l1 null_0) /\ (in_0 l1 (lslseg_domain_0 data_0 next_0 curr_2_0 null_0 x_0)) /\ (not (l1 = null_0))) \/ (((l1 = null_0) \/ (not (Btwn_0 next_0 curr_2_0 l1 null_0))) /\ (not (in_0 l1 (lslseg_domain_0 data_0 next_0 curr_2_0 null_0 x_0)))).

Hypothesis A81 : forall (_X : SetLoc)(_f : FldLoc)(_x : Loc)(_y : Loc), (Btwn_0 _f _x (ep_0 _f _X _x) _y) \/ (not (Btwn_0 _f _x _y _y)) \/ (not (in_0 _y _X)).

Hypothesis A82 : forall (_X : SetLoc)(_f : FldLoc)(_x : Loc)(_y : Loc), (not (Btwn_0 _f _x _y _y)) \/ (not (in_0 _y _X)) \/ (in_0 (ep_0 _f _X _x) _X).

Hypothesis A83 : forall (_f : FldLoc)(_u : Loc)(_x : Loc)(_y : Loc)(_z : Loc), (not (Btwn_0 _f _x _y _z)) \/ (not (Btwn_0 _f _x _u _y)) \/ ((Btwn_0 _f _x _u _z) /\ (Btwn_0 _f _u _y _z)).

Hypothesis A84 : forall (_f : FldLoc)(_u : Loc)(_x : Loc)(_y : Loc)(_z : Loc), (not (Btwn_0 _f _x _y _z)) \/ (not (Btwn_0 _f _y _u _z)) \/ ((Btwn_0 _f _x _y _u) /\ (Btwn_0 _f _x _u _z)).

Hypothesis A85 : forall (_f : FldLoc)(_x : Loc)(_y : Loc)(_z : Loc), (not (Btwn_0 _f _x _y _y)) \/ (not (Btwn_0 _f _y _z _z)) \/ (Btwn_0 _f _x _z _z).

Hypothesis A86 : forall (_f : FldLoc)(_x : Loc)(_y : Loc)(_z : Loc), (not (Btwn_0 _f _x _y _z)) \/ ((Btwn_0 _f _x _y _y) /\ (Btwn_0 _f _y _z _z)).

Hypothesis A87 : forall (_f : FldLoc)(_x : Loc)(_y : Loc)(_z : Loc), (not (Btwn_0 _f _x _y _y)) \/ (not (Btwn_0 _f _x _z _z)) \/ (Btwn_0 _f _x _y _z) \/ (Btwn_0 _f _x _z _y).

Hypothesis A88 : forall (_f : FldLoc)(_x : Loc)(_y : Loc), (not (Btwn_0 _f _x _y _x)) \/ (_x = _y).

Hypothesis A89 : forall (_f : FldLoc)(_x : Loc)(_y : Loc), (not (Btwn_0 _f _x _y _y)) \/ (_x = _y) \/ (Btwn_0 _f _x (read_1 _f _x) _y).

Hypothesis A90 : forall (_f : FldLoc)(_x : Loc)(_y : Loc), (not ((read_1 _f _x) = _x)) \/ (not (Btwn_0 _f _x _y _y)) \/ (_x = _y).

Hypothesis A91 : forall (_f : FldLoc)(_x : Loc), Btwn_0 _f _x (read_1 _f _x) (read_1 _f _x).

Hypothesis A92 : forall (_f : FldLoc)(_x : Loc), Btwn_0 _f _x _x _x.

Theorem unsat: False.
Proof.

Abort.


End Test.
