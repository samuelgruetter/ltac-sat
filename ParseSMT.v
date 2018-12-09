Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.micromega.Lia.

Definition allDistinct{A: Type}(l: list A): Prop :=
  forall i j e1 e2, nth_error l i = Some e1 -> nth_error l j = Some e2 -> e1 = e2 -> i = j.

(* Structure *)

Notation "'(check-sat)'" := False (only parsing).
Notation "'(assert' P ')' Q" := (P -> Q) (only parsing, at level 10).

Notation "'(declare-fun' f '()' T ')' Q" := (forall (f: T), Q)
  (only parsing, at level 10, f at level 0, T at level 200, Q at level 0).
Notation "'(declare-fun' f '(' A1 ')' T ')' Q" := (forall (f: A1 -> T), Q)
  (only parsing, at level 10, f at level 0, T at level 0, Q at level 0, A1 at level 0).
Notation "'(declare-fun' f '(' A1 A2 ')' T ')' Q" := (forall (f: A1 -> A2 -> T), Q)
  (only parsing, at level 10, f at level 0, T at level 0, Q at level 0,
   A1 at level 0, A2 at level 0).
Notation "'(declare-fun' f '(' A1 A2 A3 ')' T ')' Q" := (forall (f: A1 -> A2 -> A3 -> T), Q)
  (only parsing, at level 10, f at level 0, T at level 0, Q at level 0,
   A1 at level 0, A2 at level 0, A3 at level 0).
Notation "'(declare-fun' f '(' A1 A2 A3 A4 ')' T ')' Q" :=
  (forall (f: A1 -> A2 -> A3 -> A4 -> T), Q)
  (only parsing, at level 10, f at level 0, T at level 0, Q at level 0,
   A1 at level 0, A2 at level 0, A3 at level 0, A4 at level 0).

(* TODO a recursive notation over nat could also support "Type -> Type -> Type -> ..." etc *)
Notation "'(declare-sort' T '0' ')' Q" := (forall (T: Type), Q)
  (only parsing, at level 10, Q at level 0, T at level 0).

Notation "'(forall' '(' '(' x1 T1 ')' ')' P ')'" :=
  ( forall (x1: T1), P)
  (only parsing, at level 0, x1 at level 0, T1 at level 0,
   P at level 0).

Notation "'(forall' '(' '(' x1 T1 ')' '(' x2 T2 ')' ')' P ')'" :=
  ( forall (x1: T1) (x2: T2), P)
  (only parsing, at level 0, x1 at level 0, T1 at level 0, x2 at level 0, T2 at level 0,
   P at level 0).
Notation "'(forall' '(' '(' x1 T1 ')' '(' x2 T2 ')' '(' x3 T3 ')' ')' P ')'" :=
  ( forall (x1: T1) (x2: T2) (x3: T3), P)
    (only parsing, at level 0,
     x1 at level 0, T1 at level 0,
     x2 at level 0, T2 at level 0,
     x3 at level 0, T3 at level 0,
   P at level 0).
Notation "'(forall' '(' '(' x1 T1 ')' '(' x2 T2 ')' '(' x3 T3 ')' '(' x4 T4 ')' ')' P ')'" :=
  ( forall (x1: T1) (x2: T2) (x3: T3) (x4: T4), P)
    (only parsing, at level 0,
     x1 at level 0, T1 at level 0,
     x2 at level 0, T2 at level 0,
     x3 at level 0, T3 at level 0,
     x4 at level 0, T4 at level 0,
   P at level 0).
Notation "'(forall' '(' '(' x1 T1 ')' '(' x2 T2 ')' '(' x3 T3 ')' '(' x4 T4 ')' '(' x5 T5 ')' ')' P ')'" :=
  ( forall (x1: T1) (x2: T2) (x3: T3) (x4: T4) (x5: T5), P)
    (only parsing, at level 0,
     x1 at level 0, T1 at level 0,
     x2 at level 0, T2 at level 0,
     x3 at level 0, T3 at level 0,
     x4 at level 0, T4 at level 0,
     x5 at level 0, T5 at level 0,
   P at level 0).
Notation "'(forall' '(' '(' x1 T1 ')' '(' x2 T2 ')' '(' x3 T3 ')' '(' x4 T4 ')' '(' x5 T5 ')' '(' x6 T6 ')' ')' P ')'" :=
  ( forall (x1: T1) (x2: T2) (x3: T3) (x4: T4) (x5: T5) (x6: T6), P)
    (only parsing, at level 0,
     x1 at level 0, T1 at level 0,
     x2 at level 0, T2 at level 0,
     x3 at level 0, T3 at level 0,
     x4 at level 0, T4 at level 0,
     x5 at level 0, T5 at level 0,
     x6 at level 0, T6 at level 0,
   P at level 0).

Notation "'(let' '(' '(' v1 t1 ')' ')' u ')'" :=
  (let v1 := t1 in u)
    (only parsing, at level 0,
     v1 at level 0, t1 at level 0,
     u at level 0).
Notation "'(let' '(' '(' v1 t1 ')' '(' v2 t2 ')' ')' u ')'" :=
  ( let v1 := t1 in let v2 := t2 in u)
    (only parsing, at level 0,
     v1 at level 0, t1 at level 0,
     v2 at level 0, t2 at level 0,
     u at level 0).
Notation "'(let' '(' '(' v1 t1 ')' '(' v2 t2 ')' '(' v3 t3 ')' ')' u ')'" :=
  ( let v1 := t1 in let v2 := t2 in let v3 := t3 in u)
    (only parsing, at level 0,
     v1 at level 0, t1 at level 0,
     v2 at level 0, t2 at level 0,
     v3 at level 0, t3 at level 0,
     u at level 0).
Notation "'(let' '(' '(' v1 t1 ')' '(' v2 t2 ')' '(' v3 t3 ')' '(' v4 t4 ')' ')' u ')'" :=
  ( let v1 := t1 in let v2 := t2 in let v3 := t3 in let v4 := t4 in u)
    (only parsing, at level 0,
     v1 at level 0, t1 at level 0,
     v2 at level 0, t2 at level 0,
     v3 at level 0, t3 at level 0,
     v4 at level 0, t4 at level 0,
     u at level 0).
Notation "'(let' '(' '(' v1 t1 ')' '(' v2 t2 ')' '(' v3 t3 ')' '(' v4 t4 ')' '(' v5 t5 ')' ')' u ')'" :=
  ( let v1 := t1 in let v2 := t2 in let v3 := t3 in let v4 := t4 in let v5 := t5 in u)
    (only parsing, at level 0,
     v1 at level 0, t1 at level 0,
     v2 at level 0, t2 at level 0,
     v3 at level 0, t3 at level 0,
     v4 at level 0, t4 at level 0,
     v5 at level 0, t5 at level 0,
     u at level 0).


(* ignores the pattern *)
Definition with_pattern{P T: Type}(pat: P)(t: T): T := t.

Notation "P ':pattern' '(' x y .. z ')'" :=
  (with_pattern x (with_pattern y .. (with_pattern z P) .. ))
  (only parsing, at level 10, x at level 0).
Notation "P ':pattern' '(' x ')'" :=
  (with_pattern x P)
  (only parsing, at level 10, x at level 0).
Notation "'(!' P ')'" := P (only parsing, at level 0, P at level 10).

(* Operations *)
Notation "'(<=' a b ')'" := (a <= b) (only parsing, a at level 0, b at level 0).
Notation "'(<' a b ')'" := (a < b) (only parsing, a at level 0, b at level 0).
Notation "'(>=' a b ')'" := (a >= b) (only parsing, a at level 0, b at level 0).
Notation "'(>' a b ')'" := (a > b) (only parsing, a at level 0, b at level 0).
Notation "'(=' a b ')'" := (a = b) (only parsing, a at level 0, b at level 0).
Notation "'(+' a b ')'" := (a + b) (only parsing, a at level 0, b at level 0).
Notation "'(-' a b ')'" := (a - b) (only parsing, a at level 0, b at level 0).
(* Note: if we omit the space, it becomes a Coq comment! *)
Notation "'(' '*' a b ')'" := (a * b) (only parsing, a at level 0, b at level 0).

(* Logic operators *)
Notation "'(=>' a b ')'" := (a -> b) (only parsing, a at level 0, b at level 0).
Notation "'(and' a b ')'" := (a /\ b) (only parsing, a at level 0, b at level 0).
Notation "'(and' a b c ')'" := (a /\ b /\ c) (only parsing, a at level 0, b at level 0, c at level 0).
Notation "'(and' a b c d ')'" := (a /\ b /\ c /\ d) (only parsing, a at level 0, b at level 0, c at level 0, d at level 0).
Notation "'(and' a b c d e ')'" := (a /\ b /\ c /\ d /\ e) (only parsing, a at level 0, b at level 0, c at level 0, d at level 0, e at level 0).
Notation "'(and' a b c d e f ')'" := (a /\ b /\ c /\ d /\ e /\ f) (only parsing, a at level 0, b at level 0, c at level 0, d at level 0, e at level 0, f at level 0).
Notation "'(or' a b ')'" := (a \/ b) (only parsing, a at level 0, b at level 0).
Notation "'(or' a b c ')'" := (a \/ b \/ c) (only parsing, a at level 0, b at level 0, c at level 0).
Notation "'(or' a b c d ')'" := (a \/ b \/ c \/ d) (only parsing, a at level 0, b at level 0, c at level 0, d at level 0).
Notation "'(or' a b c d e ')'" := (a \/ b \/ c \/ d \/ e) (only parsing, a at level 0, b at level 0, c at level 0, d at level 0, e at level 0).
Notation "'(or' a b c d e f ')'" := (a \/ b \/ c \/ d \/ e \/ f) (only parsing, a at level 0, b at level 0, c at level 0, d at level 0, e at level 0, f at level 0).
Notation "'(not' a ')'" := (~ a) (only parsing, a at level 0).

(* Misc logic hack
Notation "'(=' a 'true)'" := (a: Prop) (only parsing, a at level 0).
Notation "'(=>' 'true' 'true)'" := True (only parsing, at level 0).
*)

(* Datatypes *)
Notation Int := Z (only parsing).
Notation Bool := Prop (only parsing).
Notation true := True (only parsing).
Notation false := False (only parsing).
(* TODO sometimes "bool" might be more appropriate *)

(* Misc *)
Notation "'(distinct' x y .. z ')'" := (allDistinct (cons x (cons y .. (cons z nil) ..)))
  (only parsing, at level 10, x at level 0, y at level 0, z at level 0).
(*
coq/theories/Lists/List.v:
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : list_scope.
*)

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

Lemma True_implies: forall (P: Prop), (True -> P) <-> P.
Proof. tauto. Qed.

Lemma implies_True: forall (P: Prop), (P -> True) <-> True.
Proof. tauto. Qed.

Lemma and_True: forall (P: Prop), (P /\ True) <-> P.
Proof. tauto. Qed.

Lemma equals_True: forall (P: Prop), (P = True) <-> P.
Proof.
  intros. split; intros.
  - subst. constructor.
  - apply propositional_extensionality. tauto.
Qed.

Goal
(*
UFLIA example from boogie from SMT competition
https://www.starexec.org/starexec/services/benchmarks/7158337/contents?limit=-1
preprocessed with preprocess.sh
*)
(declare-fun boolIff (Int Int) Int)
(declare-fun PeerGroupPlaceholder_ () Int)
(declare-fun intGreater (Int Int) Int)
(declare-fun IfThenElse_ (Int Int Int) Int)
(declare-fun CONCVARSYM (Int) Int)
(declare-fun SharingMode_Unshared_ () Int)
(declare-fun System_dot_Reflection_dot_IReflect () Int)
(declare-fun int_m2147483648 () Int)
(declare-fun System_dot_Int32 () Int)
(declare-fun intAtMost (Int Int) Int)
(declare-fun multiply (Int Int) Int)
(declare-fun Is_ (Int Int) Int)
(declare-fun Smt_dot_true () Int)
(declare-fun Bag () Int)
(declare-fun ElementType_ (Int) Int)
(declare-fun divide (Int Int) Int)
(declare-fun int_m9223372036854775808 () Int)
(declare-fun divides (Int Int) Int)
(declare-fun select1 (Int Int) Int)
(declare-fun store1 (Int Int Int) Int)
(declare-fun select2 (Int Int Int) Int)
(declare-fun nullObject () Int)
(declare-fun store2 (Int Int Int Int) Int)
(declare-fun modulo (Int Int) Int)
(declare-fun ownerRef_ () Int)
(declare-fun StructSet_ (Int Int Int) Int)
(declare-fun AsDirectSubClass (Int Int) Int)
(declare-fun System_dot_Collections_dot_ICollection () Int)
(declare-fun System_dot_Boolean () Int)
(declare-fun shl_ (Int Int) Int)
(declare-fun DimLength_ (Int Int) Int)
(declare-fun anyEqual (Int Int) Int)
(declare-fun System_dot_Array () Int)
(declare-fun System_dot_Reflection_dot_ICustomAttributeProvider () Int)
(declare-fun SharingMode_LockProtected_ () Int)
(declare-fun IsMemberlessType_ (Int) Int)
(declare-fun System_dot_UInt16 () Int)
(declare-fun ClassRepr (Int) Int)
(declare-fun System_dot_Runtime_dot_InteropServices_dot__Type () Int)
(declare-fun boolNot (Int) Int)
(declare-fun Microsoft_dot_Contracts_dot_ICheckedException () Int)
(declare-fun System_dot_Exception () Int)
(declare-fun System_dot_Runtime_dot_InteropServices_dot__MemberInfo () Int)
(declare-fun block6086_correct () Int)
(declare-fun boolAnd (Int Int) Int)
(declare-fun boolImplies (Int Int) Int)
(declare-fun Unbox (Int) Int)
(declare-fun intAtLeast (Int Int) Int)
(declare-fun ownerFrame_ () Int)
(declare-fun int_4294967295 () Int)
(declare-fun IsAllocated (Int Int) Int)
(declare-fun TypeName (Int) Int)
(declare-fun AsPeerField (Int) Int)
(declare-fun int_9223372036854775807 () Int)
(declare-fun AsRepField (Int Int) Int)
(declare-fun System_dot_Reflection_dot_MemberInfo () Int)
(declare-fun ArrayCategoryValue_ () Int)
(declare-fun is (Int Int) Int)
(declare-fun Microsoft_dot_Contracts_dot_GuardException () Int)
(declare-fun InRange (Int Int) Bool)
(declare-fun AsOwner (Int Int) Int)
(declare-fun System_dot_Int64 () Int)
(declare-fun System_dot_Runtime_dot_InteropServices_dot__Exception () Int)
(declare-fun _or_ (Int Int) Int)
(declare-fun As_ (Int Int) Int)
(declare-fun exposeVersion_ () Int)
(declare-fun System_dot_Type () Int)
(declare-fun intLess (Int Int) Int)
(declare-fun AsImmutable_ (Int) Int)
(declare-fun NonNullFieldsAreInitialized_ () Int)
(declare-fun LBound_ (Int Int) Int)
(declare-fun System_dot_Object () Int)
(declare-fun Bag_dot_a () Int)
(declare-fun System_dot_UInt32 () Int)
(declare-fun localinv_ () Int)
(declare-fun inv_ () Int)
(declare-fun Bag_dot_n () Int)
(declare-fun entry_correct () Int)
(declare-fun FirstConsistentOwner_ () Int)
(declare-fun UnboxedType (Int) Int)
(declare-fun AsRefField (Int Int) Int)
(declare-fun System_dot_Byte () Int)
(declare-fun int_2147483647 () Int)
(declare-fun ArrayCategoryRef_ () Int)
(declare-fun Heap_ () Int)
(declare-fun Length_ (Int) Int)
(declare-fun System_dot_Runtime_dot_Serialization_dot_ISerializable () Int)
(declare-fun AsNonNullRefField (Int Int) Int)
(declare-fun IsHeap (Int) Int)
(declare-fun UBound_ (Int Int) Int)
(declare-fun System_dot_String () Int)
(declare-fun System_dot_Collections_dot_IList () Int)
(declare-fun System_dot_String_dot_IsInterned_System_dot_String_notnull_ (Int) Int)
(declare-fun Rank_ (Int) Int)
(declare-fun UnknownRef_ () Int)
(declare-fun RefArraySet (Int Int Int) Int)
(declare-fun ValueArraySet (Int Int Int) Int)
(declare-fun boolOr (Int Int) Int)
(declare-fun sharingMode_ () Int)
(declare-fun subtypes (Int Int) Bool)
(declare-fun System_dot_String_dot_Equals_System_dot_String_System_dot_String_ (Int Int) Int)
(declare-fun anyNeq (Int Int) Int)
(declare-fun IsStaticField (Int) Int)
(declare-fun IsNotNull_ (Int Int) Int)
(declare-fun typeof_ (Int) Int)
(declare-fun ArrayCategoryNonNullRef_ () Int)
(declare-fun RefArrayGet (Int Int) Int)
(declare-fun ValueArrayGet (Int Int) Int)
(declare-fun TypeObject (Int) Int)
(declare-fun _and_ (Int Int) Int)
(declare-fun BoxTester (Int Int) Int)
(declare-fun Microsoft_dot_Contracts_dot_ObjectInvariantException () Int)
(declare-fun IsValueType_ (Int) Int)
(declare-fun AsRangeField (Int Int) Int)
(declare-fun System_dot_SByte () Int)
(declare-fun BeingConstructed_ () Int)
(declare-fun FieldDependsOnFCO_ (Int Int Int) Int)
(declare-fun NonNullRefArray (Int Int) Int)
(declare-fun RefArray (Int Int) Int)
(declare-fun ArrayCategory_ (Int) Int)
(declare-fun AsPureObject_ (Int) Int)
(declare-fun System_dot_String_dot_Equals_System_dot_String_ (Int Int) Int)
(declare-fun System_dot_Int16 () Int)
(declare-fun AsMutable_ (Int) Int)
(declare-fun System_dot_Char () Int)
(declare-fun block6069_correct () Int)
(declare-fun System_dot_UInt64 () Int)
(declare-fun StructGet_ (Int Int) Int)
(declare-fun OneClassDown (Int Int) Int)
(declare-fun ArrayIndex (Int Int Int Int) Int)
(declare-fun Box (Int Int) Int)
(declare-fun int_18446744073709551615 () Int)
(declare-fun shr_ (Int Int) Int)
(declare-fun System_dot_ICloneable () Int)
(declare-fun IsDirectlyModifiableField (Int) Int)
(declare-fun StringLength_ (Int) Int)
(declare-fun allocated_ () Int)
(declare-fun BaseClass_ (Int) Int)
(declare-fun ValueArray (Int Int) Int)
(declare-fun Smt_dot_false () Int)
(declare-fun IsImmutable_ (Int) Int)
(declare-fun elements_ () Int)
(declare-fun DeclType (Int) Int)
(declare-fun System_dot_Collections_dot_IEnumerable () Int)
(declare-fun ReallyLastGeneratedExit_correct () Int)
(assert (distinct allocated_ elements_ inv_ localinv_ exposeVersion_ sharingMode_ SharingMode_Unshared_ SharingMode_LockProtected_ ownerRef_ ownerFrame_ PeerGroupPlaceholder_ ArrayCategoryValue_ ArrayCategoryRef_ ArrayCategoryNonNullRef_ System_dot_Array System_dot_Object System_dot_Type BeingConstructed_ NonNullFieldsAreInitialized_ System_dot_String FirstConsistentOwner_ System_dot_SByte System_dot_Byte System_dot_Int16 System_dot_UInt16 System_dot_Int32 System_dot_UInt32 System_dot_Int64 System_dot_UInt64 System_dot_Char int_m2147483648 int_2147483647 int_4294967295 int_m9223372036854775808 int_9223372036854775807 int_18446744073709551615 UnknownRef_ Bag_dot_a Bag_dot_n Microsoft_dot_Contracts_dot_ObjectInvariantException System_dot_Collections_dot_IEnumerable System_dot_Boolean System_dot_ICloneable System_dot_Reflection_dot_ICustomAttributeProvider System_dot_Runtime_dot_Serialization_dot_ISerializable System_dot_Exception System_dot_Reflection_dot_IReflect System_dot_Runtime_dot_InteropServices_dot__Exception System_dot_Collections_dot_ICollection Microsoft_dot_Contracts_dot_ICheckedException Bag Microsoft_dot_Contracts_dot_GuardException System_dot_Runtime_dot_InteropServices_dot__MemberInfo System_dot_Collections_dot_IList System_dot_Runtime_dot_InteropServices_dot__Type System_dot_Reflection_dot_MemberInfo))
(assert (= (DeclType exposeVersion_) System_dot_Object))
(assert (forall ((c0 Int) (c1 Int)) (! (=> (not (= c0 c1)) (not (= (ClassRepr c0) (ClassRepr c1)))) :pattern ((ClassRepr c0) (ClassRepr c1)) )))
(assert (forall ((T Int)) (not (subtypes (typeof_ (ClassRepr T)) System_dot_Object))))
(assert (forall ((T Int)) (not (= (ClassRepr T) nullObject))))
(assert (forall ((T Int) (h Int)) (! (=> (= (IsHeap h) Smt_dot_true) (= (select2 h (ClassRepr T) ownerFrame_) PeerGroupPlaceholder_)) :pattern ((select2 h (ClassRepr T) ownerFrame_)) )))
(assert (not (= (IsDirectlyModifiableField allocated_) Smt_dot_true)))
(assert (= (IsDirectlyModifiableField elements_) Smt_dot_true))
(assert (not (= (IsDirectlyModifiableField inv_) Smt_dot_true)))
(assert (not (= (IsDirectlyModifiableField localinv_) Smt_dot_true)))
(assert (not (= (IsDirectlyModifiableField ownerRef_) Smt_dot_true)))
(assert (not (= (IsDirectlyModifiableField ownerFrame_) Smt_dot_true)))
(assert (not (= (IsDirectlyModifiableField exposeVersion_) Smt_dot_true)))
(assert (not (= (IsStaticField allocated_) Smt_dot_true)))
(assert (not (= (IsStaticField elements_) Smt_dot_true)))
(assert (not (= (IsStaticField inv_) Smt_dot_true)))
(assert (not (= (IsStaticField localinv_) Smt_dot_true)))
(assert (not (= (IsStaticField exposeVersion_) Smt_dot_true)))
(assert (forall ((A Int) (i Int) (x Int)) (= (ValueArrayGet (ValueArraySet A i x) i) x)))
(assert (forall ((A Int) (i Int) (j Int) (x Int)) (=> (not (= i j)) (= (ValueArrayGet (ValueArraySet A i x) j) (ValueArrayGet A j)))))
(assert (forall ((A Int) (i Int) (x Int)) (= (RefArrayGet (RefArraySet A i x) i) x)))
(assert (forall ((A Int) (i Int) (j Int) (x Int)) (=> (not (= i j)) (= (RefArrayGet (RefArraySet A i x) j) (RefArrayGet A j)))))
(assert (forall ((a Int) (d Int) (x Int) (y Int) (_x'_ Int) (_y'_ Int)) (! (=> (= (ArrayIndex a d x y) (ArrayIndex a d _x'_ _y'_)) (and (= x _x'_) (= y _y'_))) :pattern ((ArrayIndex a d x y) (ArrayIndex a d _x'_ _y'_)) )))
(assert (forall ((a Int) (T Int) (i Int) (r Int) (heap Int)) (! (=> (and (= (IsHeap heap) Smt_dot_true) (subtypes (typeof_ a) (RefArray T r))) (= (Is_ (RefArrayGet (select2 heap a elements_) i) T) Smt_dot_true)) :pattern ((subtypes (typeof_ a) (RefArray T r)) (RefArrayGet (select2 heap a elements_) i)) )))
(assert (forall ((a Int) (T Int) (i Int) (r Int) (heap Int)) (! (=> (and (= (IsHeap heap) Smt_dot_true) (subtypes (typeof_ a) (NonNullRefArray T r))) (= (IsNotNull_ (RefArrayGet (select2 heap a elements_) i) T) Smt_dot_true)) :pattern ((subtypes (typeof_ a) (NonNullRefArray T r)) (RefArrayGet (select2 heap a elements_) i)) )))
(assert (forall ((a Int)) (<= 1 (Rank_ a))))
(assert (forall ((a Int) (T Int) (r Int)) (! (=> (and (not (= a nullObject)) (subtypes (typeof_ a) (RefArray T r))) (= (Rank_ a) r)) :pattern ((subtypes (typeof_ a) (RefArray T r))) )))
(assert (forall ((a Int) (T Int) (r Int)) (! (=> (and (not (= a nullObject)) (subtypes (typeof_ a) (NonNullRefArray T r))) (= (Rank_ a) r)) :pattern ((subtypes (typeof_ a) (NonNullRefArray T r))) )))
(assert (forall ((a Int) (T Int) (r Int)) (! (=> (and (not (= a nullObject)) (subtypes (typeof_ a) (ValueArray T r))) (= (Rank_ a) r)) :pattern ((subtypes (typeof_ a) (ValueArray T r))) )))
(assert (forall ((a Int)) (! (<= 0 (Length_ a)) :pattern ((Length_ a)) )))
(assert (forall ((a Int) (i Int)) (<= 0 (DimLength_ a i))))
(assert (forall ((a Int)) (! (=> (= (Rank_ a) 1) (= (DimLength_ a 0) (Length_ a))) :pattern ((DimLength_ a 0)) )))
(assert (forall ((a Int) (i Int)) (! (= (LBound_ a i) 0) :pattern ((LBound_ a i)) )))
(assert (forall ((a Int) (i Int)) (! (= (UBound_ a i) (- (DimLength_ a i) 1)) :pattern ((UBound_ a i)) )))
(assert (forall ((T Int) (ET Int) (r Int)) (! (=> (subtypes T (ValueArray ET r)) (= (ArrayCategory_ T) ArrayCategoryValue_)) :pattern ((subtypes T (ValueArray ET r))) )))
(assert (forall ((T Int) (ET Int) (r Int)) (! (=> (subtypes T (RefArray ET r)) (= (ArrayCategory_ T) ArrayCategoryRef_)) :pattern ((subtypes T (RefArray ET r))) )))
(assert (forall ((T Int) (ET Int) (r Int)) (! (=> (subtypes T (NonNullRefArray ET r)) (= (ArrayCategory_ T) ArrayCategoryNonNullRef_)) :pattern ((subtypes T (NonNullRefArray ET r))) )))
(assert (subtypes System_dot_Array System_dot_Object))
(assert (forall ((T Int) (r Int)) (! (subtypes (ValueArray T r) System_dot_Array) :pattern ((ValueArray T r)) )))
(assert (forall ((T Int) (r Int)) (! (subtypes (RefArray T r) System_dot_Array) :pattern ((RefArray T r)) )))
(assert (forall ((T Int) (r Int)) (! (subtypes (NonNullRefArray T r) System_dot_Array) :pattern ((NonNullRefArray T r)) )))
(assert (forall ((T Int) (U Int) (r Int)) (=> (subtypes U T) (subtypes (RefArray U r) (RefArray T r)))))
(assert (forall ((T Int) (U Int) (r Int)) (=> (subtypes U T) (subtypes (NonNullRefArray U r) (NonNullRefArray T r)))))
(assert (forall ((A Int) (r Int)) (= (ElementType_ (ValueArray A r)) A)))
(assert (forall ((A Int) (r Int)) (= (ElementType_ (RefArray A r)) A)))
(assert (forall ((A Int) (r Int)) (= (ElementType_ (NonNullRefArray A r)) A)))
(assert (forall ((A Int) (r Int) (T Int)) (! (let ((v_0 (ElementType_ T))) (=> (subtypes T (RefArray A r)) (and (= T (RefArray v_0 r)) (subtypes v_0 A)))) :pattern ((subtypes T (RefArray A r))) )))
(assert (forall ((A Int) (r Int) (T Int)) (! (let ((v_0 (ElementType_ T))) (=> (subtypes T (NonNullRefArray A r)) (and (= T (NonNullRefArray v_0 r)) (subtypes v_0 A)))) :pattern ((subtypes T (NonNullRefArray A r))) )))
(assert (forall ((A Int) (r Int) (T Int)) (let ((v_0 (ValueArray A r))) (=> (subtypes T v_0) (= T v_0)))))
(assert (forall ((A Int) (r Int) (T Int)) (let ((v_0 (ElementType_ T))) (=> (subtypes (RefArray A r) T) (or (subtypes System_dot_Array T) (and (= T (RefArray v_0 r)) (subtypes A v_0)))))))
(assert (forall ((A Int) (r Int) (T Int)) (let ((v_0 (ElementType_ T))) (=> (subtypes (NonNullRefArray A r) T) (or (subtypes System_dot_Array T) (and (= T (NonNullRefArray v_0 r)) (subtypes A v_0)))))))
(assert (forall ((A Int) (r Int) (T Int)) (let ((v_0 (ValueArray A r))) (=> (subtypes v_0 T) (or (subtypes System_dot_Array T) (= T v_0))))))
(assert (forall ((s Int) (f Int) (x Int)) (= (StructGet_ (StructSet_ s f x) f) x)))
(assert (forall ((s Int) (f Int) (_f'_ Int) (x Int)) (=> (not (= f _f'_)) (= (StructGet_ (StructSet_ s f x) _f'_) (StructGet_ s _f'_)))))
(assert (forall ((A Int) (B Int) (C Int)) (! (=> (subtypes C (AsDirectSubClass B A)) (= (OneClassDown C A) B)) :pattern ((subtypes C (AsDirectSubClass B A))) )))
(assert (forall ((T Int)) (=> (= (IsValueType_ T) Smt_dot_true) (and (forall ((U Int)) (=> (subtypes T U) (= T U))) (forall ((U Int)) (=> (subtypes U T) (= T U)))))))
(assert (subtypes System_dot_Type System_dot_Object))
(assert (forall ((T Int)) (! (= (IsNotNull_ (TypeObject T) System_dot_Type) Smt_dot_true) :pattern ((TypeObject T)) )))
(assert (forall ((T Int)) (! (= (TypeName (TypeObject T)) T) :pattern ((TypeObject T)) )))
(assert (forall ((o Int) (T Int)) (! (= (= (Is_ o T) Smt_dot_true) (or (= o nullObject) (subtypes (typeof_ o) T))) :pattern ((Is_ o T)) )))
(assert (forall ((o Int) (T Int)) (! (= (= (IsNotNull_ o T) Smt_dot_true) (and (not (= o nullObject)) (= (Is_ o T) Smt_dot_true))) :pattern ((IsNotNull_ o T)) )))
(assert (forall ((o Int) (T Int)) (=> (= (Is_ o T) Smt_dot_true) (= (As_ o T) o))))
(assert (forall ((o Int) (T Int)) (=> (not (= (Is_ o T) Smt_dot_true)) (= (As_ o T) nullObject))))
(assert (forall ((h Int) (o Int)) (! (let ((v_0 (typeof_ o))) (=> (and (= (IsHeap h) Smt_dot_true) (not (= o nullObject)) (subtypes v_0 System_dot_Array)) (and (= (select2 h o inv_) v_0) (= (select2 h o localinv_) v_0)))) :pattern ((select2 h o inv_)) )))
(assert (forall ((h Int) (o Int) (f Int)) (! (=> (and (= (IsHeap h) Smt_dot_true) (= (select2 h o allocated_) Smt_dot_true)) (= (IsAllocated h (select2 h o f)) Smt_dot_true)) :pattern ((IsAllocated h (select2 h o f))) )))
(assert (forall ((h Int) (o Int) (f Int)) (! (=> (and (= (IsHeap h) Smt_dot_true) (= (select2 h o allocated_) Smt_dot_true)) (= (select2 h (select2 h o f) allocated_) Smt_dot_true)) :pattern ((select2 h (select2 h o f) allocated_)) )))
(assert (forall ((h Int) (s Int) (f Int)) (! (=> (= (IsAllocated h s) Smt_dot_true) (= (IsAllocated h (StructGet_ s f)) Smt_dot_true)) :pattern ((IsAllocated h (StructGet_ s f))) )))
(assert (forall ((h Int) (e Int) (i Int)) (! (=> (= (IsAllocated h e) Smt_dot_true) (= (IsAllocated h (RefArrayGet e i)) Smt_dot_true)) :pattern ((IsAllocated h (RefArrayGet e i))) )))
(assert (forall ((h Int) (e Int) (i Int)) (! (=> (= (IsAllocated h e) Smt_dot_true) (= (IsAllocated h (ValueArrayGet e i)) Smt_dot_true)) :pattern ((IsAllocated h (ValueArrayGet e i))) )))
(assert (forall ((h Int) (o Int)) (! (=> (= (IsAllocated h o) Smt_dot_true) (= (select2 h o allocated_) Smt_dot_true)) :pattern ((select2 h o allocated_)) )))
(assert (forall ((h Int) (c Int)) (! (=> (= (IsHeap h) Smt_dot_true) (= (select2 h (ClassRepr c) allocated_) Smt_dot_true)) :pattern ((select2 h (ClassRepr c) allocated_)) )))
(assert (forall ((f Int) (T Int)) (! (=> (= (AsNonNullRefField f T) f) (= (AsRefField f T) f)) :pattern ((AsNonNullRefField f T)) )))
(assert (forall ((h Int) (o Int) (f Int) (T Int)) (! (=> (= (IsHeap h) Smt_dot_true) (= (Is_ (select2 h o (AsRefField f T)) T) Smt_dot_true)) :pattern ((select2 h o (AsRefField f T))) )))
(assert (forall ((h Int) (o Int) (f Int) (T Int)) (! (=> (and (= (IsHeap h) Smt_dot_true) (not (= o nullObject)) (or (not (= o BeingConstructed_)) (= (= (select2 h BeingConstructed_ NonNullFieldsAreInitialized_) Smt_dot_true) true))) (not (= (select2 h o (AsNonNullRefField f T)) nullObject))) :pattern ((select2 h o (AsNonNullRefField f T))) )))
(assert (forall ((h Int) (o Int) (f Int) (T Int)) (! (=> (= (IsHeap h) Smt_dot_true) (InRange (select2 h o (AsRangeField f T)) T)) :pattern ((select2 h o (AsRangeField f T))) )))
(assert (forall ((o Int)) (! (not (= (IsMemberlessType_ (typeof_ o)) Smt_dot_true)) :pattern ((IsMemberlessType_ (typeof_ o))) )))
(assert (not (= (IsImmutable_ System_dot_Object) Smt_dot_true)))
(assert (forall ((T Int) (U Int)) (! (=> (subtypes U (AsImmutable_ T)) (and (= (IsImmutable_ U) Smt_dot_true) (= (AsImmutable_ U) U))) :pattern ((subtypes U (AsImmutable_ T))) )))
(assert (forall ((T Int) (U Int)) (! (=> (subtypes U (AsMutable_ T)) (and (not (= (IsImmutable_ U) Smt_dot_true)) (= (AsMutable_ U) U))) :pattern ((subtypes U (AsMutable_ T))) )))
(assert (forall ((o Int) (T Int)) (! (=> (and (not (= o nullObject)) (not (= o BeingConstructed_)) (subtypes (typeof_ o) (AsImmutable_ T))) (forall ((h Int)) (! (let ((v_0 (typeof_ o))) (=> (= (IsHeap h) Smt_dot_true) (and (= (select2 h o inv_) v_0) (= (select2 h o localinv_) v_0) (= (select2 h o ownerFrame_) PeerGroupPlaceholder_) (= (AsOwner o (select2 h o ownerRef_)) o) (forall ((t Int)) (! (=> (= (AsOwner o (select2 h t ownerRef_)) o) (or (= t o) (not (= (select2 h t ownerFrame_) PeerGroupPlaceholder_)))) :pattern ((AsOwner o (select2 h t ownerRef_))) ))))) :pattern ((IsHeap h)) ))) :pattern ((subtypes (typeof_ o) (AsImmutable_ T))) )))
(assert (forall ((s Int)) (! (<= 0 (StringLength_ s)) :pattern ((StringLength_ s)) )))
(assert (forall ((h Int) (o Int) (f Int) (T Int)) (! (let ((v_0 (select2 h o (AsRepField f T)))) (=> (and (= (IsHeap h) Smt_dot_true) (not (= v_0 nullObject))) (and (= (select2 h v_0 ownerRef_) o) (= (select2 h v_0 ownerFrame_) T)))) :pattern ((select2 h o (AsRepField f T))) )))
(assert (forall ((h Int) (o Int) (f Int)) (! (let ((v_0 (select2 h o (AsPeerField f)))) (=> (and (= (IsHeap h) Smt_dot_true) (not (= v_0 nullObject))) (and (= (select2 h v_0 ownerRef_) (select2 h o ownerRef_)) (= (select2 h v_0 ownerFrame_) (select2 h o ownerFrame_))))) :pattern ((select2 h o (AsPeerField f))) )))
(assert (forall ((h Int) (o Int)) (let ((v_0 (select2 h o ownerFrame_)) (v_1 (select2 h o ownerRef_)) (v_2 (typeof_ o))) (=> (and (= (IsHeap h) Smt_dot_true) (not (= v_0 PeerGroupPlaceholder_)) (subtypes (select2 h v_1 inv_) v_0) (not (= (select2 h v_1 localinv_) (BaseClass_ v_0)))) (and (= (select2 h o inv_) v_2) (= (select2 h o localinv_) v_2))))))
(assert (forall ((o Int) (f Int) (h Int)) (! (let ((v_0 (select2 h o ownerFrame_)) (v_1 (select2 h o ownerRef_))) (=> (and (= (IsHeap h) Smt_dot_true) (not (= o nullObject)) (= (= (select2 h o allocated_) Smt_dot_true) true) (not (= v_0 PeerGroupPlaceholder_)) (subtypes (select2 h v_1 inv_) v_0) (not (= (select2 h v_1 localinv_) (BaseClass_ v_0)))) (= (select2 h o f) (FieldDependsOnFCO_ o f (select2 h (select2 h o FirstConsistentOwner_) exposeVersion_))))) :pattern ((select2 h (AsPureObject_ o) f)) )))
(assert (forall ((o Int) (h Int)) (! (let ((v_0 (select2 h o ownerFrame_)) (v_1 (select2 h o ownerRef_)) (v_2 (select2 h o FirstConsistentOwner_))) (let ((v_3 (select2 h v_2 ownerFrame_)) (v_4 (select2 h v_2 ownerRef_))) (=> (and (= (IsHeap h) Smt_dot_true) (not (= o nullObject)) (= (= (select2 h o allocated_) Smt_dot_true) true) (not (= v_0 PeerGroupPlaceholder_)) (subtypes (select2 h v_1 inv_) v_0) (not (= (select2 h v_1 localinv_) (BaseClass_ v_0)))) (and (not (= v_2 nullObject)) (= (= (select2 h v_2 allocated_) Smt_dot_true) true) (or (= v_3 PeerGroupPlaceholder_) (not (subtypes (select2 h v_4 inv_) v_3)) (= (select2 h v_4 localinv_) (BaseClass_ v_3))))))) :pattern ((select2 h o FirstConsistentOwner_)) )))
(assert (forall ((x Int) (p Int)) (! (= (Unbox (Box x p)) x) :pattern ((Unbox (Box x p))) )))
(assert (forall ((p Int)) (! (=> (= (IsValueType_ (UnboxedType p)) Smt_dot_true) (forall ((heap Int) (x Int)) (let ((v_0 (Box x p))) (let ((v_1 (typeof_ v_0))) (=> (= (IsHeap heap) Smt_dot_true) (and (= (select2 heap v_0 inv_) v_1) (= (select2 heap v_0 localinv_) v_1))))))) :pattern ((IsValueType_ (UnboxedType p))) )))
(assert (forall ((x Int) (p Int)) (let ((v_0 (Box x p))) (=> (and (subtypes (UnboxedType v_0) System_dot_Object) (= v_0 p)) (= x p)))))
(assert (forall ((p Int) (typ Int)) (! (= (= (UnboxedType p) typ) (not (= (BoxTester p typ) nullObject))) :pattern ((BoxTester p typ)) )))
(assert (= (IsValueType_ System_dot_SByte) Smt_dot_true))
(assert (= (IsValueType_ System_dot_Byte) Smt_dot_true))
(assert (= (IsValueType_ System_dot_Int16) Smt_dot_true))
(assert (= (IsValueType_ System_dot_UInt16) Smt_dot_true))
(assert (= (IsValueType_ System_dot_Int32) Smt_dot_true))
(assert (= (IsValueType_ System_dot_UInt32) Smt_dot_true))
(assert (= (IsValueType_ System_dot_Int64) Smt_dot_true))
(assert (= (IsValueType_ System_dot_UInt64) Smt_dot_true))
(assert (= (IsValueType_ System_dot_Char) Smt_dot_true))
(assert (< int_m9223372036854775808 int_m2147483648))
(assert (< int_m2147483648 (- 0 100000)))
(assert (< 100000 int_2147483647))
(assert (< int_2147483647 int_4294967295))
(assert (< int_4294967295 int_9223372036854775807))
(assert (< int_9223372036854775807 int_18446744073709551615))
(assert (forall ((i Int)) (= (InRange i System_dot_SByte) (and (<= (- 0 128) i) (< i 128)))))
(assert (forall ((i Int)) (= (InRange i System_dot_Byte) (and (<= 0 i) (< i 256)))))
(assert (forall ((i Int)) (= (InRange i System_dot_Int16) (and (<= (- 0 32768) i) (< i 32768)))))
(assert (forall ((i Int)) (= (InRange i System_dot_UInt16) (and (<= 0 i) (< i 65536)))))
(assert (forall ((i Int)) (= (InRange i System_dot_Int32) (and (<= int_m2147483648 i) (<= i int_2147483647)))))
(assert (forall ((i Int)) (= (InRange i System_dot_UInt32) (and (<= 0 i) (<= i int_4294967295)))))
(assert (forall ((i Int)) (= (InRange i System_dot_Int64) (and (<= int_m9223372036854775808 i) (<= i int_9223372036854775807)))))
(assert (forall ((i Int)) (= (InRange i System_dot_UInt64) (and (<= 0 i) (<= i int_18446744073709551615)))))
(assert (forall ((i Int)) (= (InRange i System_dot_Char) (and (<= 0 i) (< i 65536)))))
(assert (forall ((b Int) (x Int) (y Int)) (! (=> (= b Smt_dot_true) (= (IfThenElse_ b x y) x)) :pattern ((IfThenElse_ b x y)) )))
(assert (forall ((b Int) (x Int) (y Int)) (! (=> (not (= b Smt_dot_true)) (= (IfThenElse_ b x y) y)) :pattern ((IfThenElse_ b x y)) )))
(assert (forall ((x Int) (y Int)) (! (= (modulo x y) (- x (multiply (divide x y) y))) :pattern ((modulo x y))  :pattern ((divide x y)) )))
(assert (forall ((x Int) (y Int)) (! (let ((v_0 (modulo x y))) (=> (and (<= 0 x) (< 0 y)) (and (<= 0 v_0) (< v_0 y)))) :pattern ((modulo x y)) )))
(assert (forall ((x Int) (y Int)) (! (let ((v_0 (modulo x y))) (=> (and (<= 0 x) (< y 0)) (and (<= 0 v_0) (< v_0 (- 0 y))))) :pattern ((modulo x y)) )))
(assert (forall ((x Int) (y Int)) (! (let ((v_0 (modulo x y))) (=> (and (<= x 0) (< 0 y)) (and (< (- 0 y) v_0) (<= v_0 0)))) :pattern ((modulo x y)) )))
(assert (forall ((x Int) (y Int)) (! (let ((v_0 (modulo x y))) (=> (and (<= x 0) (< y 0)) (and (< y v_0) (<= v_0 0)))) :pattern ((modulo x y)) )))
(assert (forall ((x Int) (y Int)) (=> (and (<= 0 x) (<= 0 y)) (= (modulo (+ x y) y) (modulo x y)))))
(assert (forall ((x Int) (y Int)) (=> (and (<= 0 x) (<= 0 y)) (= (modulo (+ y x) y) (modulo x y)))))
(assert (forall ((x Int) (y Int)) (let ((v_0 (- x y))) (=> (and (<= 0 v_0) (<= 0 y)) (= (modulo v_0 y) (modulo x y))))))
(assert (forall ((a Int) (b Int) (d Int)) (! (=> (and (<= 2 d) (= (modulo a d) (modulo b d)) (< a b)) (<= (+ a d) b)) :pattern ((modulo a d) (modulo b d)) )))
(assert (forall ((x Int) (y Int)) (! (=> (or (<= 0 x) (<= 0 y)) (<= 0 (_and_ x y))) :pattern ((_and_ x y)) )))
(assert (forall ((x Int) (y Int)) (! (let ((v_0 (_or_ x y))) (=> (and (<= 0 x) (<= 0 y)) (and (<= 0 v_0) (<= v_0 (+ x y))))) :pattern ((_or_ x y)) )))
(assert (forall ((i Int)) (! (= (shl_ i 0) i) :pattern ((shl_ i 0)) )))
(assert (forall ((i Int) (j Int)) (=> (<= 0 j) (= (shl_ i (+ j 1)) ( * (shl_ i j) 2)))))
(assert (forall ((i Int)) (! (= (shr_ i 0) i) :pattern ((shr_ i 0)) )))
(assert (forall ((i Int) (j Int)) (=> (<= 0 j) (= (shr_ i (+ j 1)) (divide (shr_ i j) 2)))))
(assert (forall ((a Int) (b Int)) (! (= (= (System_dot_String_dot_Equals_System_dot_String_ a b) Smt_dot_true) (= (System_dot_String_dot_Equals_System_dot_String_System_dot_String_ a b) Smt_dot_true)) :pattern ((System_dot_String_dot_Equals_System_dot_String_ a b)) )))
(assert (forall ((a Int) (b Int)) (! (= (= (System_dot_String_dot_Equals_System_dot_String_System_dot_String_ a b) Smt_dot_true) (= (System_dot_String_dot_Equals_System_dot_String_System_dot_String_ b a) Smt_dot_true)) :pattern ((System_dot_String_dot_Equals_System_dot_String_System_dot_String_ a b)) )))
(assert (forall ((a Int) (b Int)) (! (=> (and (not (= a nullObject)) (not (= b nullObject)) (= (System_dot_String_dot_Equals_System_dot_String_System_dot_String_ a b) Smt_dot_true)) (= (System_dot_String_dot_IsInterned_System_dot_String_notnull_ a) (System_dot_String_dot_IsInterned_System_dot_String_notnull_ b))) :pattern ((System_dot_String_dot_Equals_System_dot_String_System_dot_String_ a b)) )))
(assert (not (= (IsStaticField Bag_dot_n) Smt_dot_true)))
(assert (= (IsDirectlyModifiableField Bag_dot_n) Smt_dot_true))
(assert (= (DeclType Bag_dot_n) Bag))
(assert (= (AsRangeField Bag_dot_n System_dot_Int32) Bag_dot_n))
(assert (not (= (IsStaticField Bag_dot_a) Smt_dot_true)))
(assert (= (IsDirectlyModifiableField Bag_dot_a) Smt_dot_true))
(assert (= (AsRepField Bag_dot_a Bag) Bag_dot_a))
(assert (= (DeclType Bag_dot_a) Bag))
(assert (= (AsNonNullRefField Bag_dot_a (ValueArray System_dot_Int32 1)) Bag_dot_a))
(assert (subtypes Bag Bag))
(assert (= (BaseClass_ Bag) System_dot_Object))
(assert (subtypes Bag (BaseClass_ Bag)))
(assert (= (AsDirectSubClass Bag (BaseClass_ Bag)) Bag))
(assert (not (= (IsImmutable_ Bag) Smt_dot_true)))
(assert (= (AsMutable_ Bag) Bag))
(assert (forall ((oi_ Int) (h_ Int)) (! (let ((v_0 (select2 h_ oi_ Bag_dot_n))) (=> (and (= (IsHeap h_) Smt_dot_true) (subtypes (select2 h_ oi_ inv_) Bag) (not (= (select2 h_ oi_ localinv_) System_dot_Object))) (and (<= 0 v_0) (<= v_0 (Length_ (select2 h_ oi_ Bag_dot_a)))))) :pattern ((subtypes (select2 h_ oi_ inv_) Bag)) )))
(assert (forall ((U_ Int)) (! (=> (subtypes U_ System_dot_Boolean) (= U_ System_dot_Boolean)) :pattern ((subtypes U_ System_dot_Boolean)) )))
(assert (subtypes Microsoft_dot_Contracts_dot_ObjectInvariantException Microsoft_dot_Contracts_dot_ObjectInvariantException))
(assert (subtypes Microsoft_dot_Contracts_dot_GuardException Microsoft_dot_Contracts_dot_GuardException))
(assert (subtypes System_dot_Exception System_dot_Exception))
(assert (= (BaseClass_ System_dot_Exception) System_dot_Object))
(assert (subtypes System_dot_Exception (BaseClass_ System_dot_Exception)))
(assert (= (AsDirectSubClass System_dot_Exception (BaseClass_ System_dot_Exception)) System_dot_Exception))
(assert (not (= (IsImmutable_ System_dot_Exception) Smt_dot_true)))
(assert (= (AsMutable_ System_dot_Exception) System_dot_Exception))
(assert (subtypes System_dot_Runtime_dot_Serialization_dot_ISerializable System_dot_Object))
(assert (= (IsMemberlessType_ System_dot_Runtime_dot_Serialization_dot_ISerializable) Smt_dot_true))
(assert (subtypes System_dot_Exception System_dot_Runtime_dot_Serialization_dot_ISerializable))
(assert (subtypes System_dot_Runtime_dot_InteropServices_dot__Exception System_dot_Object))
(assert (= (IsMemberlessType_ System_dot_Runtime_dot_InteropServices_dot__Exception) Smt_dot_true))
(assert (subtypes System_dot_Exception System_dot_Runtime_dot_InteropServices_dot__Exception))
(assert (= (BaseClass_ Microsoft_dot_Contracts_dot_GuardException) System_dot_Exception))
(assert (subtypes Microsoft_dot_Contracts_dot_GuardException (BaseClass_ Microsoft_dot_Contracts_dot_GuardException)))
(assert (= (AsDirectSubClass Microsoft_dot_Contracts_dot_GuardException (BaseClass_ Microsoft_dot_Contracts_dot_GuardException)) Microsoft_dot_Contracts_dot_GuardException))
(assert (not (= (IsImmutable_ Microsoft_dot_Contracts_dot_GuardException) Smt_dot_true)))
(assert (= (AsMutable_ Microsoft_dot_Contracts_dot_GuardException) Microsoft_dot_Contracts_dot_GuardException))
(assert (= (BaseClass_ Microsoft_dot_Contracts_dot_ObjectInvariantException) Microsoft_dot_Contracts_dot_GuardException))
(assert (subtypes Microsoft_dot_Contracts_dot_ObjectInvariantException (BaseClass_ Microsoft_dot_Contracts_dot_ObjectInvariantException)))
(assert (= (AsDirectSubClass Microsoft_dot_Contracts_dot_ObjectInvariantException (BaseClass_ Microsoft_dot_Contracts_dot_ObjectInvariantException)) Microsoft_dot_Contracts_dot_ObjectInvariantException))
(assert (not (= (IsImmutable_ Microsoft_dot_Contracts_dot_ObjectInvariantException) Smt_dot_true)))
(assert (= (AsMutable_ Microsoft_dot_Contracts_dot_ObjectInvariantException) Microsoft_dot_Contracts_dot_ObjectInvariantException))
(assert (subtypes System_dot_Array System_dot_Array))
(assert (= (BaseClass_ System_dot_Array) System_dot_Object))
(assert (subtypes System_dot_Array (BaseClass_ System_dot_Array)))
(assert (= (AsDirectSubClass System_dot_Array (BaseClass_ System_dot_Array)) System_dot_Array))
(assert (not (= (IsImmutable_ System_dot_Array) Smt_dot_true)))
(assert (= (AsMutable_ System_dot_Array) System_dot_Array))
(assert (subtypes System_dot_ICloneable System_dot_Object))
(assert (= (IsMemberlessType_ System_dot_ICloneable) Smt_dot_true))
(assert (subtypes System_dot_Array System_dot_ICloneable))
(assert (subtypes System_dot_Collections_dot_IList System_dot_Object))
(assert (subtypes System_dot_Collections_dot_ICollection System_dot_Object))
(assert (subtypes System_dot_Collections_dot_IEnumerable System_dot_Object))
(assert (= (IsMemberlessType_ System_dot_Collections_dot_IEnumerable) Smt_dot_true))
(assert (subtypes System_dot_Collections_dot_ICollection System_dot_Collections_dot_IEnumerable))
(assert (= (IsMemberlessType_ System_dot_Collections_dot_ICollection) Smt_dot_true))
(assert (subtypes System_dot_Collections_dot_IList System_dot_Collections_dot_ICollection))
(assert (subtypes System_dot_Collections_dot_IList System_dot_Collections_dot_IEnumerable))
(assert (= (IsMemberlessType_ System_dot_Collections_dot_IList) Smt_dot_true))
(assert (subtypes System_dot_Array System_dot_Collections_dot_IList))
(assert (subtypes System_dot_Array System_dot_Collections_dot_ICollection))
(assert (subtypes System_dot_Array System_dot_Collections_dot_IEnumerable))
(assert (= (IsMemberlessType_ System_dot_Array) Smt_dot_true))
(assert (subtypes System_dot_Type System_dot_Type))
(assert (subtypes System_dot_Reflection_dot_MemberInfo System_dot_Reflection_dot_MemberInfo))
(assert (= (BaseClass_ System_dot_Reflection_dot_MemberInfo) System_dot_Object))
(assert (subtypes System_dot_Reflection_dot_MemberInfo (BaseClass_ System_dot_Reflection_dot_MemberInfo)))
(assert (= (AsDirectSubClass System_dot_Reflection_dot_MemberInfo (BaseClass_ System_dot_Reflection_dot_MemberInfo)) System_dot_Reflection_dot_MemberInfo))
(assert (= (IsImmutable_ System_dot_Reflection_dot_MemberInfo) Smt_dot_true))
(assert (= (AsImmutable_ System_dot_Reflection_dot_MemberInfo) System_dot_Reflection_dot_MemberInfo))
(assert (subtypes System_dot_Reflection_dot_ICustomAttributeProvider System_dot_Object))
(assert (= (IsMemberlessType_ System_dot_Reflection_dot_ICustomAttributeProvider) Smt_dot_true))
(assert (subtypes System_dot_Reflection_dot_MemberInfo System_dot_Reflection_dot_ICustomAttributeProvider))
(assert (subtypes System_dot_Runtime_dot_InteropServices_dot__MemberInfo System_dot_Object))
(assert (= (IsMemberlessType_ System_dot_Runtime_dot_InteropServices_dot__MemberInfo) Smt_dot_true))
(assert (subtypes System_dot_Reflection_dot_MemberInfo System_dot_Runtime_dot_InteropServices_dot__MemberInfo))
(assert (= (IsMemberlessType_ System_dot_Reflection_dot_MemberInfo) Smt_dot_true))
(assert (= (BaseClass_ System_dot_Type) System_dot_Reflection_dot_MemberInfo))
(assert (subtypes System_dot_Type (BaseClass_ System_dot_Type)))
(assert (= (AsDirectSubClass System_dot_Type (BaseClass_ System_dot_Type)) System_dot_Type))
(assert (= (IsImmutable_ System_dot_Type) Smt_dot_true))
(assert (= (AsImmutable_ System_dot_Type) System_dot_Type))
(assert (subtypes System_dot_Runtime_dot_InteropServices_dot__Type System_dot_Object))
(assert (= (IsMemberlessType_ System_dot_Runtime_dot_InteropServices_dot__Type) Smt_dot_true))
(assert (subtypes System_dot_Type System_dot_Runtime_dot_InteropServices_dot__Type))
(assert (subtypes System_dot_Reflection_dot_IReflect System_dot_Object))
(assert (= (IsMemberlessType_ System_dot_Reflection_dot_IReflect) Smt_dot_true))
(assert (subtypes System_dot_Type System_dot_Reflection_dot_IReflect))
(assert (= (IsMemberlessType_ System_dot_Type) Smt_dot_true))
(assert (subtypes Microsoft_dot_Contracts_dot_ICheckedException System_dot_Object))
(assert (= (IsMemberlessType_ Microsoft_dot_Contracts_dot_ICheckedException) Smt_dot_true))
(assert (forall ((A Int) (i Int) (v Int)) (= (select1 (store1 A i v) i) v)))
(assert (forall ((A Int) (i Int) (j Int) (v Int)) (=> (not (= i j)) (= (select1 (store1 A i v) j) (select1 A j)))))
(assert (forall ((A Int) (o Int) (f Int) (v Int)) (= (select2 (store2 A o f v) o f) v)))
(assert (forall ((A Int) (o Int) (f Int) (p Int) (g Int) (v Int)) (=> (not (= o p)) (= (select2 (store2 A o f v) p g) (select2 A p g)))))
(assert (forall ((A Int) (o Int) (f Int) (p Int) (g Int) (v Int)) (=> (not (= f g)) (= (select2 (store2 A o f v) p g) (select2 A p g)))))
(assert (forall ((x Int) (y Int)) (= (= (boolIff x y) Smt_dot_true) (= (= x Smt_dot_true) (= y Smt_dot_true)))))
(assert (forall ((x Int) (y Int)) (= (= (boolImplies x y) Smt_dot_true) (=> (= x Smt_dot_true) (= y Smt_dot_true)))))
(assert (forall ((x Int) (y Int)) (= (= (boolAnd x y) Smt_dot_true) (and (= x Smt_dot_true) (= y Smt_dot_true)))))
(assert (forall ((x Int) (y Int)) (= (= (boolOr x y) Smt_dot_true) (or (= x Smt_dot_true) (= y Smt_dot_true)))))
(assert (forall ((x Int)) (! (= (= (boolNot x) Smt_dot_true) (not (= x Smt_dot_true))) :pattern ((boolNot x)) )))
(assert (forall ((x Int) (y Int)) (= (= (anyEqual x y) Smt_dot_true) (= x y))))
(assert (forall ((x Int) (y Int)) (! (= (= (anyNeq x y) Smt_dot_true) (not (= x y))) :pattern ((anyNeq x y)) )))
(assert (forall ((x Int) (y Int)) (= (= (intLess x y) Smt_dot_true) (< x y))))
(assert (forall ((x Int) (y Int)) (= (= (intAtMost x y) Smt_dot_true) (<= x y))))
(assert (forall ((x Int) (y Int)) (= (= (intAtLeast x y) Smt_dot_true) (>= x y))))
(assert (forall ((x Int) (y Int)) (= (= (intGreater x y) Smt_dot_true) (> x y))))
(assert (distinct Smt_dot_false Smt_dot_true))
(assert (forall ((t Int)) (! (subtypes t t) :pattern ((subtypes t t)) )))
(assert (forall ((t Int) (u Int) (v Int)) (! (=> (and (subtypes t u) (subtypes u v)) (subtypes t v)) :pattern ((subtypes t u) (subtypes u v)) )))
(assert (forall ((t Int) (u Int)) (! (=> (and (subtypes t u) (subtypes u t)) (= t u)) :pattern ((subtypes t u) (subtypes u t)) )))
(assert (let ((v_0 (forall ((o_ Int)) (let ((v_5 (select2 Heap_ o_ ownerRef_)) (v_6 (select2 Heap_ o_ ownerFrame_))) (=> (and (not (= o_ nullObject)) (= (= (select2 Heap_ o_ allocated_) Smt_dot_true) true)) (and (= v_5 v_5) (= v_6 v_6)))))) (v_1 (= ReallyLastGeneratedExit_correct Smt_dot_true)) (v_2 (= block6086_correct Smt_dot_true)) (v_3 (= block6069_correct Smt_dot_true)) (v_4 (= entry_correct Smt_dot_true))) (not (=> (=> (=> true (=> (= (IsHeap Heap_) Smt_dot_true) (=> (= BeingConstructed_ nullObject) (=> true (=> true (=> (=> (=> true (=> true (=> true (=> (=> (=> true (=> true (=> true (=> (=> (=> true (and v_0 (=> v_0 (=> true true)))) v_1) v_1)))) v_2) v_2)))) v_3) v_3)))))) v_4) v_4))))
(check-sat)
.
  intros.
  (* cbv beta delta [with_pattern] in *. *)
  cbv [with_pattern] in *.

  rewrite! True_implies in H244.
  rewrite! implies_True in H244.
  rewrite! and_True in H244.
  setoid_rewrite equals_True in H244.
  apply H244; clear H244.
  intro P. apply P. clear P.
  intros P1 P2 P3.
  apply P3; clear P3.
  intro P; apply P; clear P.
  intro P; apply P; clear P.
  intros *.
  intro P3. destruct P3 as [P3 P4].
  split; reflexivity. (* turns out to be a trivial goal *)
Qed.

(* https://www.starexec.org/starexec/secure/details/benchmark.jsp?id=6920515
(amortized queues in leon) declares datatypes, and these cannot be parsed as a goal
*)
