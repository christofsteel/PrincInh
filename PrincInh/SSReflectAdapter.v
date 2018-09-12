Require Import mathcomp.ssreflect.fingraph.
Require Import mathcomp.ssreflect.fintype.
Require Import ssrbool.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Classes.EquivDec.

Require Import PrincInh.Utils.
Require Import PrincInh.Paths.
Require Import PrincInh.TypesCommon.

Import Notations.
Import ListNotations.

Inductive t_Path rho : type -> Type :=
| mt_path : t_Path rho rho
| t_Src sigma tau : rho = (sigma ~> tau) -> t_Path rho sigma
| t_Tgt sigma tau : rho = (sigma ~> tau) -> t_Path rho tau.

Canonical t_Path_fin := Eval hnf. in FinType (t_Path rho tau) _.

Instance t_Path_fin : forall tau rho, t_Path tau rho = finType.

Lemma t_Path_to_Path (rho : type) : t_Path rho rho.

Lemma t_Path_Path : t_Path rho rho' -> {p, P 


Inductive In_T {A} : A -> list A -> Type :=
  | In_T_head a x l: (a = x) -> In_T x (a :: l)
  | In_T_tail a x l : In_T x l -> In_T x (a:: l).

Lemma In_In_T {A} {eqdec : EqDec A eq} (a :A) l : In a l -> In_T a l.
Proof.
  intros.
  induction l.
  - inversion H.
  - apply (In_head_set) in H. destruct H. constructor 1. assumption. constructor 2. apply IHl. assumption.
Qed.

Lemma In_T_In {A} (a: A) l : In_T a l -> In a l.
Proof.
  induction l; intros.
  - inversion X.
  - inversion X. constructor. assumption.
    constructor 2. apply IHl. assumption.
Qed.

Instance path_fintype : FinType path.

Lemma path_fintype : Path : fin

Definition R_rel {A} {eqdec: EqDec A eq} (l : list (A * A)) : rel A :=
  fun a b => Inb (a,b) l.

Definition R_rel_equiv {A} {eqdec: EqDec A eq} l : rel A :=
  connect (R_rel l).


Print In_rel.

Check [x | In].


connect
ssrbool.rel

eq_cl_prop