Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Autosubst.Autosubst.

Require Import PrincInh.TypesCommon.
Require Import PrincInh.TypesType.
Require Import PrincInh.Terms.
Require Import PrincInh.Utils.

Import ListNotations.
      
Inductive ty_P (Gamma : list type) : term -> type -> Prop:=
| Ty_Var_P x A : nth_error Gamma x = Some A ->
        ty_P Gamma (Var x) A
| Ty_Lam_P s A B : ty_P (A :: Gamma) s B ->
        ty_P Gamma (Lam s) (Arr A B)
| Ty_App_P s t A B : ty_P Gamma s (Arr A B) -> ty_P Gamma t A ->
                   ty_P Gamma (App s t) B.

Lemma ty_P_inh_ty_T : forall Gamma m tau, ty_P Gamma m tau <-> inhabited (ty_T Gamma m tau).
Proof.
  intros.
  split.
  - intros. induction H.
    + constructor. constructor. assumption.
    + inversion IHty_P. constructor. constructor. assumption.
    + inversion IHty_P1. inversion IHty_P2. constructor. econstructor.
      * apply X.
      * assumption.
  - intros. ainv. induction X.
    + constructor. assumption.
    + constructor. assumption.
    + econstructor. apply IHX1. apply IHX2.
Qed.

Lemma generation_app_P : forall s t tau Gamma, ty_P Gamma (s@t) tau ->
                             exists sigma, ty_P Gamma s (sigma ~> tau) /\ ty_P Gamma t sigma.
Proof.
  intros s t tau Gamma H.
  inv H.
  exists A.
  split; assumption.
Qed.

Lemma generation_lam_P : forall s A Gamma sigma tau, ty_P Gamma (\_ s) A ->
                        A = sigma ~> tau ->
                        ty_P (sigma :: Gamma) s tau.
Proof.
  intros.
  ainv.
Qed.

Lemma generation_var_P : forall x A Gamma, ty_P Gamma (! x) A ->
                          nth_error Gamma x = Some A.
Proof.
  intros.
  ainv.
Qed.
  
Lemma ty_app_ex_P : forall Gamma (B:type) s t, ty_P Gamma (App s t) B -> exists A, ty_P Gamma t A ->
    ty_P Gamma s (A ~> B).
Proof.
    intros. ainv. exists A. ainv. 
Qed.

Definition has_ty_P (m: term) (tau: type) : Prop :=
    ty_P [] m tau.

Example ident_typing_P : has_ty_P (\_ !0) (?0 ~> ?0).
Proof.
    unfold has_ty_P.
    constructor. constructor. reflexivity.
Qed.


Theorem subst_ty_P : forall Gamma s A, ty_P Gamma s A ->
    forall (Su : var -> type), ty_P Gamma..[Su] s A.[Su]. 
Proof.
    intros.
    generalize dependent A.
    generalize dependent Gamma.
    induction s.
    - intros Gamma A. constructor. apply subst_repo_some. inversion H. assumption.
    - intros Gamma A. ainv. econstructor.
      + pose proof (IHs1 Gamma (A0 ~> A)). asimpl in H. apply H. assumption.
      + apply IHs2. eassumption.
    - intros Gamma A. ainv. constructor. rewrite subst_repo_cons. eapply IHs. assumption.
Qed.

Definition Typable_P (t:term) := exists tau Gamma, ty_P Gamma t tau.

Theorem typable_subterm_P : forall m t, Typable_P t -> subterm m t -> Typable_P m.
Proof.
    intros.
    induction H0.
    - assumption.
    - apply IHsubterm. ainv. unfold Typable. exists (A ~> x). exists x0. assumption.
    - apply IHsubterm. ainv. unfold Typable. exists A. exists x0. assumption.
    - apply IHsubterm. ainv. unfold Typable. exists B. exists (A :: x0). assumption.
Qed.

Lemma mp_gen_P : forall Gamma ms x tau, ty_P Gamma (curry (!x) ms) tau ->
  exists sigmas, prod (Forall2 (ty_P Gamma) ms sigmas) (nth_error Gamma x = Some (make_arrow_type (sigmas) tau)).
Proof.
  induction ms using rev_ind.
  - intros. ainv. exists []. split.
    + constructor.
    + simpl. assumption.
  - intros. rewrite curry_tail in H. apply generation_app_P in H as [sigma [HArr Hsig]]. apply IHms in HArr as [sigmas0 [HForall HGamma]].
    exists (sigmas0 ++ [sigma]). split.
    + apply Forall2_head_to_last. constructor; assumption.
    + unfold make_arrow_type. rewrite fold_right_app.
      simpl. assumption.
Qed.

Lemma subst_var_is_var_P : forall Su a tau, ? a = tau.[Su] -> exists b, tau = ? b.
Proof.
  induction tau.
  - simpl. intros. exists x. reflexivity.
  - simpl. intros. inversion H.
Qed.

Lemma subst_arr_is_arr_or_P : forall x t Su t0, x.[Su] = t ~> t0 
    -> (exists st st0,
          x = st ~> st0 /\ st.[Su] = t /\ st0.[Su] = t0) \/
       (exists a, x = ? a).
Proof.
  intros. destruct x.
  - right. exists x. auto.
  - left. exists x1. exists x2.
    split.
    + reflexivity.
    + split; ainv.
Qed.
