Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Autosubst.Autosubst.

Require Import PrincInh.TypesCommon.
Require Import PrincInh.Terms.
Require Import PrincInh.Utils.

Import ListNotations.
      
Inductive ty_T (Gamma : var -> option type) : term -> type -> Type:=
| Ty_Var x A : Gamma x = Some A ->
        ty_T Gamma (Var x) A
| Ty_Lam s A B : ty_T (Some A .: Gamma) s B ->
        ty_T Gamma (Lam s) (Arr A B)
| Ty_App s t A B : ty_T Gamma s (Arr A B) -> ty_deriv_of Gamma t A ->
                   ty_T Gamma (App s t) B.

Definition ty Gamma m tau := inhabited (ty_deriv_of Gamma m tau).

Lemma Ty_Var_lift Gamma x A : Gamma x = Some A -> ty Gamma (Var x) A.
Proof.
  intros.
  constructor.
  constructor.
  assumption.
Qed.

Lemma Ty_Lam_lift Gamma s A B : ty (Some A .: Gamma) s B ->
                                ty Gamma (Lam s) (Arr A B).
Proof.
  intros.
  revert H.
  apply inhabited_covariant.
  subst.
  apply Ty_Lam.
Qed.

Lemma Ty_App_lift Gamma s t A B : ty Gamma s (Arr A B) -> ty Gamma t A ->
                                  ty Gamma (App s t) B.
Proof.
  intros H H1.
  ainv.
  constructor.
  econstructor.
  apply X.
  assumption.
Qed.

 (*
Inductive ty_deriv_of (Gamma : var -> option type) : forall (m: term) (tau : type), ty Gamma m tau -> Type :=
| TyDeriv_Var x A proof : ty_deriv_of Gamma (Var x) A (Ty_Var Gamma x A proof).
| TyDeriv_Lam s A B proof : ty (Some A .: Gamma) s B ->
        ty Gamma (Lam s) (Arr A B)
| TyDeriv_App s t A B : ty Gamma s (Arr A B) -> ty Gamma t A ->
        ty Gamma (App s t) B.
 *)

Lemma generation_app : forall s t tau Gamma, ty Gamma (s@t) tau ->
                        exists sigma, ty Gamma s (sigma ~> tau)
                                   /\ ty Gamma t (sigma).
Proof.
  intros s t tau Gamma H.
  ainv.
  exists A.
  split; constructor; assumption.
Qed.

Lemma generation_lam : forall s A Gamma sigma tau, ty Gamma (\_ s) A ->
                        A = sigma ~> tau ->
                        ty (Some sigma .: Gamma) s tau.
Proof.
  intros.
  ainv.
  constructor. subst. assumption.
Qed.


Lemma generation_var : forall x A Gamma, ty Gamma (! x) A ->
                          Gamma x = Some A.
Proof.
  intros.
  ainv.
Qed.
  
(*
Inductive tyty :=
| TytyVar (Gamma : var -> option type) (x : var) (A : type)
| TytyLam (Gamma : var -> option type) (m : term) (A : type) (B : type) (proofm : tyty)
| TytyAbs (Gamma : var -> option type) (p : term) (q : term) (A : type) (proofp : tyty) (proofq : tyty)
.

Inductive tyty2 (Gamma : var -> option type) :=
| TytyVar2 (x : var) (A : type)
| TytyLam2 (m : term) (A : type) (B : type) (proofm : tyty2 (Some A .: Gamma))
| TytyAbs2 (p : term) (q : term) (A : type) (proofp : tyty2 Gamma) (proofq : tyty2 Gamma)
.

Fixpoint Checktyty (Gamma: var -> option type) (proof: tyty2 Gamma ) : bool :=
  match proof with
  | TytyVar2 _ x A => true
  | TytyLam2 _ m A B proofm => Checktyty Gamma proofm
  | TytyAbs2 _ p q A proofp proofq => Checktyty Gamma  proofp && Checktyty Gamma proofq
  end.

Fixpoint Checktyty (proof: tyty) : bool :=
  match proof with
  | TytyVar Gamma x A => if (Gamma x == Some A) then true else false
  | TytyLam Gamma m A B proofm => match proofm with
                                  | TytyVar Gamma2 _ _ => Gamma = Some A2 .: Gamma
      if (Checktyty proofm) && (
*)

Lemma ty_app_ex : forall Gamma (B:type) s t, ty Gamma (App s t) B -> exists A, ty Gamma t A ->
    ty Gamma s (A ~> B).
Proof.
    intros. ainv. exists A. ainv. constructor. assumption.
Qed.

Lemma ty_deriv_of_ren Gamma s A:
  ty_deriv_of Gamma s A -> forall Delta xi,
    Gamma = xi >>> Delta ->
      ty_deriv_of Delta s.[ren xi] A.
Proof.
    induction 1.   
    - constructor. subst. autosubst.
    - intros. subst. asimpl. econstructor. eapply IHX. autosubst.
    - intros. subst. asimpl. econstructor. eapply IHX1. reflexivity.
                                           eapply IHX2. reflexivity.
Qed.                                           

Lemma ty_ren Gamma s A:
  ty Gamma s A -> forall Delta xi,
    Gamma = xi >>> Delta ->
      ty Delta s.[ren xi] A.
Proof.
  intros.  
  ainv. eapply ty_deriv_of_ren in X.
  + unfold ty. constructor. apply X.
  + reflexivity.
Qed.

Lemma ty_deriv_of_subst Gamma s A:
      ty_deriv_of Gamma s A -> forall sigma Delta,
        (forall x t, Gamma x = Some t -> ty_deriv_of Delta (sigma x) (t)) ->
          ty_deriv_of Delta s.[sigma] A.
Proof.
  induction 1.
    - intros. simpl. apply X. assumption.
    - econstructor. eapply IHX. intros [|];
      asimpl; eauto using ty_deriv_of, ty_deriv_of_ren.
    - asimpl. eauto using ty_deriv_of.
Qed.
(*
Lemma ty_dec : forall m Gamma, {exists tau, ty Gamma m tau} + {forall tau, ~ty Gamma m tau}.
Proof.
  unfold ty.
  induction m.
  - intros. destruct (Gamma x) eqn:HGamma.
    + destruct (type_eq_dec t tau).
      * left. constructor. constructor. subst. assumption.
      * right. isfalse. inversion X. subst. rewrite HGamma in H0. ainv. apply n. reflexivity.
    + right. isfalse. inversion X. rewrite HGamma in H0. ainv.
  - intros. destruct IHm1 
    + destruct IHm2.
      * left.


*)

Ltac inhab_ty := inversion 1 as [HTY]; generalize dependent HTY;
                 repeat match goal with
                          [ H: _ |- _ ] => clear H

                        end;
                 repeat match goal with
                          [ H: _ |- _ ] => revert H

                        end.

Lemma ty_subst Gamma s A:
      ty Gamma s A -> forall sigma Delta,
        (forall x t, Gamma x = Some t -> ty Delta (sigma x) (t)) ->
        ty Delta s.[sigma] A.
Proof.  
  inhab_ty.
  induction 1.
  - intros. simpl. apply H. assumption.
  - intros. eapply Ty_Lam_lift. apply IHHTY.
    intros [|].
    + asimpl. intros. apply Ty_Var_lift. simpl. assumption.
    + intros. asimpl. eapply ty_ren.
      * apply H. inversion H0. reflexivity.
      * auto.
  - asimpl. eauto using Ty_App_lift.
Qed.

Lemma step_var : forall x s , ~(step (! x) s).
Proof.
  ainv.
  isfalse.
Qed.

Lemma step_lam : forall s s', step (\_ s) s' -> (forall m, s' = \_ m -> step s m).
Proof.
  intros.
  rewrite H0 in H.
  ainv.
Qed.

(* Mal gucken, ob die Lemmatas überhaupt wichtig sind...
Lemma ty_deriv_of_pres Gamma s A :
  ty_deriv_of Gamma s A -> forall s',
    step s s' ->
    ty_deriv_of Gamma s' A.
Proof.
  induction 1; intros s' H_step.
  - apply step_var in H_step. exfalso. apply H_step.
  - eapply step_lam in H_step.
    + c
    ainv. eapply ty_deriv_of_subst.
    
  asimpl. apply step_var in H_step. ainv. inversion H_step; ainv; eauto using ty.
    - eapply ty_subst.
      + eassumption.
      + intros [|]; simpl; eauto using ty.
        intros. ainv.
Qed.
  
Lemma ty_pres Gamma s A :
      ty Gamma s A -> forall s',
        step s s' ->
          ty Gamma s' A.
Proof.
    induction 1; intros s' H_step; asimpl; inversion H_step; ainv; eauto using ty.
    - eapply ty_subst.
      + eassumption.
      + intros [|]; simpl; eauto using ty.
        intros. ainv.
Qed.
*)
Definition mtTy : var -> option type := fun x => None.

Definition has_ty (m: term) (tau: type) : Prop :=
    ty mtTy m tau.

Example ident_typing : has_ty (\_ !0) (?0 ~> ?0).
Proof.
    unfold has_ty.
    constructor. constructor. constructor. reflexivity.
Qed.

Instance eq_dec_option : forall T, EqDec T eq -> EqDec (option T) eq.
Proof.
    unfold EqDec.
    intros.
    destruct x, y.
    - destruct (X t t0); dec_eq.
    - right. isfalse.
    - right. isfalse.
    - left. reflexivity.
Defined.

Lemma is_none_dec {T: Type} : forall (x: option T), {x = None} + { x <> None}.
Proof.
    intros. destruct x.
    - right. discriminate.
    - left. reflexivity.
Defined.


Definition subst_option (S : var -> type) (Gamma : var -> option type) (t : var) : option type :=
    match Gamma t with
    | None => None
    | Some z => Some (subst S z)
    end.

Definition subst_option_monad (S : var -> type) (Gamma : var -> option type) : var -> option type :=
    Gamma >=> (subst S >>> Some).

Lemma subst_option_def : subst_option = subst_option_monad.
Proof.
    unfold subst_option.
    unfold subst_option_monad.
    unfold kleisli_option. unfold funcomp. reflexivity.
Qed.

Notation "s .?[ sigma ]" := (subst_option sigma s) (at level 2, 
    sigma at level 200, left associativity, format "s .?[ sigma ]") : subst_scope.

Theorem subst_repo_some : forall (Gamma : var -> option type) (Su : var -> type) (a : var) (tau: type),
    Gamma a = Some tau ->
    Gamma.?[Su] a = Some tau.[Su].
Proof.
    intros.
    unfold subst_option.
    rewrite H. reflexivity.
Qed.

Theorem subst_repo_none : forall (Gamma : var -> option type) (Su : var -> type) (a : var),
    Gamma a = None ->
    Gamma.?[Su] a = None.
Proof.
    intros.
    unfold subst_option.
    rewrite H.
    reflexivity.
Qed.

Theorem subst_repo : forall (Gamma : var -> option type) (Su : var -> type) (a : var),
    Gamma.?[Su] a = (Gamma a)..[Su].
Proof.
    intros.
    destruct (Gamma a) eqn:G.
    - apply subst_repo_some. assumption.
    - apply subst_repo_none. assumption.
Qed.

Theorem subst_repo_cons : forall (Gamma : var -> option type) (Su : var -> type)
    (A : type),
    (Some A.[Su] .: Gamma.?[Su]) = (Some A .: Gamma).?[Su].
Proof.
    intros.
    extensionality x.
    destruct x.
    - reflexivity.
    - asimpl. unfold scons. unfold subst_option. reflexivity.
Qed.

Theorem subst_ty : forall Gamma s A, ty Gamma s A ->
    forall (Su : var -> type), ty Gamma.?[Su] s A.[Su]. 
Proof.
    intros.
    generalize dependent A.
    generalize dependent Gamma.
    induction s.
    - intros Gamma A. constructor. constructor. apply subst_repo_some. inversion H. inversion X. assumption.
    - intros Gamma A. ainv. apply Ty_App_lift with (A0.[Su]).
      + pose proof (IHs1 Gamma (A0 ~> A)). asimpl in H. apply H. constructor. assumption.
      + apply IHs2. constructor. eassumption.
    - intros Gamma A. ainv. apply Ty_Lam_lift. rewrite subst_repo_cons. eapply IHs. constructor. assumption.
Qed.

Definition Typable (t:term) := exists tau Gamma, ty Gamma t tau.

Theorem typable_subterm : forall m t, Typable t -> subterm m t -> Typable m.
Proof.
    intros.
    induction H0.
    - assumption.
    - apply IHsubterm. ainv. unfold Typable. exists (A ~> x). exists x0. constructor. assumption.
    - apply IHsubterm. ainv. unfold Typable. exists A. exists x0. constructor. assumption.
    - apply IHsubterm. ainv. unfold Typable. exists B. exists (Some A.: x0). constructor. assumption.
Qed.

Inductive subformula : type -> type -> Prop :=
| subf_refl : forall rho, subformula rho rho
| subf_arrow_l : forall rho sigma tau, subformula rho sigma -> subformula rho (sigma ~> tau)
| subf_arrow_r : forall rho sigma tau, subformula rho tau -> subformula rho (sigma ~> tau)
.

Theorem subformula_dec : forall x y, {subformula x y} + {~subformula x y}.
Proof.
    intros.
    destruct (x == y); dec_eq.
    - left. constructor.
    - generalize dependent x. induction y; intros.
      + right. isfalse.
      + destruct (x == y1); dec_eq.
        { left. constructor. constructor. }
        { destruct (IHy1 x); dec_eq.
          - assumption.
          - left. constructor. assumption.
          - destruct (x == y2); dec_eq.
            + left. constructor 3. constructor.
            + destruct (IHy2 x); dec_eq.
              { assumption. }
              { left. constructor 3. assumption. }
              { right. isfalse. } }
Defined.              


Definition single_subst (a: var) (tau: type) : var -> type :=
    fun (y: var) => if a == y then tau else ? y.

(*
Definition upd_fun {A B : Type} {eqdec : EqDec A eq} (f : A -> B) (new_a : A) (new_b : B) (a : A) : B :=
    if eqdec a new_a then new_b else f a.

Notation "f [ a => b ]" := (@upd_fun nat _ _ f a b) (at level 2).

Example updfun_ex : ((fun a : nat => 1 + a ) [7 => 9]) 7 = 9.
Proof.
    unfold upd_fun. simpl. reflexivity.
Qed.
*)
Definition rel_dom {A B} (ls : list (A * B)) : list A :=
    map fst ls.

Definition rel_codom {A B} (ls : list (A * B)) : list B :=
    map snd ls.

Definition not_subf (a : var) (tau : type) :=
    ~(subformula (? a) tau).

Theorem not_subf_dec : forall a tau,
    {~subformula (? a) tau} + {~(~subformula (? a) tau) }.
Proof.
    intros.
    destruct (subformula_dec (? a) tau).
    - right. intros F. apply F. assumption.
    - left. assumption.
Defined.

Fixpoint nth_subformula (n:nat) (rho:type) : option type :=
    match (n, rho) with
    | (0, ? x) => Some (? x)
    | (0, sigma ~> tau) => Some sigma
    | (Datatypes.S n', ? x) => None
    | (Datatypes.S n', sigma ~> tau) => nth_subformula n' tau
    end.

Definition mk_arrow_option (left : type) (right : option type) : type :=
    match right with
    | None => left
    | Some x => left ~> x
    end.

Fixpoint type_init (rho: type) : option type :=
    match rho with
    | ? x => None
    | sigma ~> tau => Some (mk_arrow_option sigma (type_init tau))
    end.

Fixpoint type_target (rho: type) : var :=
    match rho with
    | ? x => x
    | sigma ~> tau => type_target tau
    end.

Definition split_type_target (rho: type) : (option type * var) :=
    (type_init rho, type_target rho).

Example nth_subformula_ex : nth_subformula 2 (? 0 ~> (? 1 ~> (? 0 ~> ? 0)) ~> (? 2 ~> ?0) ~> ? 3) = Some (? 2 ~> ?0).
Proof. reflexivity. Qed.

Fixpoint flat_length (rho : type) : nat :=
    match rho with
    | ? x => 1
    | sigma ~> tau => Datatypes.S (flat_length tau)
    end.

Lemma fl_1_iff_var : forall rho, flat_length rho = 1 <-> exists x, rho = ? x.
Proof.
    intros.
    split.
    - intros. destruct rho.
      + exists x. reflexivity.
      + simpl in H. ainv. destruct rho2; simpl in H0; inversion H0.
    - intros. destruct H. subst. reflexivity.
Qed.


Definition make_arrow_type (ts : list type) (a : type) :=
    fold_right Arr a ts. 

Lemma mp_gen : forall Gamma ms x tau, ty Gamma (curry (!x) ms) tau ->
  exists sigmas, Forall2 (ty Gamma) ms sigmas /\ Gamma x = Some (make_arrow_type (sigmas) tau).
Proof.
  induction ms using rev_ind.
  - intros. ainv. exists []. split.
    + constructor.
    + simpl. assumption.
  - intros. rewrite curry_tail in H. apply generation_app in H as [sigma [HArr Hsig]]. apply IHms in HArr as [sigmas0 [HForall HGamma]].
    exists (sigmas0 ++ [sigma]). split.
    + apply Forall2_head_to_last. constructor; assumption.
    + unfold make_arrow_type. rewrite fold_right_app.
      simpl. assumption.
Qed.

Definition eq_ind_ty {A : Type } := 
fun (x : A) (P : A -> Type) (f : P x) (y : A) (e : x = y) =>
match e in (_ = y0) return (P y0) with
| eq_refl => f
end.

Definition list_ind_ty {A : Type} := 
fun (P : list A -> Type) (f : P []) (f0 : forall (a : A) (l : list A), P l -> P (a :: l)) =>
fix F (l : list A) : P l := match l as l0 return (P l0) with
                            | [] => f
                            | y :: l0 => f0 y l0 (F l0)
                            end.

Definition rev_list_ind_ty {A : Type} :=
fun (P : list A -> Type) (H : P [])
  (H0 : forall (a : A) (l : list A), P (rev l) -> P (rev (a :: l))) (l : list A) =>
  list_ind_ty (fun l0 : list A => P (rev l0)) H (fun (a : A) (l0 : list A) (IHl : P (rev l0)) => H0 a l0 IHl) l.

Definition rev_ind_ty {A : Type} := 
fun (P : list A -> Type) (H : P []) (H0 : forall (x : A) (l : list A), P l -> P (l ++ [x]))
  (l : list A) =>
(fun E : rev (rev l) = l =>
 eq_ind_ty (rev (rev l)) (fun l0 : list A => P l0)
   (rev_list_ind_ty P H (fun (a : A) (l0 : list A) (H1 : P (rev l0)) => H0 a (rev l0) H1) (rev l)) l E)
  (rev_involutive l).

Lemma mp_gen_t : forall Gamma ms x tau, ty_deriv_of Gamma (curry (!x) ms) tau ->
  { sigmas | Forall2 (ty Gamma) ms sigmas /\ Gamma x = Some (make_arrow_type (sigmas) tau)}.
Proof.
  induction ms using rev_ind_ty.
  - intros. ainv. 

Lemma pump_type_target : forall sigma tau, type_target tau = type_target (sigma ~> tau).
Proof.
    reflexivity.
Qed.

Lemma subst_var_is_var : forall Su a tau, ? a = tau.[Su] -> exists b, tau = ? b.
Proof.
  induction tau.
  - simpl. intros. exists x. reflexivity.
  - simpl. intros. inversion H.
Qed.

Lemma subst_make_arrow : forall Su ts x ss, ss = map (subst Su) ts -> make_arrow_type ss (x.[Su])
  = (make_arrow_type ts x).[Su].
Proof.
  induction ts.
  - intros. subst. reflexivity.
  - intros. ainv. simpl. rewrite IHts; reflexivity.
Qed.

Lemma make_arrow_type_last : forall ts t a,
  make_arrow_type (ts ++ [t]) (? a) =
    make_arrow_type (ts) (t ~> ? a).
Proof.
  unfold make_arrow_type.
  intros.
  rewrite <- (rev_involutive ts).
  rewrite <- (rev_head_last).
  rewrite fold_left_rev_right.
  simpl. 
  rewrite <- fold_left_rev_right.
  reflexivity.
Qed.

Lemma make_arrow_type_head : forall ts t a,
  make_arrow_type (t :: ts) (? a) =
    t ~> make_arrow_type ts (? a).
Proof.
  intros. reflexivity.
Qed.

Lemma repo_pump_subst : forall Gamma Gamma0 A Su, Gamma = Gamma0.?[Su] -> (Some A .: Gamma) = Some A .: Gamma0.?[Su].
Proof.
  intros.
  subst. try rewrite <- subst_repo_cons.
  reflexivity.
Qed.

Lemma repo_subst_exists : forall Gamma Su x A, (Gamma.?[Su] x = Some A) 
  -> exists B, B.[Su] = A /\ Gamma x = Some B.
Proof.
  intros. unfold subst_option in H. destruct (Gamma x).
  + inv H. exists t. auto.
  + inv H.
Qed.

Lemma subst_arr_is_arr_or : forall x t Su t0, x.[Su] = t ~> t0 
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

Lemma subst_arr : forall x y Su, x.[Su] ~> y.[Su] = (x ~> y).[Su].
Proof.
  reflexivity.
Qed.

Lemma add_arr_head : forall A B B0, B = B0 -> A ~> B = A ~> B0.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma mkarrow_subst_exists : forall ts x Su a, x.[Su] = make_arrow_type ts (? a) ->
  exists ts0 a0, x = (make_arrow_type ts0 (? a0)).
Proof.
  induction ts.
  - intros. simpl in H. symmetry in H. apply subst_var_is_var in H. exists []. ainv.
  - intros. rewrite make_arrow_type_head in H. apply subst_arr_is_arr_or in H as [[st [st0 [xst [xsu stmkarr]]]] | xvar].
    + apply IHts in stmkarr. inv stmkarr. inv H. exists (st :: x0). exists x. rewrite make_arrow_type_head.
      reflexivity.
    + ainv. exists []. exists x0. reflexivity.
Qed.


Definition not_in_codom (ls : list (var * type)) (a : var) :=
    Forall (not_subf a) (rel_codom ls).

Theorem not_in_codom_dec : forall ls x, {not_in_codom ls x} + {~not_in_codom ls x}.
Proof.
    intros.
    unfold not_in_codom.
    apply Forall_dec.
    apply not_subf_dec.
Defined.

Theorem not_in_codom_tail (ls : list (var * type)) (c : (var * type)) (a : var) :
    not_in_codom (c :: ls) a -> not_in_codom ls a.
Proof.
    ainv.
Qed.

Definition domain_codomain_free ls :=
        Forall (not_in_codom ls) (rel_dom ls).

Theorem domain_codomain_free_dec : forall ls, { domain_codomain_free ls } + { ~ domain_codomain_free ls }.
Proof.
    intros ls.
    unfold domain_codomain_free.
    apply Forall_dec.
    apply not_in_codom_dec.
Defined.

Definition unique_domain {A B} (ls : list (A * B)) :=
    NoDup (rel_dom ls).

Theorem unique_domain_dec {A B: Type} {eq_dec: EqDec A eq}: forall (ls : list (A * B)),  {unique_domain ls} + {~unique_domain ls}.
Proof.
    intros ls.
    unfold unique_domain.
    induction ls.
    - left. constructor.
    - destruct IHls.
      + destruct (in_dec eq_dec (fst a) (rel_dom ls)).
        { right. isfalse. }
        { left. unfold rel_dom. rewrite map_cons. constructor; assumption. }
      + right. isfalse.
Defined.

Definition correct_context ls := 
        unique_domain ls /\
        domain_codomain_free ls.

Theorem correct_context_dec : forall ls, {correct_context ls} + {~correct_context ls}.
Proof.
    intros.
    unfold correct_context.
    destruct (unique_domain_dec ls).
    - destruct (domain_codomain_free_dec ls).
      + left. split; assumption.
      + right. isfalse.
    - right. isfalse.
Defined.


Fixpoint wrap_lam (n : nat) (m : term) : term :=
  match n with
  | 0 => m
  | S n =>  \_ (wrap_lam n (rename (+1) m) @ !0)
  end.

Compute (wrap_lam 2 tI).

(*
Fixpoint eta_expand (arities : var -> nat ) (m : term) : term :=
  match m with
    | ! x => 
*)
(*
Fixpoint infer_type_aux (Gamma : var -> type) (firstfresh : nat) (m : term) : (list (type*type))*type :=
  match m with
  | ! x => ([], Gamma x)
  | \_ s => let (cinner, tinner) := infer_type_aux () (firstfresh) s in
*)

(*
Lemma nat_eq_eqdec : forall (x y : nat), {x = y} + {x <> y}.
Proof.
  induction x.
  - induction y.
    + left. reflexivity.
    + right. auto.
  - induction y.
    + right. auto.
    + destruct IHy.
      * subst. right. auto.
      * destruct (IHx y).
        { subst. left. auto. }
        { right. auto. }
        Qed.
*)
  
Fixpoint fv_type (tau: type) : set var :=
    match tau with
    | ? a => [a]
    | sigma ~> tau => set_union (nat_eq_eqdec) (fv_type sigma) (fv_type tau)
    end. 

Fixpoint subst_len_to_index (ls: list var) (v : var) : var :=
    match ls with
    | [] => v
    | a :: ls' => if v == a then 0 else 1 + subst_len_to_index ls' v
    end.

Definition canon_type_subst (tau : type) := subst_len_to_index (fv_type tau) >>> Atom.

Definition canon_type (tau: type) := tau.[canon_type_subst tau].

Example canon_type_ex : canon_type (? 8 ~> ? 8) = (? 0 ~> ? 0).
Proof.
    reflexivity.
Qed.

Theorem canon_type_ty : forall Gamma m tau, 
    ty Gamma m tau 
        -> ty Gamma.?[canon_type_subst tau] m tau.[canon_type_subst tau].
Proof.
    intros.
    unfold canon_type.
    apply subst_ty.
    assumption.
Qed.

Instance Ids_option {T} {ids : Ids T} : Ids (option T) := ids >>> Some.
Instance Rename_option {T} {rename : Rename T} : Rename (option T) := fun xi opterm =>
                                                                    match opterm with
                                                                    | None => None
                                                                    | Some term => Some (rename xi term)
                                                                    end.

Fixpoint app_unify (Gamma : var -> option type) (sigma : type) (tau : type) : option type :=
  Some tau.

Fixpoint infer_type (Gamma : var -> option type) (depth: nat) (m : term) : option type :=
  match m with
  | !x => Gamma x
  | \_ s => let otau := infer_type ((Some (? depth)) .: Gamma) (depth + 1) s in
            match otau with
            | Some tau => Some (? depth ~> tau)
            | None => None
            end
  | p @ q => let osigma := infer_type Gamma depth q in
             let otau_sigma := infer_type Gamma depth p in
             match (osigma, otau_sigma) with
             | (Some sigma, Some tau) => app_unify Gamma sigma tau
             | _ => None
             end
  end.

(*
Lemma infer_type_correct : forall m n rho Gamma, infer_type Gamma n m = Some rho -> ty Gamma m rho.
Proof.
induction m.
- intros.
  simpl in H.
  constructor.
 admit. (*intros. inv H.
  destruct (infer_type Gamma n m2) eqn:im2.
  + destruct (infer_type Gamma n m1) eqn:im1.
    * econstructor.*)
- ainv.  
  destruct (infer_type (Some (? n) .: Gamma) (n + 1) s) eqn:Hi.
  + inv H0.
    constructor.
    eapply IHm.
    apply Hi.    
  + ainv.
Admitted.
*)
Definition upd {A} {B} {eqdec: EqDec A _} (f : A -> B) (upda: A) (updb: B) (a : A) : B :=
  if eqdec upda a then
    updb
  else
    f a.

Fixpoint unify_ (types: nat) (rho1 : type) (rho2 : type)  : option (var -> type) :=
    match types with
    | 0 => None
    | S n =>
      match (rho1, rho2) with
      | (? a, _) => if subformula_dec (? a) rho2 then 
                  if (? a) == rho2 then
                    Some ids
                  else
                    None
               else
                 Some (single_subst a rho2)
      | (_, ? a) => if subformula_dec (? a) rho1 then 
                  if (? a) == rho1 then
                    Some ids
                  else
                    None
               else
                 Some (single_subst a rho1)
      | (sigma1 ~> sigma2, tau1 ~> tau2) => let oSu := unify_ n sigma2 tau2 in
                                          match oSu with
                                          | None => None
                                          | Some Su => 
                                              unify_ n sigma1.[Su] tau1.[Su] >>= 
                                                fun Sbst => Some (Su >> Sbst)
                                          end
      end
    end.

Fixpoint depth_ty rho := match rho with
| ? n => 1
| sigma ~> tau => 1 + max (depth_ty sigma) (depth_ty tau)
end.
  
Definition unify rho1 rho2 := unify_ 
  ((length (fv_type (rho1 ~> rho2))) * (depth_ty (rho1~>rho2))) rho1 rho2.

Definition mgu rho1 rho2 := unify rho1 rho2 >>=
                                  fun Su => Some rho1.[Su].

(*
Fixpoint get_ty (Gamma : var -> option type) (m : term) : option type :=
  match m with
  | ! x => Gamma x
  | \_ s => get_ty Gamma s >>= fun tau := 


.

Compute (length (fv_type (? S 0 ~> ? S 0)) * depth_ty (? S 0 ~> ? S 0)).
*)
Lemma nat_refl: forall x, (PeanoNat.Nat.eq_dec x x = left eq_refl).
Proof.
  intros.
  induction x.
  - reflexivity.
  - simpl. rewrite IHx. reflexivity.
Defined.

Lemma term_refl: forall x, eq_dec_term x x = left eq_refl.
Proof.
  induction x.
  - simpl. rewrite nat_refl. reflexivity.
  - simpl. rewrite IHx1. rewrite IHx2. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Defined.    
    
Lemma type_refl: forall t, eq_dec_type t t = left eq_refl.
Proof.
  induction t.
  - simpl. rewrite nat_refl. reflexivity.
  - simpl. rewrite IHt1. rewrite IHt2. reflexivity.
Defined.
(*
Lemma mgu_refl : forall rho, mgu rho rho = Some rho.
Proof.
  intros.
  induction rho.
  + unfold mgu. unfold unify. simpl. rewrite nat_refl. simpl. unfold subformula_dec.
    unfold equiv_dec. rewrite type_refl. simpl. unfold ids. unfold Ids_type. reflexivity.
  + unfold mgu. simpl. unfold unify. simpl.


    unfold nat_eq_eqdec. c. rewrite eqdec_refl. apply nat_eq_eqdec. }
    ainv
    + unfold mgu. unfold unify. simpl. compute. 
  unfold mgu.
*)

Lemma notU : (if subformula_dec (? 0) (? 0 ~> ? 0) then true else false) = true.
Proof.
    reflexivity.
Qed.

(*
Fixpoint get_type (Gamma : var -> option type) (m : term) : option type :=
    match m with
    | ! x => Gamma x
    | p @ q => match get_type p with
               | None => None
               | Some rho => 
                   get_type q >>= fun rho2 => get_type q >>= fun rho1 =>
                     match rho1 with
                     | ? n => None
                     | sigma ~> tau => uni
                   match get_type q with
                    | None => None
                    | Some sigma => match get_ty

Theorem typ_dec : forall m Gamma, { tau | , ty Gamma m tau).


Theorem ty_not_app : forall tau Gamma m n, (forall t, ty Gamma n t -> ~(ty Gamma m (t ~> tau))) -> ~(ty Gamma (m@n) tau).
Proof.
    intros. intros F. inversion F. subst. apply (H A); assumption.
Qed.

Theorem app_dec : forall Gamma tau m n, is_dec (forall t, ty Gamma m t /\ ty Gamma n (t~> tau)).
Proof.
    intros. unfold is_dec.  Abort.

Theorem typable_dec : forall m, Typable m -> forall Gamma, is_dec ( exists tau, ty Gamma m tau).
Proof.
    intros m Tm1 Gamma.
    unfold is_dec.
    induction m.
    - destruct (Gamma x) eqn:HG.
      + left. exists t. constructor. assumption.
      + right. isfalse. inversion H. subst. rewrite HG in H1. ainv.
    - assert (Typable (m1 @ m2)) as Tm2. assumption. 
      apply (typable_subterm m1) in Tm1. apply (typable_subterm m2) in Tm2.
      + apply IHm1 in Tm1. apply IHm2 in Tm2.
        destruct Tm1.
        { destruct Tm2.
          - Check Typable. left. 
          Abort.
      *)
    
(*
Theorem ty_dec : forall Gamma m tau, Typable m -> {ty Gamma m tau} + {~(ty Gamma m tau)}.
Proof.

    
    intros.
    generalize dependent tau.
    induction m; intros tau.
    - remember (Gamma x) as ty_x. destruct ty_x.
      + destruct (type_eq_dec t tau).
        { left. constructor. ainv. }
        { right. isfalse. ainv. rewrite H3 in H0. ainv. contradiction. }
      + right. isfalse. rewrite H1 in Heqty_x. ainv.
    - assert (Typable m1 /\ Typable m2). 
      { split; eapply typable_subterm; try apply H.
        - repeat constructor.
        - constructor 3. constructor. }
      destruct H0 as [Tym1 Tym2]. eapply IHm1 in Tym1.
      eapply IHm2 in Tym2.
      destruct Tym1; destruct Tym2.
      
      unfold Typable in Tym1.

      destruct IHm1 with (sigma ~> tau); try assumption.
      +  Abort.
      *)
      (*
      unfold Typable in Tym2. eapply IHm1 in Tym1. destruct Tym1.
      + left. 


*)
(*
      eapply IHm2 in Tym2.
      destruct Tym2.
      + eapply IHm1 in Tym1. destruct Tym1.
        { left. eapply Ty_App.
          - apply t0.
          - apply t. }
        { 0
      left. eapply Ty_App with sigma.
        { apply t0. }
        { apply t. }
      +  right. eapply ty_not_app.
      induction (?A). intros F. inversion F. ainv. contradiction.
*)
(*
Theorem ty_dec : forall m Gamma tau, {ty Gamma m tau} + {~(ty Gamma m tau)}.
Proof.
  induction m.
    - intros. remember (Gamma x) as sigma. induction (sigma).
      + destruct (type_eq_dec a tau).
        { left. constructor. ainv. }
        { right. intros F. ainv. rewrite H0 in H2. ainv. apply n. reflexivity. }
      + right. intros F. ainv. rewrite H0 in H2. ainv.
    - intros. 
      
    (*
      destruct IHm2.
      pose proof (IHm2 sigma) as Hm2. pose proof (IHm1 (sigma ~> tau)) as Hm1.
      destruct Hm2 ; destruct Hm1.
      + left. apply Ty_App with sigma; assumption.
      + 
      right. intros F. ainv. generalize dependent sigma. intros.
        assert (t = A).
        { generalize dependent A. generalize dependent t. intuition.*)
Abort.
*)