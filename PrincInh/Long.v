Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Autosubst.Autosubst.

Require Import PrincInh.Terms.
Require Import PrincInh.TypesCommon.
Require Import PrincInh.TypesType.
Require Import PrincInh.TypesProp.
Require Import PrincInh.Utils.

Import ListNotations.
Import EqNotations.

Inductive long_ty_T (Gamma : repo) : term -> type -> Type :=
| Long_I_T s A B : long_ty_T (A :: Gamma) s B ->
        long_ty_T Gamma (Lam s) (Arr A B)
| Long_E_T x ms ts a : nth_error Gamma x = Some (make_arrow_type ts (? a)) 
        -> long_rel_T Gamma ms ts -> 
        long_ty_T Gamma (curry (! x) ms) (? a)
with 
    long_rel_T (Gamma : repo) : list term -> list type -> Type :=
    | lr_atom_T : long_rel_T Gamma [] []
    | lr_cons_T m t ms ts : long_ty_T Gamma m t -> long_rel_T Gamma ms ts -> 
            long_rel_T Gamma (m::ms) (t::ts)
.

Inductive long_ty_P (Gamma : repo) : term -> type -> Prop :=
| Long_I_P s A B : long_ty_P (A :: Gamma) s B ->
        long_ty_P Gamma (Lam s) (Arr A B)
| Long_E_P x ms ts a : nth_error Gamma x = Some (make_arrow_type ts (? a)) 
        -> long_rel_P Gamma ms ts -> 
        long_ty_P Gamma (curry (! x) ms) (? a)
with 
    long_rel_P (Gamma : repo) : list term -> list type -> Prop :=
    | lr_atom_P : long_rel_P Gamma [] []
    | lr_cons_P m t ms ts : long_ty_P Gamma m t -> long_rel_P Gamma ms ts -> 
            long_rel_P Gamma (m::ms) (t::ts)
.

Lemma Long_E_aux_T : forall Gamma x ms ts a curr v,
nth_error Gamma x = Some (make_arrow_type ts (? a)) 
        -> long_rel_T Gamma ms ts -> 
        curr = curry (! x) ms -> v = (? a) ->
        long_ty_T Gamma curr v.
Proof.
  intros. subst. econstructor; try assumption.
  - apply H.
  - assumption.
Qed.
         
Definition long_ty_T_ind' :
      forall P : repo -> term -> type -> Type,
       (forall (Gamma : repo) (s : term) (A B : type),
        long_ty_T (A :: Gamma) s B ->
        P (A :: Gamma) s B -> P Gamma (\_ s) (A ~> B)) ->
       (forall (Gamma : repo) (x : var) 
          (ms : list term) (ts : list type) (a : var),
        nth_error Gamma x = Some (make_arrow_type ts (? a)) ->
        long_rel_T Gamma ms ts -> 
        Forall2_T (P Gamma) ms ts -> 
        P Gamma (curry (! x) ms) (? a)) ->
       forall (Gamma : repo) (t : term) (t0 : type),
       long_ty_T Gamma t t0 -> P Gamma t t0 :=
       fun P icase ecase => 
       fix long_ty_ind'_rec (Gamma : repo) (t : term) (t0 : type) 
        (proof : long_ty_T Gamma t t0) {struct proof} : P Gamma t t0 :=
            match proof with
            | Long_I_T _ s A B proof' => icase Gamma s A B proof' 
                    (long_ty_ind'_rec (A :: Gamma) s B proof')
            | Long_E_T _ x ms ts a eqproof longrelproof => 
               ecase Gamma x ms ts a eqproof longrelproof
                 ((fix long_rel_ind'_rec (ms : list term) (ts : list type) 
                   (proof : long_rel_T Gamma ms ts) {struct proof} 
                     : Forall2_T (P Gamma) ms ts :=
                  match proof with
                  | lr_atom_T _ => Forall2_T_nil _
                  | lr_cons_T _ m t ms ts long_ty_proof long_rel_proof =>
                          @Forall2_T_cons _ _ _ m t ms ts (long_ty_ind'_rec Gamma m t long_ty_proof)
                            (long_rel_ind'_rec ms ts long_rel_proof)
                  end) ms ts longrelproof )
             end.

Definition long_ty_P_ind' :
      forall P : repo -> term -> type -> Prop,
       (forall (Gamma : repo) (s : term) (A B : type),
        long_ty_P (A :: Gamma) s B ->
        P (A :: Gamma) s B -> P Gamma (\_ s) (A ~> B)) ->
       (forall (Gamma : repo) (x : var) 
          (ms : list term) (ts : list type) (a : var),
        nth_error Gamma x = Some (make_arrow_type ts (? a)) ->
        long_rel_P Gamma ms ts -> 
        Forall2 (P Gamma) ms ts -> 
        P Gamma (curry (! x) ms) (? a)) ->
       forall (Gamma : repo) (t : term) (t0 : type),
       long_ty_P Gamma t t0 -> P Gamma t t0 :=
       fun P icase ecase => 
       fix long_ty_ind'_rec (Gamma : repo) (t : term) (t0 : type) 
        (proof : long_ty_P Gamma t t0) {struct proof} : P Gamma t t0 :=
            match proof with
            | Long_I_P _ s A B proof' => icase Gamma s A B proof' 
                    (long_ty_ind'_rec (A :: Gamma) s B proof')
            | Long_E_P _ x ms ts a eqproof longrelproof => 
               ecase Gamma x ms ts a eqproof longrelproof
                 ((fix long_rel_ind'_rec (ms : list term) (ts : list type) 
                   (proof : long_rel_P Gamma ms ts) {struct proof} 
                     : Forall2 (P Gamma) ms ts :=
                  match proof with
                  | lr_atom_P _ => Forall2_nil _
                  | lr_cons_P _ m t ms ts long_ty_proof long_rel_proof =>
                          @Forall2_cons _ _ _ m t ms ts (long_ty_ind'_rec Gamma m t long_ty_proof)
                            (long_rel_ind'_rec ms ts long_rel_proof)
                  end) ms ts longrelproof )
            end.


Lemma long_rel_iff_Forall2_P : forall Gamma ms ts, long_rel_P Gamma ms ts <-> Forall2 (long_ty_P Gamma) ms ts.
Proof.
  intros Gamma ms ts.
  split; induction 1; constructor; try constructor; assumption.
Qed.


Lemma Forall2_if_long_rel_T : forall Gamma ms ts, long_rel_T Gamma ms ts -> Forall2_T (long_ty_T Gamma) ms ts.
Proof.
  intros Gamma ms ts.
  induction 1; constructor; try constructor; assumption.
Qed.

Lemma long_rel_if_Forall2_T : forall Gamma ms ts,  Forall2_T (long_ty_T Gamma) ms ts -> long_rel_T Gamma ms ts.
Proof.
  intros Gamma ms ts.
  induction 1; constructor; try constructor; assumption.
Qed.

Lemma Forall2_inh {B C}: forall (A : B -> C -> Type) ms ts, Forall2 (fun a b => inhabited (A a b)) ms ts -> inhabited (Forall2_T (fun a b => A a b) ms ts).
  Proof.
    induction 1.
    - constructor. constructor.
    - ainv. constructor. constructor.
      + assumption.
      + assumption.
  Qed.


 (*
Lemma long_ty_T_P : forall Gamma m tau, long_ty_T Gamma m tau -> long_ty_P Gamma m tau.
Proof.
  induction 1 using long_ty_T_ind'.
  - constructor. assumption.
  - econstructor.
    + apply H.
    + apply long_rel_if_Forall2_T in X0.
  *)

Lemma long_ty_inh : forall Gamma m tau, long_ty_P Gamma m tau <-> inhabited (long_ty_T Gamma m tau).
Proof.
  intros.
  split.
  - revert Gamma m tau. induction 1 using long_ty_P_ind'.
    + ainv. constructor. constructor. assumption.
    + apply Forall2_inh in H1. inversion H1. constructor. econstructor.
      * apply H.
      * apply long_rel_if_Forall2_T. apply X.
  - apply inhabited_ind. revert Gamma m tau.
    fix ih 4.
    intros.
    destruct X.
    + constructor. apply ih. assumption.
    + econstructor.
      * apply e.
      * clear e. revert ms ts l. fix ih2 3. intros. destruct l.
        ** constructor.
        ** constructor.
           { apply ih. assumption. }
           { apply ih2.
             - assumption.
           }
Qed.

Lemma mkArrow_curry_ty_T : forall Gamma ms ts a ,
    Forall2_T (fun m t => ty_T Gamma m t) ms ts
    -> forall x, ty_T Gamma x (make_arrow_type ts a)
    -> ty_T Gamma (curry x ms) a.
Proof.
    induction 1.
    - intros. simpl in *. assumption.
    - intros. simpl in *. apply IHX. econstructor.
      + apply X0.
      + assumption.
Qed.

Lemma long_impl_ty_T : forall Gamma m t, long_ty_T Gamma m t -> ty_T Gamma m t.
Proof.
    intros. induction X using long_ty_T_ind'.
    - constructor. assumption.
    - eapply mkArrow_curry_ty_T.
      + apply X0.
      + constructor. assumption.
Qed.

Definition is_long_ty (t: term) (ty: type) := long_ty_P [] t ty.
Definition is_ty (t: term) (typ : type) := ty_P [] t typ.

Lemma long_ty_var_T : forall Gamma x t, nth_error Gamma x = Some (? t) -> long_ty_T Gamma (! x) (? t).
Proof.
  intros. assert (! x = curry (! x) []). { reflexivity. } rewrite H0. econstructor.
  - instantiate (1:=[]). auto.
  - constructor.
Qed.

Lemma long_rel_rev_T : forall ms ts Gamma, long_rel_T Gamma ms ts -> long_rel_T Gamma (rev ms) (rev ts).
Proof.
  intros. apply long_rel_if_Forall2_T. apply Forall2_T_is_rev. repeat rewrite rev_involutive.
  apply Forall2_if_long_rel_T. assumption.
Qed.
  
Lemma rev_long_rel_T : forall ms ts Gamma, long_rel_T Gamma (rev ms) (rev ts) ->  long_rel_T Gamma ms ts.
  intros. apply long_rel_if_Forall2_T. apply Forall2_T_is_rev_r. apply Forall2_if_long_rel_T. assumption.
Qed.

Lemma long_ty_app_T : forall Gamma n m ms t ts a x, 
  n = curry (! x) (ms) ->  
  long_ty_T Gamma m t ->
  long_rel_T Gamma ms ts ->
  nth_error Gamma x = Some (make_arrow_type ts (t ~> ? a)) 
  -> long_ty_T Gamma (n @ m) (? a).
Proof.
  intros.
  subst. rewrite <- curry_tail.  econstructor.
  - instantiate (1:=(ts ++ [t])). 
    rewrite make_arrow_type_last. assumption.
  - apply rev_long_rel_T. repeat rewrite rev_unit.
    constructor.
    + assumption.
    + apply long_rel_rev_T in X0. assumption.
Qed.

(*
Lemma long_general_abs : forall m tau Su Gamma,
  long_ty (Gamma.?[Su]) (\_ m) tau.[Su] -> ty Gamma (\_ m) tau -> long_ty Gamma (\_ m) tau.
Proof.
  Admitted.
 *)

(* Das scheint nicht gebraucht zu werden... außerdem ist das andersherum wahrscheinlich besser...
long_ty -> exists a, tau <> ? a
Lemma not_long_ty : forall Gamma tau x ms, (forall a, tau <> (? a)) -> ~ long_ty_P Gamma (curry (!x) ms) tau.
Proof.
  intros.
  intros F. inv F. inv X.
  - remember (! x) as n.
    generalize dependent n.
    induction ms using rev_ind; intros.
    + simpl in H1. subst. inversion H1.
    + rewrite curry_tail in H1. ainv. 
  - apply (H a). reflexivity.
Qed.

Lemma long_ty_app_gen_T : forall s t B Gamma, long_ty_T Gamma (s @ t) B 
  -> { x  & { ms & { A  & { a & { ts, B = (? a) /\ s = curry (! x) ms /\ Gamma x = Some (make_arrow_type ts (A ~> B))
     /\ long_rel_T Gamma ms ts.
Proof.
  intros.
  ainv. exists x. apply long_rel_rev in H1.
  destruct (rev ms) eqn:rms.
  - symmetry in rms. apply rev_nil_iff_nil in rms. ainv.
  - destruct (rev ts) eqn:rts.
    + ainv. (* symmetry in H2. apply app_eq_nil in H2. ainv. *)
    + ainv. exists (rev l). exists t1. exists a. exists (rev l0).
      split.
      { reflexivity. }
      { split.
        - symmetry in H2. apply rev_cons_iff_last in H2. ainv.
          apply curry_split in H1. ainv.
        - split.
          + symmetry in H3. apply rev_cons_iff_last in H3. rewrite H3 in H1.
            rewrite make_arrow_type_last in H1. assumption. 
          + apply long_rel_rev. repeat rewrite rev_involutive. assumption. }
Qed.
 *)

Lemma long_ty_lam_aux_T : forall m Gamma, { s & { t & long_ty_T (s :: Gamma) m t  } } ->
  { t0 & long_ty_T Gamma (\_ m) t0}.
Proof.
  intros.
  ainv. exists (x ~> x0). constructor. assumption.
Qed.

(*
Lemma mkarrow_subst_exists2 : forall ts x Su a, x.[Su] = make_arrow_type ts (? a) ->
  exists ts0 a0, (x = ? a0 /\ Su a0 = make_arrow_type ts (? a)) /\
  ts = ts0 /\ ? a = (? a0).[Su] /\ x = (make_arrow_type ts0 (? a0)).
Proof.
  induction ts.
  - intros. exists []. simpl in H. symmetry in H. inversion H. apply subst_var_is_var in H as [b H]. exists b.
    split.
    + reflexivity.
    + split; ainv.
  - intros. rewrite make_arrow_type_head in H. inversion H. apply subst_arr_is_arr_or in H as [[st [st0 [xst [xsu stmkarr]]]] | xvar].
    + apply IHts in stmkarr as [ts0 [a1 [Htsmap [Ha0var Hstarr]]]]. exists (st :: ts0). exists a1.
      split. 
      { ainv. }
      { split; ainv. }
    + exists [a]. eexists. split.
      { simpl.
    simpl.
Qed.
      rewrite make_arrow_type_head.
      split.
      { 
      reflexivity.
    + ainv. exists []. exists x0. reflexivity.
Qed.
*)
(*
Lemma repo_mkarrow_subst : forall ts Gamma Su x a, Gamma.?[Su] x = Some (make_arrow_type ts (? a)) ->
exists sa sts, make_arrow_type ts (? a) = (make_arrow_type sts (? sa)).[Su] /\ ts = map (subst Su) sts /\ (? a) = (? sa).[Su].
Proof.
  intros.
  unfold subst_option in H. destruct (Gamma x) eqn:HG.
  - inversion H. apply mkarrow_subst_exists in H1 as [ts0 [a0 H1]].
    exists a0. exists ts0. split.
    + rewrite H1. reflexivity.
    + split.
      { 
  induction ts.
  - ainv. Admitted.
*)

(*
Lemma long_ty_subst : forall m t Gamma Su, long_ty Gamma.?[Su] m t -> exists t0, long_ty Gamma m t0.
Proof.
  intros.
  remember (Gamma.?[Su]) as sGamma.
  generalize dependent Gamma.
  generalize dependent Su.
  induction H using long_ty_ind'.
  - intros. subst. apply long_ty_lam_aux. exists A. apply IHlong_ty.
    ainv.
  econstructor. constructor.
  Show Existentials.
  Grab Existantial Variables. instantiate (1:=exists). prooflater.
  - prooflater. 
  Qed.
  
  ainv. eexists. econstructor.
    + apply repo_subst_exists in H2 as [B [HB HGamma]].
      apply mkarrow_subst_exists in HB.
  revert Goal1. apply IHlong_ty.
  econstructor. constructor. 

  induction m.
  - intros. ainv. apply repo_subst_exists in H0. symmetry in H1. apply curry_if_nil in H1.  
    ainv. symmetry in H0. apply subst_var_is_var in H0. ainv. exists (? x0). econstructor. 
    + instantiate (1:=[]). simpl. apply H0.
    + constructor.
  - intros. ainv. apply repo_subst_exists in H0 as [B [Bmkat HB]]. apply mkarrow_subst_exists in Bmkat.
    ainv. assert (exists msinit mslast, ms = msinit ++ [mslast]).
    { destruct ms.
      + inv H0.
      + apply list_split_rev. exists t. exists ms. reflexivity. }
    destruct H as [msinit [mslast H]]. subst. apply curry_split in H0 as [H0 Hm2].
    subst. exists (? x1). econstructor.
    + apply H1.
    + constructor.
    inv H0.
    + inv H0.
    apply mkarrow_subst_exists in H4. ainv.  
  intros.
  remember (Gamma.?[Su]) as sGamma.
  generalize dependent Gamma.
  generalize dependent Su.
  induction H using long_ty_ind'.
  - ainv. destruct (Gamma0.?[Su] 0). 
    +
  
  apply long_ty_subst_lam_aux.
    
  induction H using long_ty_ind'.
  - inv H. ainv. apply long_ty_subst_lam_aux. exists A. apply IHlong_ty. 
      rewrite <- subst_repo_cons. ainv. prooflater.
    + 
  apply (repo_pump_subst _ _ A _) in HeqsGamma. apply IHlong_ty in HeqsGamma.
  econstructor. econstructor.
    

Lemma long_rel_subst Gamma Su ms ts: long_rel Gamma.?[Su] ms ts -> exists ts0, long_rel Gamma ms ts0.
Proof.
  remember (Gamma.?[Su]) as sGamma.
  induction 1.
  - exists []. constructor.
  - exists (
*)

Lemma long_general_T : forall m Su tau Gamma,
  ty_T Gamma m tau -> long_ty_T Gamma..[Su] m tau.[Su] -> long_ty_T Gamma m tau.
Proof.
  intros m.
  remember (term_length m) as lengthm.
  assert (term_length m <= lengthm). { firstorder. }
  clear Heqlengthm.
  revert m H.
  induction (lengthm).
  - intros. exfalso. ainv.
  - intros. destruct m. 
    + ainv. symmetry in H4. apply curry_if_nil in H4. ainv.
    apply subst_var_is_var_T in H1. ainv. apply Long_E_T with [].
      { simpl. inv H1. reflexivity. }
      { constructor. }
    + inversion X0. apply subst_var_is_var_T in H1 as [b H1]. rewrite <- H0 in X.
      apply mp_gen_T in X as [sigmas [HForall HGamma]].
      rewrite H1 in *. apply Long_E_T with sigmas.
      { assumption. }
      { assert (Forall2_T (fun t sigma => t = sigma.[Su]) ts sigmas).
        { rewrite subst_repo in H2. rewrite HGamma in H2. revert HForall H2 X1.
          clear...
          revert ts sigmas.
          induction ms.
          - intros. inv HForall. inv X1. constructor.
          - intros. inversion HForall. inversion X1. constructor.
            { ainv. }
            { ainv. apply IHms; try assumption.
              - simpl. apply f_equal. assumption. } }
        rewrite <- H0 in H.
        generalize (curry_le (! x) ms _ H).
        (* revert H1 HForall H3 IHn. clear...*)
        clear HGamma H2.
        revert X1 HForall H3 IHn.
        clear ...
        revert sigmas ts.
        induction ms.
        - ainv. constructor.
        - intros. ainv. constructor.
          + apply IHn with Su. 
            { ainv. firstorder. }
            { assumption. }
            { assumption. }
          + eapply IHms.
            { eassumption. }
            { assumption. }
            { assumption. }
            { assumption. }
            { ainv. } }
    + inversion X0. symmetry in H2. apply subst_arr_is_arr_or_T in H2 as [Harr | Hvar].
      { destruct Harr as [st [st0 [Htau [HstSu Hst0su]]]]. 
        rewrite Htau. constructor. apply IHn with Su.
        - simpl in H. firstorder.
        - inversion X. rewrite Htau in H0. ainv.
        - rewrite <- HstSu in X1. rewrite subst_repo_cons in X1. rewrite Hst0su.
          assumption.
      }
      { ainv. }
      { ainv. }
Qed.


