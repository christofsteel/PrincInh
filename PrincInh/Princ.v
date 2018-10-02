Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Classes.EquivDec.
Require Import Autosubst.Autosubst.
Require Import Datatypes.

Require Import PrincInh.Types.
Require Import PrincInh.Utils.
Require Import PrincInh.NFTerms.
Require Import PrincInh.LongTyping.
Require Import PrincInh.SfC.
Require Import PrincInh.Paths.

Import ListNotations.
Import EqNotations.

Example id_princ : nflong_princ (? 0 ~> ? 0) (\__ (!! 0 @@ [])).
Proof.
    unfold nflong_princ.
    split.
    - constructor. econstructor.
      + instantiate (1 := []). reflexivity.
      + intros. exfalso. inversion pms.        
    - simpl. destruct rho'.
      + ainv.
      + intros. ainv.
        assert (ts = []).
        { clear X. asimpl in Lenproof. symmetry in Lenproof.
          apply length_zero_iff_nil in Lenproof. assumption. }
        subst. clear X. exists (? a .: ids). reflexivity. Unshelve. reflexivity.
Qed.

Definition norm_princ_inhab (M: nfterm) (tau: type) :=
    nflong_princ tau M.

Lemma subst_var_is_var_T : forall Su a tau, ? a = tau.[Su] -> {b | tau = ? b}.
Proof.
  intros.
  simpl in H.
  destruct tau.  
  - exists x. reflexivity.
  - simpl in H. exfalso. inv H.
Qed.

Definition star tau := forall pi, In pi (dom_P tau) -> forall x, P tau (pi ++ [Tgt]) = Some (? x) ->
                                                  R_tau_ts tau (pi ++ [Tgt]) (pi ++ [Tgt]).

(* General: Utils *)
Definition Req {T} (A B : (T -> T -> Type)) := (Rsub A B * Rsub B A)%type.

(* General: Utils *)
Lemma trans_hull_in_R {A} {eqdec : EqDec A eq} R (a b : A) : trans_hull R a b -> {c & In (a, c) R} + {c & In (c, a) R}.
Proof.
  intros.
  induction X.
  - left. eexists. exact i.
  - destruct IHX1 as [[c' Hin]|[c' Hin]].
    + left. exists c'. assumption.
    + right. exists c'. assumption.
Qed.

Lemma ts_cl_in_R {A} {eqdec : EqDec A eq} R (a b : A) : ts_cl_list R a b -> {c & In (a, c) R} + {c & In (c, a) R}.
Proof.
  intros. apply ts_cl_list_trans_sym in X. apply trans_hull_in_R in X. destruct X.
  - destruct s. unfold sym_hull_list in i. apply In_app_sumbool in i. destruct i.
    + left. eexists. apply i.
    + right. apply In_flipped in i. rewrite flipped_invol in i. eexists. apply i.
  - destruct s. unfold sym_hull_list in i. apply In_app_sumbool in i. destruct i.
    + right. eexists. apply i.
    + left. apply In_flipped in i. rewrite flipped_invol in i. eexists. apply i.
Qed.

(* General: Paths *)
Lemma R_tau_ts_in_dom_P : forall pi pi' tau, R_tau_ts tau pi pi' -> prod (In pi (dom_P tau))
                                                                   {a & P tau pi = Some (? a)}.
Proof.
  intros.
  apply ts_cl_in_R in X.
  destruct X as [[x Hin] | [x Hin]].
  - unfold R_tau_list in Hin. apply filter_In in Hin. destruct Hin. apply in_prod_iff in H.
    unfold R_tau_cond in H0. simpl in H0. apply andb_prop in H0. destruct H0.
    destruct (P tau pi); try discriminate H1. destruct t; try discriminate H1. split. ainv. exists x0. reflexivity.
  - unfold R_tau_list in Hin. apply filter_In in Hin. destruct Hin. apply in_prod_iff in H.
    unfold R_tau_cond in H0. simpl in H0. apply andb_prop in H0. destruct H0.
    destruct (P tau x); try discriminate H1. destruct t; try discriminate H1.
    destruct (P tau pi); try discriminate H1. rewrite equivb_prop in H1. subst.
    split. ainv. exists x0. reflexivity.
Qed.

Lemma replace_at_paths_split : forall pi tau1 tau2, {m1 & { m2 & replace_at_path (tau1 ~> tau2) (fresh_type (tau1 ~> tau2)) pi = m1 ~> m2}} + {pi = []} + {In pi (dom_P (tau1~>tau2))}.
Proof.
  intros.
Admitted.

(* Irgendwas mit 26
Lemma replace_all_paths_split : forall pi s tau1 tau2, {m1 & { m2 & replace_all_paths (fresh_type (tau1 ~> tau2)) (replaceable_paths (tau1 ~> tau2) (\__ s) pi) = m1 ~> m2}} + {pi = []}.
Proof.
  intros.
  destruct (pi == []).
  - right. assumption.
  - left. eexists. eexists.
    unfold replace_all_paths.
Admitted. *)

Lemma princ_nec {m tau} : nfty_long [] m tau -> nflong_princ tau m -> Req (R_m_ts m) (R_tau_ts tau).
Proof.
  intros. pose proof (Long_closed _ _ X). pose proof X as nfty_l.
  apply long_to_sfc_tau in X. apply sfc_tau_to_Rsub_m_tau in X.
  split.
  - assumption.
  - unfold Rsub. assert (forall pi pi', (R_tau_ts tau) pi pi' -> ((R_m_ts m) pi pi' -> False) -> False).
    { intros.
      remember (fresh_type tau).
      pose proof R_tau_ts_in_dom_P _ _ _ X1 as [Hin [a Heq]].
      apply P_P_ok_set in Heq as [Hpr HPok].
      pose proof long_stays_long m tau pi Hpr a nfty_l HPok as Hszw.
      ainv.
      pose proof X3 _ Hszw as [Su Heqtau].
      clear X1 H1 Hpr a nfty_l H0 X.
      admit.
    }
    (*intros.
    pose proof H1 pi pi' _ X0.
    destruct (R_m_ts_dec m pi pi').
    + ainv.
    + exfalso. eapply H1. apply f.*)
Admitted.
  
Lemma princ_suff : forall tau, star tau -> forall m, nfty_long [] m tau ->
  Req (R_m_ts m) (R_tau_ts tau) -> nflong_princ tau m.
Proof.
Admitted.
