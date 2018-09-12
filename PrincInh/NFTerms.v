Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Autosubst.Autosubst.

Require Import PrincInh.Utils.
Require Import PrincInh.Terms.
Require Import PrincInh.TypesCommon.
Require Import PrincInh.TypesType.

Import ListNotations.
Import EqNotations.

Inductive nfterm :=
| NFcurr (ms: list nfterm) (x : var)
| NFLam (s: {bind nfterm})
.

Instance Ids_term : Ids nfterm := fun var => NFcurr [] var.
Instance Rename_term : Rename nfterm :=
  fun ren =>
    fix dummy m := match m as n return (annot nfterm n) with
                   | NFcurr ms x => NFcurr (mmap dummy ms) (ren x)
                   | NFLam s => NFLam (dummy s)
                   end.



Definition nfterm_ind' : forall P : nfterm -> Prop,
       (forall (ms : list nfterm) (x : var), (Forall P ms) -> P (NFcurr ms x)) ->
       (forall s : {bind nfterm}, P s -> P (NFLam s)) -> forall n : nfterm, P n :=
fun (P : nfterm -> Prop) f
  (f0 : forall s : {bind nfterm}, P s -> P (NFLam s)) =>
fix F (n : nfterm) : P n :=
  match n as n0 return (P n0) with
  | NFcurr ms x => f ms x ((fix ms_rec ms : Forall P ms
                           := match ms with
                              | [] => Forall_nil _
                              | x :: xs => @Forall_cons _ _ x xs (F x) (ms_rec xs)
                              end
                          ) ms)
  | NFLam s => f0 s (F s)
  end.

Definition nfterm_rect'
     : forall P : nfterm -> Type,
       (forall (ms : list nfterm) (x : var) (p: forall n (lp : n < length ms), P (nth_ok ms n lp)), P (NFcurr ms x)) ->
       (forall s : {bind nfterm}, P s -> P (NFLam s)) -> forall n : nfterm, P n.
Proof.
  intros.
  revert n.
  fix F 1.
  destruct n.
  - apply X. revert ms. fix ih 1. destruct ms.
    + intros. exfalso. inversion lp.
    + destruct n0.
      * intros. simpl. apply F.
      * simpl. intros. apply ih.
  - apply X0. apply F.
Qed.

Notation "'!!' x '@@' ms" := (NFcurr ms x) (at level 31, left associativity).
Notation "'\__' s" := (NFLam s) (at level 35, right associativity).

Compute (rename S (\__ !! 0 @@[])).
(* Instance Subst_term : Subst nfterm := fun sigma =>
fix dummy (s : nfterm) {struct s} : nfterm :=
  match s as n return (annot nfterm n) with
  | !! x @@ _ => match sigma x with
                | 
                
  | \__ s0 => \__ (dummy s0)
  end.
derive. Defined.
  *)

Inductive subterm_nf : nfterm -> nfterm -> Type :=
| sub_ref : forall m, subterm_nf m m
| sub_lam m1 m2 : subterm_nf m1 m2 -> subterm_nf m1 (\__ m2)
| sub_app m1 m2 ms x : subterm_nf m1 m2 -> In m2 ms -> subterm_nf m1 (!! x @@ ms). 


Definition eqdec_nfterm_fix (m1 m2 : nfterm) : {m1 = m2} + {m1 <> m2}.  
  revert m1 m2. fix ih 1. intros. destruct m1; destruct m2.
  - destruct (x == x0).
    + destruct (@list_eqdec _ _ ih ms ms0).
      * left. ainv.
      * right. intros F. ainv. apply c. reflexivity.
    + right. intros F. ainv. apply c. reflexivity.
  - right. intros F. discriminate F.
  - right. intros F. discriminate F.
  - destruct (ih s s0).
    + left. ainv.
    + right. intros F. ainv. apply n. reflexivity.
Defined.      
  
Instance eqdec_nfterm : EqDec nfterm eq. unfold EqDec. apply eqdec_nfterm_fix. Defined.

Inductive nfty (Gamma : repo) : nfterm -> type -> Type :=
| NFTy_lam s sigma tau : nfty (sigma :: Gamma) s tau -> nfty Gamma (\__ s) (sigma ~> tau)
| NFTy_var x tau ts ms : nth_error Gamma x = Some (make_arrow_type ts tau) ->             
                         length ms = length ts ->
                         (forall n (pms : n < length ms) (pts : n < length ts),
                             nfty Gamma (nth_ok ms n pms) (nth_ok ts n pts)) ->
             nfty Gamma (!!x @@ ms) tau
.

Inductive nfty_long (Gamma : repo) : nfterm -> type -> Type :=
| NFTy_lam_long s sigma tau : nfty_long (sigma :: Gamma) s tau -> nfty_long Gamma (\__ s) (sigma ~> tau)
| NFTy_var_long : forall x a ts ms (Gammaok : nth_error Gamma x = Some (make_arrow_type ts (? a)))
                    (Lenproof : length ms = length ts),
    (forall n (pms : n < length ms),
        nfty_long Gamma (nth_ok ms n pms) (nth_ok ts n (rew Lenproof in pms))) ->
    nfty_long Gamma (!!x @@ ms) (? a)
.

Inductive nfty_long_subj : forall Gamma Gamma' m m' rho rho', nfty_long Gamma m rho -> nfty_long Gamma' m' rho' -> Type :=
| nfty_long_refl : forall Gamma m rho (proof: nfty_long Gamma m rho), nfty_long_subj _ _ _ _ _ _ proof proof
| nfty_long_trans : forall Gamma Gamma' Gamma'' m m' m'' rho rho' rho''
                      (proof1 : nfty_long Gamma m rho)
                      (proof2 : nfty_long Gamma' m' rho')
                      (proof3 : nfty_long Gamma'' m'' rho''),
    nfty_long_subj _ _ _ _ _ _ proof1 proof2 ->
    nfty_long_subj _ _ _ _ _ _ proof2 proof3 ->
    nfty_long_subj _ _ _ _ _ _ proof1 proof3
| nfty_long_subj_I : forall Gamma sigma tau s (proof : nfty_long (sigma :: Gamma) s tau),
    nfty_long_subj _ _ _ _ _ _ proof (NFTy_lam_long _ _ _ _ proof)
| nfty_long_subj_E : forall Gamma x ts ms a
                       (Gammaok : nth_error Gamma x = Some (make_arrow_type ts (? a)))
                       (Lenproof : length ms = length ts)
                       (proofs : (forall n (pms : n < length ms),
                                     nfty_long Gamma (nth_ok ms n pms) (nth_ok ts n (rew Lenproof in pms))))
                       n (len: n < length ms),   
    nfty_long_subj _ _ _ _ _ _ (proofs n len) (NFTy_var_long _ _ _ _ _ Gammaok Lenproof proofs).

(*
Lemma nfty_long_inv_lam : forall s Gamma sigma tau (proof1 : nfty_long (sigma :: Gamma) s tau)
                            (proof2 : nfty_long Gamma (\__ s) (sigma ~> tau)),
    proof2 = NFTy_lam_long _ _ _ _ proof1.
Proof.
  intros. inversion proof2.

Lemma nfty_long_proof_eq : forall Gamma m rho (proof1 : nfty_long Gamma m rho) (proof2 : nfty_long Gamma m rho), proof1 = proof2.
Proof.
  induction proof1.
  - intros. inv proof2. ainv.
 *)

Lemma nfty_long_subterm : forall n m, subterm_nf n m -> forall tau Gamma, nfty_long Gamma m tau -> {Gamma' & {tau' & nfty_long Gamma' n tau'}}.
Proof.
  induction 1; intros.
  - exists Gamma. exists tau. assumption.
  - inv X0. eapply IHX. exact X1.
  - inv X0. apply In_nth_error_set in i. destruct i as [n H].
    apply nth_error_nth_ok in H. destruct H as [lp H]. pose proof (X1 n lp). eapply IHX. rewrite H in X0. exact X0.
Qed.

(*
Inductive nfty_sfc (Gamma : repo) : nfterm -> type -> Type :=
| NFTy_var_sfc x tau ts ms : nth_error Gamma x = Some (make_arrow_type ts tau) ->             
                         (forall n (pms : n < length ms) (pts : n < length ts),
                             nfty_sfc Gamma (nth_ok ms n pms) (nth_ok ts n pts)) ->
             nfty_sfc Gamma (!!x @@ ms) tau
| NFTy_lam_sfc s sigma tau : nfty_sfc (sigma :: Gamma) s tau -> nfty_sfc Gamma (\__ s) (sigma ~> tau)
.
*)



                                   

Fixpoint NFterm_term nft : term :=
  match nft with
  | !! x @@ ms => curry (! x) (map NFterm_term ms)
  | \__ s => \_ NFterm_term s
  end.

Fixpoint term_NFterm t : option nfterm :=
  match t with
  | ! x => Some (!! x @@ [])
  | \_ s => match term_NFterm s with
           | None => None
           | Some s' => Some (\__ s')
           end
  | p @ q => match term_NFterm p with
            | None => None
            | Some (!! x @@ ms) => match term_NFterm q with
                                  | None => None
                                  | Some q' => Some (!! x @@ (ms ++ [q']))
                                  end
            | Some (\__ s) => None
            end
  end.

Lemma NFterm_term_inv1 : forall t, term_NFterm (NFterm_term t) = Some t.
Proof.
  intros.
  induction t using nfterm_ind'.
  - induction ms using rev_ind.
    + reflexivity.
    + rewrite Forall_forall in IHms.
      rewrite Forall_forall in H.
      simpl. rewrite map_app. simpl. rewrite curry_tail.
      simpl. simpl in IHms. rewrite IHms.
      * erewrite H.
        ** reflexivity. 
        ** apply in_or_app. right. constructor. reflexivity.
      * intros. apply H. apply in_or_app. left. assumption.
  - simpl. rewrite IHt. reflexivity.
Qed.

Lemma NF_if_no_redex_all : forall t, (forall m n, ~subterm ((\_m) @ n) t) -> NF t.
Proof.
  induction t; intros.
  - unfold NF. intros. isfalse.
  - unfold NF. intros t F. inversion F.
    + eapply H. instantiate (1:=t2). instantiate (1:=s1). subst. constructor.
    + subst. eapply IHt1.
      * intros. intros Fsub. eapply H. constructor. exact Fsub. Unshelve. apply s2.
      * assumption.
    + subst. eapply IHt2.
      * intros. intros Fsub. eapply H. constructor 3. exact Fsub. Unshelve. apply t3.
      * assumption.
  - unfold NF. intros t F. inv F. eapply IHt.
    + intros m n Fsub. eapply H. constructor. exact Fsub.
    + exact H1.
Qed.

Lemma no_redex_if_NF_all : forall t, NF t -> forall m n, ~subterm ((\_m) @ n) t.
Proof.
  intros.
  - induction t.
    + intros. intros F. inversion F.
    + intros. intros F. inv F.
      * unfold NF in H. pose proof (H m.[t2/]).
        apply H0. constructor. reflexivity.
      * revert H2. apply IHt1. unfold NF.
        intros. unfold NF in H. pose proof (H (t' @ t2)). intros Fstep.
        apply H0. constructor. assumption.
      * revert H2. apply IHt2. unfold NF.
        intros. unfold NF in H. pose proof (H (t1 @ t')). intros Fstep.
        apply H0. constructor. assumption.
    + intros. unfold NF in H. intros F. eapply IHt.
      * unfold NF. intros. pose proof (H (\_ t')). intros Fstep. apply H0. constructor. assumption.
      * inversion F. assumption.
Qed. 

Lemma NF_iff_no_redex: forall t, NF t <-> forall m n, ~subterm ((\_m) @ n) t.
Proof.
  split.
  - apply no_redex_if_NF_all.
  - apply NF_if_no_redex_all.
Qed.

Lemma NFterm t : NF t -> { t' & term_NFterm t = Some t'}.
Proof.
  intros.
  rewrite NF_iff_no_redex in H.
  induction t.
  - simpl. intros. eexists. reflexivity.
  - simpl. assert (forall (m : {bind term}) (n : term), ~ subterm ((\_ m) @ n) t1).
    {
      intros m n F. eapply H. constructor. exact F.
    }
    apply IHt1 in H0. destruct H0. rewrite e. destruct x.
    + assert (forall (m : {bind term}) (n : term), ~ subterm ((\_ m) @ n) t2).
      {
        intros m n F. eapply H. constructor 3. exact F.
      }
      apply IHt2 in H0 as [t H1]. rewrite H1. exists (!! x @@ (ms ++ [t])).
      reflexivity.
    + exfalso. assert (exists s, t1 = \_ s).
      {
        destruct t1.
        + ainv.
        + ainv. destruct (term_NFterm t1_1); try discriminate H2.
                destruct n; try discriminate H2.
                destruct (term_NFterm t1_2); try discriminate H2.
        + exists s0. reflexivity.
      }
      destruct H0.
      eapply H. instantiate (1 :=t2). instantiate (1 := x). subst. constructor.
  - simpl. assert (forall (m : {bind term}) (n : term), ~ subterm ((\_ m) @ n) (s)).
    {
      intros m n F. eapply H. constructor. exact F.
    }
    apply IHt in H0. destruct H0. rewrite e. exists (\__ x). reflexivity.
Defined.

Lemma NF_lam : forall s, NF (\_ s) -> NF s.
Proof.
  intros.
  unfold NF in *.
  intros t' F.
  eapply H.
  constructor.
  exact F.
Qed.

Lemma NF_is_no_redex : forall s q, ~(NF ((\_s) @ q)).
Proof.
  intros.
  rewrite NF_iff_no_redex. simpl.
  intros F.
  apply (F s q).
  constructor.
Qed.

Fixpoint max_fvar (m: nfterm) : var :=
  match m with
  | !! x @@ ms => fold_left Nat.max (map max_fvar ms) (S x)
  | \__ s => pred (max_fvar s)
  end.

Compute (max_fvar (\__ (!!0 @@ [!!0 @@ []]))).

Definition all_var_in_repo {A} m (Delta : list A) := max_fvar m < S (length Delta).


(*
Lemma NF_app1 : forall p q, NF (p @ q) -> NF p.
Admitted.
Lemma NF_app2 : forall p q, NF (p @ q) -> NF q.
Admitted.
*)

Fixpoint term_NFterm_proof (t: term) : NF t -> nfterm.
(*  match t with
  | ! x => fun _ => !! x @@ []
  | \_ s => fun proof => \__ term_NFterm_proof s (NF_lam _ proof)
  | p @ q => (fix inner p q :=
    match p with
    | \_ s => fun proof => False_rect _ (NF_is_no_redex s _ proof)
    | ! x => fun proof => !! x @@ [term_NFterm_proof q (NF_app2 _ _ proof)]
    | p' @ q' => fun proof => inner p' q' (NF_app1 _ _ proof)
    end) p q
  end.

      

             ]
    
    
    match p with
            | \_ s => fun proof => False_rect _ (NF_is_no_redex s _ proof)
            | ! x => fun proof => !! x @@ [term_NFterm_proof q (NF_app2 _ _ proof)]
            | p' @ q' => fun proof => 
            end              
  end.

    fun proof => match term_NFterm_proof p (NF_app1 _ _  proof) with
            | \__ s => fun proof' => False_rect _ (NF_is_no_redex p q proof)
            | !! x @@ ms => fun _ => !! x @@ (ms ++ [term_NFterm_proof q (NF_app2 _ _ proof)])
            end proof
  end.

            
            

    match p with
            | \_ s => fun proof => False_rect _ (NF_is_no_redex s _ proof)
            | ! x => fun proof => !! x @@ [term_NFterm_proof q (NF_app2 _ _ proof)]
            | p' @ q' => fun proof => 
            end              
  end.


              match (term_NFterm_proof p (NF_app1 p q proof)) with
                      | \__ s => False_rect _ (NF_is_no_redex p q _)
                      | !! x @@ ms => !! x @@ (ms ++ [term_NFterm_proof q (NF_app2 _ _ proof)]) 
                      end
  end.


  | (! x) @ q => fun proof => !! x @@ 
  | (p' @ q') @ q => fun _ => match term_NFterm_proof (p' @ q') (NF_app1 _) with
                  | !! x @@ ms => !! x @@ (ms ++ [q])
                  |

  end
.


           ]



*)
Proof.
  intros proof.
  apply NFterm in proof.
  destruct proof.
  apply x.
Defined.
(*
Print term_NFterm_proof.
  
Lemma NFterm_term_inv2 : forall t (proof : NF t), NFterm_term (term_NFterm_proof t proof) = t.
Proof.
  intros.
  induction t.
  - reflexivity.
  - pose proof (IHt1 (NF_app1 _ _ proof)).
    pose proof (IHt2 (NF_app2 _ _ proof)).
    simpl.
    unfold term_NFterm_proof. unfold NFterm. unfold term_rect. simpl. unfold eq_rect_r. unfold eq_rect. 
    destruct (eq_sym eq_refl).
*)
