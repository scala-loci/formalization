Require Import ReTierSyntax.
Require Import ReTierStaticSemantics.
Require Import ReTierDynamicSemantics.
Require Import ReTierProofContext.


Lemma substitution_t_gamma:
  forall typing ties Psi Delta Gamma P x t T v U,
  Context typing ties Psi Delta (idUpdate x U Gamma) P |- t \in T ->
  Context typing ties Psi emptyPlaceEnv emptyVarEnv P |- v \in U ->
  Context typing ties Psi Delta Gamma P |- [x :=_t v] t \in T.
Proof.
intros until U.
intros H_typing_t H_typing_v.
generalize dependent Gamma.
generalize dependent T.
induction t; (intros; inversion H_typing_t; subst; simpl).
- case_eq (beq_id x i); intros H_eq_x.
  + apply T_Abs.
    apply beq_id_eq in H_eq_x.
    subst.
    eapply context_invariance_t; try eassumption.
    intros.
    split; try reflexivity.
    unfold idUpdate, Maps.p_update, Maps.t_update.
    case (beq_id x i); reflexivity.
  + apply T_Abs, IHt.
    eapply context_invariance_t; try eassumption.
    intros.
    split; try reflexivity.
    unfold idUpdate, Maps.p_update, Maps.t_update.
    case_eq (beq_id x0 i); try reflexivity.
    intros H_eq_x0.
    apply beq_id_eq in H_eq_x0.
    subst.
    rewrite beq_id_comm in H_eq_x.
    rewrite H_eq_x.
    reflexivity.
- eapply T_App.
  + apply IHt1. apply H2.
  + apply IHt2. apply H4.
- case_eq (beq_id x i); intros H_eq.
  + rewrite beq_id_eq in H_eq.
    subst.
    simpl in H1.
    unfold idUpdate, Maps.p_update, Maps.t_update in H1.
    rewrite beq_id_refl in H1.
    destruct H1.
    * inversion H.
      subst.
      eapply typable_empty_closed_t in H_typing_v as H_closed.
      eapply context_invariance_t; try eassumption.
      intros.
      unfold closed_t in H_closed.
      specialize H_closed with x.
      contradiction.
    * destruct H.
      congruence.
  + apply T_Var.
    simpl.
    assert (Gamma i = idUpdate x U Gamma i).
    * unfold idUpdate, Maps.p_update, Maps.t_update.
      rewrite beq_id_comm in H_eq.
      rewrite H_eq.
      reflexivity.
    * rewrite H.
      assumption.
- apply T_Unit.
- apply T_None.
- apply T_Some, IHt. assumption.
- apply T_Nil.
- eapply T_Cons.
  + apply IHt1. assumption.
  + apply IHt2. assumption.
- eapply T_AsLocal.
  + reflexivity.
  + apply IHt. assumption.
  + assumption.
  + assumption.
- eapply T_AsLocalFrom.
  + reflexivity.
  + apply IHt1. assumption.
  + assumption.
  + apply IHt2. assumption.
- case_eq (beq_id x i); intros H_eq_x.
  + eapply T_Comp; try reflexivity || assumption.
    * apply IHt1. eassumption.
    * apply beq_id_eq in H_eq_x.
      subst.
      eapply context_invariance_t; try eassumption.
      intros.
      split; try reflexivity.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      case (beq_id x i); reflexivity.
  + eapply T_Comp; try reflexivity || assumption.
    * apply IHt1. eassumption.
    * apply IHt2.
      eapply context_invariance_t; try eassumption.
      intros.
      split; try reflexivity.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      case_eq (beq_id x0 i); try reflexivity.
      intros H_eq_x0.
      apply beq_id_eq in H_eq_x0.
      subst.
      rewrite beq_id_comm in H_eq_x.
      rewrite H_eq_x.
      reflexivity.
- case_eq (beq_id x i); intros H_eq_x.
  + eapply T_ComFrom; try reflexivity || assumption.
    * apply IHt1. eassumption.
    * apply beq_id_eq in H_eq_x.
      subst.
      eapply context_invariance_t; try eassumption.
      intros.
      split; try reflexivity.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      case (beq_id x i); reflexivity.
    * apply IHt3. assumption.
  + eapply T_ComFrom; try reflexivity || assumption.
    * apply IHt1. eassumption.
    * apply IHt2.
      eapply context_invariance_t; try eassumption.
      intros.
      split; try reflexivity.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      case_eq (beq_id x0 i); try reflexivity.
      intros H_eq_x0.
      apply beq_id_eq in H_eq_x0.
      subst.
      rewrite beq_id_comm in H_eq_x.
      rewrite H_eq_x.
      reflexivity.
    * apply IHt3. assumption.
- apply T_Signal, IHt. assumption.
- apply T_ReactiveVar, IHt. assumption.
- eapply T_Now.
  + apply IHt. eassumption.
  + assumption.
- eapply T_Set.
  + apply IHt1. eassumption.
  + apply IHt2. eassumption.
- apply T_Peer. assumption.
- apply T_Reactive. assumption.
- apply T_Nat.
Qed.


Lemma substitution_t_delta:
  forall typing ties Psi Delta Gamma P P' x t T v U,
  Gamma x = None ->
  Context typing ties Psi (idUpdate x (U on P') Delta) Gamma P |- t \in T ->
  Context typing ties Psi emptyPlaceEnv emptyVarEnv P' |- v \in U ->
  Context typing ties Psi Delta Gamma P |- [x :=_t v] t \in T.
Proof.
intros until U.
intros H_Gamma H_typing_t H_typing_v.
generalize dependent Gamma.
generalize dependent T.
induction t; (intros; inversion H_typing_t; subst; simpl).
- case_eq (beq_id x i); intros H_eq.
  + apply T_Abs.
    apply beq_id_eq in H_eq.
    subst.
    eapply context_invariance_t; try eassumption.
    intros.
    split; try reflexivity.
    unfold idUpdate, Maps.p_update, Maps.t_update.
    case (beq_id x i); try reflexivity.
    congruence.
  + apply T_Abs, IHt.
    * unfold idUpdate, Maps.p_update, Maps.t_update.
      rewrite H_eq.
      assumption.
    * eapply context_invariance_t; try eassumption.
      intros.
      split; try reflexivity.
- eapply T_App.
  + apply IHt1; eassumption.
  + apply IHt2; eassumption.
- case_eq (beq_id x i); intros H_eq.
  + rewrite beq_id_eq in H_eq.
    subst.
    simpl in H1.
    unfold idUpdate, Maps.p_update, Maps.t_update in H1.
    rewrite beq_id_refl in H1.
    destruct H1; try congruence.
    destruct H.
    inversion H0.
    subst.
    eapply typable_empty_closed_t in H_typing_v as H_closed.
    eapply context_invariance_t; try eassumption.
    intros.
    unfold closed_t in H_closed.
    specialize H_closed with x.
    contradiction.
  + apply T_Var.
    simpl.
    simpl in H1.
    destruct H1.
    * left. assumption.
    * right.
      destruct H.
      split; try assumption.
      rewrite <- H0.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      rewrite beq_id_comm in H_eq.
      rewrite H_eq.
      reflexivity.
- apply T_Unit.
- apply T_None.
- apply T_Some, IHt; assumption.
- apply T_Nil.
- eapply T_Cons.
  + apply IHt1; assumption.
  + apply IHt2; assumption.
- eapply T_AsLocal; try reflexivity || assumption.
  apply IHt; assumption.
- eapply T_AsLocalFrom; try reflexivity || assumption.
  + apply IHt1; assumption.
  + apply IHt2; assumption.
- case_eq (beq_id x i); intros H_eq.
  + eapply T_Comp; try reflexivity || assumption.
    * apply IHt1; eassumption.
    * apply beq_id_eq in H_eq.
      subst.
      eapply context_invariance_t; try eassumption.
      intros.
      split; try reflexivity.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      case (beq_id x i); congruence.
  + eapply T_Comp; try reflexivity || assumption.
    * apply IHt1; eassumption.
    * apply IHt2; try assumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      rewrite H_eq.
      assumption.
- case_eq (beq_id x i); intros H_eq.
  + eapply T_ComFrom; try reflexivity || assumption.
    * apply IHt1; eassumption.
    * apply beq_id_eq in H_eq.
      subst.
      eapply context_invariance_t; try eassumption.
      intros.
      split; try reflexivity.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      case (beq_id x i); congruence.
    * apply IHt3; assumption.
  + eapply T_ComFrom; try reflexivity || assumption.
    * apply IHt1; eassumption.
    * apply IHt2; try assumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      rewrite H_eq.
      assumption.
    * apply IHt3; assumption.
- apply T_Signal, IHt; assumption.
- apply T_ReactiveVar, IHt; assumption.
- eapply T_Now; try eassumption.
  apply IHt; assumption.
- eapply T_Set.
  + apply IHt1; eassumption.
  + apply IHt2; eassumption.
- apply T_Peer. assumption.
- apply T_Reactive. assumption.
- apply T_Nat.
Qed.


Lemma substitution_s:
  forall typing ties Psi Delta P x s v U,
  PlacementContext typing ties Psi (idUpdate x (U on P) Delta) |~ s ->
  Context typing ties Psi emptyPlaceEnv emptyVarEnv P |- v \in U ->
  PlacementContext typing ties Psi Delta |~ [x :=_s v] s.
Proof.
intros.
generalize dependent U.
generalize dependent Delta.
induction s; (intros; inversion H; subst; simpl).
- case_eq (beq_id x i); intros H_eq_x.
  + eapply T_Place.
    * apply beq_id_eq in H_eq_x.
      subst.
      eapply context_invariance_s; try eassumption.
      intros.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      case_eq (beq_id x i); try reflexivity.
    * eapply substitution_t_delta; try eassumption.
      unfold emptyVarEnv, idEmpty, Maps.p_empty.
      reflexivity.
  + eapply T_Place.
    * eapply IHs; try eassumption.
      simpl in H4.
      eapply context_invariance_s; try eassumption.
      intros.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      case_eq (beq_id x0 i); try reflexivity.
      intros H_eq_x0.
      apply beq_id_eq in H_eq_x0.
      symmetry in H_eq_x0.
      subst.
      rewrite beq_id_comm in H_eq_x.
      rewrite H_eq_x.
      reflexivity.
    * eapply substitution_t_delta; try eassumption.
      unfold emptyVarEnv, idEmpty, Maps.p_empty.
      reflexivity.
- apply T_End.
Qed.
