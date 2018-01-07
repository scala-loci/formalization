Require Import ReTierSyntax.
Require Import ReTierStaticSemantics.
Require Import ReTierDynamicSemantics.
Require Import ReTierProofContext.


Lemma substitution_t_generalized:
  forall program Psi Delta Gamma P x t T v U,
  (exists P',
   Gamma x = None /\
   (Delta x = None \/ Delta x = Some (U on P')) /\
   program :: Psi; Delta; Gamma; P |- t : T /\
   program :: Psi; emptyPlaceEnv; emptyVarEnv; P' |- v : U) \/
  (program :: Psi; Delta; idUpdate x U Gamma; P |- t : T /\
   program :: Psi; emptyPlaceEnv; emptyVarEnv; P |- v : U) ->
  program :: Psi; Delta; Gamma; P |- [x :=_t v] t : T.
Proof.
intros until U.
intros H_typing.
generalize dependent Gamma.
generalize dependent T.
generalize dependent U.
generalize dependent P.
induction t; intros; (destruct H_typing as [ H_typing | H_typing ];
   [ destruct
       H_typing as [ P' H_typing ],
       H_typing as [ H_Gamma H_typing ],
       H_typing as [ H_Delta H_typing ],
       H_typing as [ H_typing H_typing_v ] |
     destruct
       H_typing as [ H_typing H_typing_v ] ]); inversion H_typing; subst; simpl.
- case_eq (beq_id x i); intros H_eq.
  + apply T_Abs.
    eapply context_invariance_t; try reflexivity || eassumption.
    intros.
    split; reflexivity.
  + eapply T_Abs, IHt; try assumption.
    left.
    intros.
    exists P'.
    split.
    * unfold idUpdate, Maps.p_update, Maps.t_update.
      rewrite H_eq.
      assumption.
    * repeat split; eassumption.
- case_eq (beq_id x i); intros H_eq.
  + apply T_Abs.
    apply beq_id_eq in H_eq.
    subst.
    eapply context_invariance_t; try reflexivity || eassumption.
    intros.
    split; try reflexivity.
    unfold idUpdate, Maps.p_update, Maps.t_update.
    destruct (beq_id x i); reflexivity.
  + eapply T_Abs, IHt; try assumption.
    right.
    split; try assumption.
    eapply context_invariance_t; try reflexivity || eassumption.
    * intros.
      split; try reflexivity.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      case_eq (beq_id x0 i); try reflexivity.
      intros H_eq_x0.
      apply beq_id_eq in H_eq_x0.
      subst.
      rewrite beq_id_comm in H_eq.
      rewrite H_eq.
      reflexivity.
    * assumption.
- eapply T_App.
  + eapply IHt1. left. exists P'. repeat split; eassumption.
  + eapply IHt2. left. exists P'. repeat split; eassumption.
- eapply T_App.
  + eapply IHt1. right. split; eassumption.
  + eapply IHt2. right. split; eassumption.
- case_eq (beq_id x i); intros H_eq.
  + rewrite beq_id_eq in H_eq.
    subst.
    destruct H5.
    * congruence.
    * { destruct H.
        destruct H_Delta; try congruence.
        rewrite H1 in H0.
        inversion H0.
        subst.
        eapply typable_empty_closed_t in H_typing_v as H_closed.
        unfold closed_t in H_closed.
        eapply context_invariance_t; try eassumption; intros x H_free_x.
        - specialize H_closed with x.
          contradiction.
        - specialize H_closed with x.
          apply appears_free_locally_or_remotely in H_free_x.
          contradiction.
      }
  + apply T_Var.
    assumption.
- case_eq (beq_id x i); intros H_eq.
  + rewrite beq_id_eq in H_eq.
    subst.
    unfold idUpdate, Maps.p_update, Maps.t_update in H5.
    rewrite beq_id_refl in H5.
    destruct H5.
    * { inversion H.
        subst.
        eapply typable_empty_closed_t in H_typing_v as H_closed.
        unfold closed_t in H_closed.
        eapply context_invariance_t; try eassumption; intros x H_free_x.
        - specialize H_closed with x.
          contradiction.
        - specialize H_closed with x.
          apply appears_free_locally_or_remotely in H_free_x.
          contradiction.
      }
    * destruct H.
      congruence.
  + apply T_Var.
    assert (Gamma i = idUpdate x U Gamma i).
    * unfold idUpdate, Maps.p_update, Maps.t_update.
      rewrite beq_id_comm in H_eq.
      rewrite H_eq.
      reflexivity.
    * rewrite H.
      assumption.
- apply T_Unit.
- apply T_Unit.
- apply T_None.
- apply T_None.
- apply T_Some. eapply IHt. left. exists P'. repeat split; eassumption.
- apply T_Some. eapply IHt. right. split; eassumption.
- apply T_Nil.
- apply T_Nil.
- eapply T_Cons.
  + eapply IHt1. left. exists P'. repeat split; eassumption.
  + eapply IHt2. left. exists P'. repeat split; eassumption.
- eapply T_Cons.
  + eapply IHt1. right. split; eassumption.
  + eapply IHt2. right. split; eassumption.
- eapply T_AsLocal; reflexivity || eassumption.
- pose proof delta_typing as H_Delta.
  specialize H_Delta with Delta x.
  destruct H_Delta as [ H_Delta | H_Delta ].
  + eapply T_AsLocal; reflexivity || eassumption.
  + destruct H_Delta as [ T'' H_Delta ], H_Delta as [ P'' H_Delta ].
    eapply T_AsLocal; reflexivity || eassumption.
- eapply T_AsLocalFrom; try reflexivity || eassumption.
  eapply IHt2. left. exists P'. repeat split; eassumption.
- pose proof delta_typing as H_Delta.
  specialize H_Delta with Delta x.
  destruct H_Delta as [ H_Delta | H_Delta ].
  + eapply T_AsLocalFrom; try reflexivity || eassumption.
    eapply IHt2. right. split; eassumption.
  + destruct H_Delta as [ T'' H_Delta ], H_Delta as [ P'' H_Delta ].
    eapply T_AsLocalFrom; try reflexivity || eassumption.
    eapply IHt2. right. split; eassumption.
- eapply T_Comp; try reflexivity || eassumption.
  eapply IHt1. left. exists P'. repeat split; try eassumption.
- pose proof delta_typing as H_Delta.
  specialize H_Delta with Delta x.
  destruct H_Delta as [ H_Delta | H_Delta ].
  + eapply T_Comp; try reflexivity || eassumption.
    eapply IHt1. right. split; eassumption.
  + destruct H_Delta as [ T'' H_Delta ], H_Delta as [ P'' H_Delta ].
    eapply T_Comp; try reflexivity || eassumption.
    eapply IHt1. right. split; eassumption.
- eapply T_ComFrom; try reflexivity || eassumption.
  + eapply IHt1. left. exists P'. repeat split; eassumption.
  + eapply IHt3. left. exists P'. repeat split; eassumption.
- pose proof delta_typing as H_Delta.
  specialize H_Delta with Delta x.
  destruct H_Delta as [ H_Delta | H_Delta ].
  + eapply T_ComFrom; try reflexivity || eassumption.
    * eapply IHt1. right. split; eassumption.
    * eapply IHt3. right. split; eassumption.
  + destruct H_Delta as [ T'' H_Delta ], H_Delta as [ P'' H_Delta ].
    eapply T_ComFrom; try reflexivity || eassumption.
    * eapply IHt1. right. split; eassumption.
    * eapply IHt3. right. split; eassumption.
- apply T_Signal. eapply IHt. left. exists P'. repeat split; eassumption.
- apply T_Signal. eapply IHt. right. split; eassumption.
- apply T_ReactiveVar. eapply IHt. left. exists P'. repeat split; eassumption.
- apply T_ReactiveVar. eapply IHt. right. split; eassumption.
- eapply T_Now; try eassumption. eapply IHt. left. exists P'. repeat split; eassumption.
- eapply T_Now; try eassumption. eapply IHt. right. split; eassumption.
- eapply T_Set.
  + eapply IHt1. left. exists P'. repeat split; eassumption.
  + eapply IHt2. left. exists P'. repeat split; eassumption.
- eapply T_Set.
  + eapply IHt1. right. split; eassumption.
  + eapply IHt2. right. split; eassumption.
- apply T_Peer. assumption.
- apply T_Peer. assumption.
- apply T_Reactive. assumption.
- apply T_Reactive. assumption.
- apply T_Nat.
- apply T_Nat.
Qed.


Lemma substitution_t:
  forall program Psi Delta Gamma P x t T v U,
  program :: Psi; Delta; idUpdate x U Gamma; P |- t : T ->
  program :: Psi; emptyPlaceEnv; emptyVarEnv; P |- v : U ->
  program :: Psi; Delta; Gamma; P |- [x :=_t v] t : T.
Proof.
intros.
eapply substitution_t_generalized.
right. split; eassumption.
Qed.


Lemma substitution_s_generalized:
  forall program Psi Delta Gamma P P' x t T v U,
  (Gamma x = None ->
   program :: Psi; emptyPlaceEnv; emptyVarEnv; P' |- v : U ->
   program :: Psi; idUpdate x (U on P') Delta; Gamma; P |- t : T ->
   program :: Psi; Delta; Gamma; P |- subst_s_locality x v t LocalOrRemoteVar : T) /\
  (Gamma x <> None ->
   program :: Psi; emptyPlaceEnv; emptyVarEnv; P' |- v : U ->
   program :: Psi; idUpdate x (U on P') Delta; Gamma; P |- t : T ->
   program :: Psi; Delta; Gamma; P |- subst_s_locality x v t RemoteVar : T).
Proof.
intros until U.
generalize dependent Delta.
generalize dependent Gamma.
generalize dependent T.
generalize dependent P.
induction t; intros; split; intros H_Gamma H_typing_v H_typing; inversion H_typing; subst; simpl.
- case_eq (beq_id x i); intros H_eq.
  + eapply T_Abs, IHt; try eassumption.
    unfold idUpdate, Maps.p_update, Maps.t_update.
    rewrite H_eq.
    congruence.
  + eapply T_Abs, IHt; try eassumption.
    unfold idUpdate, Maps.p_update, Maps.t_update.
    rewrite H_eq.
    assumption.
- case_eq (beq_id x i); intros H_eq.
  + eapply T_Abs, IHt; try eassumption.
    unfold idUpdate, Maps.p_update, Maps.t_update.
    rewrite H_eq.
    congruence.
  + eapply T_Abs, IHt; try eassumption.
    unfold idUpdate, Maps.p_update, Maps.t_update.
    rewrite H_eq.
    assumption.
- eapply T_App; [ apply IHt1 | apply IHt2 ]; eassumption.
- eapply T_App; [ apply IHt1 | apply IHt2 ]; eassumption.
- case_eq (beq_id x i); intros H_eq.
  + destruct H5.
    * apply beq_id_eq in H_eq.
      subst.
      congruence.
    * { destruct H.
        unfold idUpdate, Maps.p_update, Maps.t_update in H0.
        rewrite beq_id_comm in H_eq.
        rewrite H_eq in H0.
        inversion H0.
        subst.
        eapply typable_empty_closed_t in H_typing_v as H_closed.
        unfold closed_t in H_closed.
        eapply context_invariance_t; try eassumption; intros y H_free_y.
        - specialize H_closed with y.
          contradiction.
        - specialize H_closed with y.
          apply appears_free_locally_or_remotely in H_free_y.
          contradiction.
      }
  + apply T_Var.
    destruct H5.
    * left. assumption.
    * right.
      destruct H.
      split; try assumption.
      rewrite <- H0.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      rewrite beq_id_comm in H_eq.
      rewrite H_eq.
      reflexivity.
- case_eq (beq_id x i); intros H_eq.
  + apply T_Var.
    apply beq_id_eq in H_eq.
    subst.
    destruct H5.
    * left. assumption.
    * destruct H.
      congruence.
  + apply T_Var.
    destruct H5.
    * left. assumption.
    * destruct H.
      unfold idUpdate, Maps.p_update, Maps.t_update in H0.
      rewrite beq_id_comm in H_eq.
      rewrite H_eq in H0.
      right. split; assumption.
- apply T_Unit.
- apply T_Unit.
- apply T_None.
- apply T_None.
- apply T_Some. apply IHt; assumption.
- apply T_Some. apply IHt; assumption.
- apply T_Nil.
- apply T_Nil.
- apply T_Cons; [ apply IHt1 | apply IHt2 ]; eassumption.
- apply T_Cons; [ apply IHt1 | apply IHt2 ]; eassumption.
- eapply T_AsLocal; try reflexivity || eassumption.
  eapply IHt; try eassumption.
  unfold emptyVarEnv, idEmpty, Maps.p_empty.
  reflexivity.
- eapply T_AsLocal; try reflexivity || eassumption.
  eapply IHt; try eassumption.
  unfold emptyVarEnv, idEmpty, Maps.p_empty.
  reflexivity.
- eapply T_AsLocalFrom; try reflexivity || eassumption.
  + eapply IHt1; try eassumption.
    unfold emptyVarEnv, idEmpty, Maps.p_empty.
    reflexivity.
  + eapply IHt2; try eassumption.
- eapply T_AsLocalFrom; try reflexivity || eassumption.
  + eapply IHt1; try eassumption.
    unfold emptyVarEnv, idEmpty, Maps.p_empty.
    reflexivity.
  + eapply IHt2; try eassumption.
- case_eq (beq_id x i); intros H_eq.
  + eapply T_Comp; try reflexivity || eassumption.
    * eapply IHt1; eassumption.
    * eapply IHt2; try eassumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      rewrite H_eq.
      congruence.
  + eapply T_Comp; try reflexivity || eassumption.
    * eapply IHt1; eassumption.
    * eapply IHt2; try eassumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      rewrite H_eq.
      unfold emptyVarEnv, idEmpty, Maps.p_empty.
      reflexivity.
- case_eq (beq_id x i); intros H_eq.
  + eapply T_Comp; try reflexivity || eassumption.
    * eapply IHt1; eassumption.
    * eapply IHt2; try eassumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      rewrite H_eq.
      congruence.
  + eapply T_Comp; try reflexivity || eassumption.
    * eapply IHt1; eassumption.
    * eapply IHt2; try eassumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      rewrite H_eq.
      unfold emptyVarEnv, idEmpty, Maps.p_empty.
      reflexivity.
- case_eq (beq_id x i); intros H_eq.
  + eapply T_ComFrom; try reflexivity || eassumption.
    * eapply IHt1; eassumption.
    * eapply IHt2; try eassumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      rewrite H_eq.
      congruence.
    * eapply IHt3; eassumption.
  + eapply T_ComFrom; try reflexivity || eassumption.
    * eapply IHt1; eassumption.
    * eapply IHt2; try eassumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      rewrite H_eq.
      unfold emptyVarEnv, idEmpty, Maps.p_empty.
      reflexivity.
    * eapply IHt3; eassumption.
- case_eq (beq_id x i); intros H_eq.
  + eapply T_ComFrom; try reflexivity || eassumption.
    * eapply IHt1; eassumption.
    * eapply IHt2; try eassumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      rewrite H_eq.
      congruence.
    * eapply IHt3; eassumption.
  + eapply T_ComFrom; try reflexivity || eassumption.
    * eapply IHt1; eassumption.
    * eapply IHt2; try eassumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      rewrite H_eq.
      unfold emptyVarEnv, idEmpty, Maps.p_empty.
      reflexivity.
    * eapply IHt3; eassumption.
- apply T_Signal. apply IHt; assumption.
- apply T_Signal. apply IHt; assumption.
- apply T_ReactiveVar. apply IHt; assumption.
- apply T_ReactiveVar. apply IHt; assumption.
- eapply T_Now; try eassumption. apply IHt; assumption.
- eapply T_Now; try eassumption. apply IHt; assumption.
- eapply T_Set; [ apply IHt1 | apply IHt2 ]; eassumption.
- eapply T_Set; [ apply IHt1 | apply IHt2 ]; eassumption.
- apply T_Peer. assumption.
- apply T_Peer. assumption.
- apply T_Reactive. assumption.
- apply T_Reactive. assumption.
- apply T_Nat.
- apply T_Nat.
Qed.


Lemma substitution_s:
  forall program Psi Delta P x s v U,
  program :: Psi; idUpdate x (U on P) Delta |- s ->
  program :: Psi; emptyPlaceEnv; emptyVarEnv; P |- v : U ->
  program :: Psi; Delta |- [x :=_s v] s.
Proof.
intros.
generalize dependent U.
generalize dependent Delta.
induction s; intros; inversion H; subst; simpl.
- case_eq (beq_id x i); intros H_eq_x.
  + eapply T_Place.
    * apply beq_id_eq in H_eq_x.
      subst.
      eapply context_invariance_s; try eassumption.
      intros y H_free_y.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      destruct (beq_id y i); reflexivity.
    * eapply substitution_s_generalized; try eassumption.
      unfold emptyVarEnv, idEmpty, Maps.p_empty.
      reflexivity.
  + eapply T_Place.
    * eapply IHs; try eassumption.
      eapply context_invariance_s; try eassumption.
      intros y H_free_y.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      case_eq (beq_id y i); try reflexivity.
      intros H_eq_y.
      apply beq_id_eq in H_eq_y.
      rewrite <- H_eq_y in H_eq_x.
      rewrite beq_id_comm in H_eq_x.
      rewrite H_eq_x.
      reflexivity.
    * eapply substitution_s_generalized; try eassumption.
      unfold emptyVarEnv, idEmpty, Maps.p_empty.
      reflexivity.
- apply T_End.
Qed.
