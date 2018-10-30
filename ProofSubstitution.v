Require Import Syntax.
Require Import SemanticsStatic.
Require Import SemanticsDynamic.
Require Import ProofContext.


Lemma substitution_t_generalized:
  forall program Psi Delta Gamma P x t t' T T',
  (exists P',
   Gamma x = Datatypes.None /\
   (Delta x = Datatypes.None \/ Delta x = Datatypes.Some (T' on P')) /\
   program :: Psi; Delta; Gamma; P |- t : T /\
   program :: Psi; emptyPlaceEnv; emptyVarEnv; P' |- t' : T') \/
  (program :: Psi; Delta; idUpdate x T' Gamma; P |- t : T /\
   program :: Psi; emptyPlaceEnv; emptyVarEnv; P |- t' : T') ->
  program :: Psi; Delta; Gamma; P |- [x :=_t t'] t : T.
Proof.
intros until T'.
intros H_typing.
generalize dependent Gamma.
generalize dependent T.
generalize dependent T'.
generalize dependent P.
induction t; intros; (destruct H_typing as [ H_typing | H_typing ];
   [ destruct
       H_typing as [ P' H_typing ],
       H_typing as [ H_Gamma H_typing ],
       H_typing as [ H_Delta H_typing ],
       H_typing as [ H_typing H_typing_t' ] |
     destruct
       H_typing as [ H_typing H_typing_t' ] ]); inversion H_typing; subst; simpl.
- destruct id_dec.
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
      destruct id_dec; try contradiction.
      assumption.
    * repeat split; eassumption.
- destruct id_dec.
  + apply T_Abs.
    eapply context_invariance_t; try reflexivity || eassumption.
    intros.
    split; try reflexivity.
    unfold idUpdate, Maps.p_update, Maps.t_update.
    destruct id_dec; try reflexivity.
    destruct id_dec; try reflexivity.
    subst.
    contradiction.
  + eapply T_Abs, IHt; try assumption.
    right.
    split; try assumption.
    eapply context_invariance_t; try reflexivity || eassumption.
    * intros.
      split; try reflexivity.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      destruct id_dec; try reflexivity.
      destruct id_dec; try reflexivity.
      subst.
      contradiction.
    * assumption.
- eapply T_App.
  + eapply IHt1. left. exists P'. repeat split; eassumption.
  + eapply IHt2. left. exists P'. repeat split; eassumption.
- eapply T_App.
  + eapply IHt1. right. split; eassumption.
  + eapply IHt2. right. split; eassumption.
- destruct id_dec.
  + destruct H5.
    * congruence.
    * { destruct H.
        destruct H_Delta.
        - congruence.
        - subst.
          rewrite H1 in H0.
          inversion H0.
          subst.
          eapply typable_empty_closed_t in H_typing_t' as H_closed.
          unfold closed_t in H_closed.
          eapply context_invariance_t; try eassumption; intros x H_free_x.
          + specialize H_closed with x.
            contradiction.
          + specialize H_closed with x.
            apply appears_free_locally_or_remotely in H_free_x.
           contradiction.
      }
  + apply T_Var.
    assumption.
- destruct id_dec.
  + subst.
    unfold idUpdate, Maps.p_update, Maps.t_update in H5.
    destruct id_dec; try contradiction.
    destruct H5.
    * { inversion H.
        subst.
        eapply typable_empty_closed_t in H_typing_t' as H_closed.
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
    assert (Gamma i = idUpdate x T' Gamma i).
    * unfold idUpdate, Maps.p_update, Maps.t_update.
      destruct id_dec; try reflexivity.
      subst.
      contradiction.
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
- eapply T_Reactive; eassumption.
- eapply T_Reactive; eassumption.
- apply T_Nat.
- apply T_Nat.
Qed.


Lemma substitution_t:
  forall program Psi Delta Gamma P x t t' T T',
  program :: Psi; Delta; idUpdate x T' Gamma; P |- t : T ->
  program :: Psi; emptyPlaceEnv; emptyVarEnv; P |- t' : T' ->
  program :: Psi; Delta; Gamma; P |- [x :=_t t'] t : T.
Proof.
intros.
eapply substitution_t_generalized.
right. split; eassumption.
Qed.


Lemma substitution_s_generalized:
  forall program Psi Delta Gamma P P' x t t' T T',
  program :: Psi; emptyPlaceEnv; emptyVarEnv; P' |- t' : T' ->
  program :: Psi; idUpdate x (T' on P') Delta; Gamma; P |- t : T ->
  (Gamma x = Datatypes.None ->
   program :: Psi; Delta; Gamma; P |- subst_s_locality x t' t LocalOrRemoteVar : T) /\
  (Gamma x <> Datatypes.None ->
   program :: Psi; Delta; Gamma; P |- subst_s_locality x t' t RemoteVar : T).
Proof.
intros until T'.
intros H_typing_t' H_typing.
generalize dependent Delta.
generalize dependent Gamma.
generalize dependent T.
generalize dependent P.
induction t; intros; split; intros H_Gamma; inversion H_typing; subst; simpl.
- destruct id_dec.
  + eapply T_Abs, IHt; try eassumption.
    unfold idUpdate, Maps.p_update, Maps.t_update.
    destruct id_dec; try contradiction.
    congruence.
  + eapply T_Abs, IHt; try eassumption.
    unfold idUpdate, Maps.p_update, Maps.t_update.
    destruct id_dec; try contradiction.
    assumption.
- destruct id_dec.
  + eapply T_Abs, IHt; try eassumption.
    unfold idUpdate, Maps.p_update, Maps.t_update.
    destruct id_dec; try contradiction.
    congruence.
  + eapply T_Abs, IHt; try eassumption.
    unfold idUpdate, Maps.p_update, Maps.t_update.
    destruct id_dec; try contradiction.
    assumption.
- eapply T_App; [ apply IHt1 | apply IHt2 ]; eassumption.
- eapply T_App; [ apply IHt1 | apply IHt2 ]; eassumption.
- destruct id_dec.
  + destruct H5.
    * congruence.
    * { subst.
        destruct H.
        unfold idUpdate, Maps.p_update, Maps.t_update in H0.
        destruct id_dec; try contradiction.
        inversion H0.
        subst.
        eapply typable_empty_closed_t in H_typing_t' as H_closed.
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
      destruct id_dec; try reflexivity.
      subst.
      contradiction.
- apply T_Var.
  destruct H5.
  + left. assumption.
  + destruct H.
    unfold idUpdate, Maps.p_update, Maps.t_update in H0.
    destruct id_dec.
    * subst.
      congruence.
    * right. split; assumption.
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
- destruct id_dec.
  + eapply T_Comp; try reflexivity || eassumption.
    * eapply IHt1; eassumption.
    * eapply IHt2; try eassumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      destruct id_dec; try contradiction.
      congruence.
  + eapply T_Comp; try reflexivity || eassumption.
    * eapply IHt1; eassumption.
    * eapply IHt2; try eassumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      destruct id_dec; try contradiction.
      unfold emptyVarEnv, idEmpty, Maps.p_empty.
      reflexivity.
- destruct id_dec.
  + eapply T_Comp; try reflexivity || eassumption.
    * eapply IHt1; eassumption.
    * eapply IHt2; try eassumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      destruct id_dec; try contradiction.
      congruence.
  + eapply T_Comp; try reflexivity || eassumption.
    * eapply IHt1; eassumption.
    * eapply IHt2; try eassumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      destruct id_dec; try contradiction.
      unfold emptyVarEnv, idEmpty, Maps.p_empty.
      reflexivity.
- destruct id_dec.
  + eapply T_ComFrom; try reflexivity || eassumption.
    * eapply IHt1; eassumption.
    * eapply IHt2; try eassumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      destruct id_dec; try contradiction.
      congruence.
    * eapply IHt3; eassumption.
  + eapply T_ComFrom; try reflexivity || eassumption.
    * eapply IHt1; eassumption.
    * eapply IHt2; try eassumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      destruct id_dec; try contradiction.
      unfold emptyVarEnv, idEmpty, Maps.p_empty.
      reflexivity.
    * eapply IHt3; eassumption.
- destruct id_dec.
  + eapply T_ComFrom; try reflexivity || eassumption.
    * eapply IHt1; eassumption.
    * eapply IHt2; try eassumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      destruct id_dec; try contradiction.
      congruence.
    * eapply IHt3; eassumption.
  + eapply T_ComFrom; try reflexivity || eassumption.
    * eapply IHt1; eassumption.
    * eapply IHt2; try eassumption.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      destruct id_dec; try contradiction.
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
- eapply T_Reactive; eassumption.
- eapply T_Reactive; eassumption.
- apply T_Nat.
- apply T_Nat.
Qed.


Lemma substitution_s:
  forall program Psi Delta P x s t T,
  program :: Psi; idUpdate x (T on P) Delta |- s ->
  program :: Psi; emptyPlaceEnv; emptyVarEnv; P |- t : T ->
  program :: Psi; Delta |- [x :=_s t] s.
Proof.
intros.
generalize dependent T.
generalize dependent Delta.
induction s; intros; inversion H; subst; simpl.
- destruct id_dec.
  + eapply T_Place.
    * eapply context_invariance_s; try eassumption.
      intros y H_free_y.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      destruct id_dec; try reflexivity.
      destruct id_dec; try reflexivity.
      subst.
      contradiction.
    * eapply substitution_s_generalized; try eassumption.
      unfold emptyVarEnv, idEmpty, Maps.p_empty.
      reflexivity.
  + eapply T_Place.
    * eapply IHs; try eassumption.
      eapply context_invariance_s; try eassumption.
      intros y H_free_y.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      destruct id_dec; try reflexivity.
      destruct id_dec; try reflexivity.
      subst.
      contradiction.
    * eapply substitution_s_generalized; try eassumption.
      unfold emptyVarEnv, idEmpty, Maps.p_empty.
      reflexivity.
- apply T_End.
Qed.
