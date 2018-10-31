Require Import Syntax.
Require Import SemanticsStatic.
Require Import SemanticsDynamic.
Require Import ProofContext.
Require Import ProofSubstitution.
Require Import ProofReactiveSystem.
Require Import ProofTransmission.
Require Import ProofAggregation.

Theorem preservation_t: forall t t' T theta theta' program Psi P rho rho',
  program :: Psi; emptyPlaceEnv; emptyVarEnv; P |- t : T ->
  program :: Psi; emptyPlaceEnv; emptyVarEnv |- rho ->
  List.incl theta (peer_instances_of_type program P) ->
  program :: theta : P |> t; rho == theta' ==> t'; rho' ->
  exists Psi',
    Psi' extends Psi /\
    program :: Psi'; emptyPlaceEnv; emptyVarEnv; P |- t' : T /\
    program :: Psi'; emptyPlaceEnv; emptyVarEnv |- rho'.
Proof.
intros until rho'.
intros H_typing H_reactive_typing H_instances H_eval.
remember emptyPlaceEnv as Delta.
remember emptyVarEnv as Gamma.
generalize dependent theta.
generalize dependent t'.
induction H_typing; intros; subst.
- inversion H_eval.
- inversion H_eval; subst.
  + apply IHH_typing1 in H8; try assumption || reflexivity.
    destruct H8 as [ Psi' ].
    destruct H, H0.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_App; try eassumption.
    eapply reactive_typing_weakening_t; eassumption.
  + apply IHH_typing2 in H9; try assumption || reflexivity.
    destruct H9 as [ Psi' ].
    destruct H, H0.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_App; try eassumption.
    eapply reactive_typing_weakening_t; eassumption.
  + inversion H_typing1.
    subst.
    exists Psi.
    split.
    * apply reactive_typing_extends_refl.
    * split; try assumption.
      eapply substitution_t; eassumption.
- inversion H_eval.
- inversion H_eval; subst.
  + apply IHH_typing1 in H8; try assumption || reflexivity.
    destruct H8 as [ Psi' ].
    destruct H, H0.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_Cons; try eassumption.
    eapply reactive_typing_weakening_t; eassumption.
  + apply IHH_typing2 in H9; try assumption || reflexivity.
    destruct H9 as [ Psi' ].
    destruct H, H0.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_Cons; try eassumption.
    eapply reactive_typing_weakening_t; eassumption.
- inversion H_eval.
- inversion H_eval; subst.
  apply IHH_typing in H3; try assumption || reflexivity.
  destruct H3 as [ Psi' ].
  destruct H, H0.
  exists Psi'.
  do 2 (split; try assumption).
  eapply T_Some; try eassumption.
- inversion H_eval.
- inversion H_eval.
- inversion H_eval.
- inversion H_eval; subst.
  + exists Psi.
    split.
    * apply reactive_typing_extends_refl.
    * split; try assumption.
      eapply aggregation; try eassumption.
      apply List.incl_refl.
  + apply IHH_typing in H12; try assumption || reflexivity.
    * destruct H12 as [ Psi' ].
      destruct H2, H3.
      exists Psi'.
      do 2 (split; try assumption).
      eapply T_AsLocal; try eassumption.
    * apply List.incl_refl.
- inversion H_eval; subst.
  + apply IHH_typing2 in H11; try assumption || reflexivity.
    destruct H11 as [ Psi' ].
    destruct H1, H2.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_AsLocalFrom; try eassumption.
    eapply reactive_typing_weakening_t; eassumption.
  + inversion H_typing2.
    subst.
    exists Psi.
    split.
    * apply reactive_typing_extends_refl.
    * split; try assumption.
      eapply transmission; try eassumption.
  + inversion H_typing2.
    subst.
    apply IHH_typing1 in H12; try assumption || reflexivity.
    destruct H12 as [ Psi' ].
    destruct H1, H2.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_AsLocalFrom; try eassumption.
    eapply reactive_typing_weakening_t; eassumption.
- inversion H_eval; subst.
  + apply IHH_typing1 in H15; try assumption || reflexivity.
    destruct H15 as [ Psi' ].
    destruct H3, H4.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_Comp; try eassumption.
    eapply reactive_typing_weakening_t; eassumption.
  + exists Psi.
    split.
    * apply reactive_typing_extends_refl.
    * split; try assumption.
      eapply T_AsLocal; try eassumption.
      eapply substitution_t; try eassumption.
      eapply transmission; try eassumption.
      unfold peers_tied in H1.
      destruct H1.
      unfold peers_tied.
      split; assumption.
- inversion H_eval; subst.
  + apply IHH_typing3 in H15; try assumption || reflexivity.
    destruct H15 as [ Psi' ].
    destruct H2, H3.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_ComFrom; try eassumption.
    * eapply reactive_typing_weakening_t; eassumption.
    * eapply reactive_typing_weakening_t; eassumption.
  + apply IHH_typing1 in H16; try assumption || reflexivity.
    destruct H16 as [ Psi' ].
    destruct H2, H3.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_ComFrom; try eassumption.
    * eapply reactive_typing_weakening_t; eassumption.
    * eapply reactive_typing_weakening_t; eassumption.
  + exists Psi.
    split.
    * apply reactive_typing_extends_refl.
    * split; try assumption.
      eapply T_AsLocalFrom; try eassumption.
      eapply substitution_t; try eassumption.
      eapply transmission; try eassumption.
      unfold peers_tied in H1.
      destruct H1.
      unfold peers_tied.
      split; assumption.
- inversion H_eval.
- inversion H_eval.
  subst.
  pose proof reactive_typing_add.
  specialize H with program Psi emptyPlaceEnv emptyVarEnv rho P t T (Signal T).
  apply H in H_reactive_typing as H0; try assumption || (right; reflexivity).
  destruct H0 as [ Psi' ], H0 as [ rho0 ], H0 as [ r' ].
  destruct H0, H1, H2, H4.
  rewrite H3 in H1.
  inversion H1.
  subst.
  exists Psi'.
  do 2 (split; try assumption).
  eapply T_Reactive; try eassumption.
  left. reflexivity.
- inversion H_eval; subst.
  + apply IHH_typing in H3; try assumption || reflexivity.
    destruct H3 as [ Psi' ].
    destruct H, H0.
    exists Psi'.
    do 2 (split; try assumption).
    apply T_ReactiveVar.
    assumption.
  + pose proof reactive_typing_add.
    specialize H with program Psi emptyPlaceEnv emptyVarEnv rho P t T (Var T).
    apply H in H_reactive_typing as H1; try assumption || (left; reflexivity).
    destruct H1 as [ Psi' ], H1 as [ rho0 ], H1 as [ r' ].
    destruct H1, H2, H3, H5.
    rewrite H4 in H2.
    inversion H2.
    subst.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_Reactive; try eassumption.
    right. reflexivity.
- inversion H_eval; subst.
  + apply IHH_typing in H4; try assumption || reflexivity.
    destruct H4 as [ Psi' ].
    destruct H0, H1.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_Now; eassumption.
  + inversion H_typing.
    subst.
    exists Psi.
    split.
    * apply reactive_typing_extends_refl.
    * { split; try assumption.
        unfold reactive_system_well_typed in H_reactive_typing.
        destruct H_reactive_typing as [ H0 H2 ].
        specialize H2 with r.
        assert (reactive_system_lookup r rho' <> Datatypes.None).
        - congruence.
        - apply reactive_system_lookup_domain in H3.
          apply H2 in H3.
          destruct H3 as [ t2 ], H3 as [ T2 ], H3 as [ T2' ], H3 as [ P2 ].
          destruct H3, H5, H6.
          rewrite H4 in H3.
          inversion H3.
          rewrite H1 in H5.
          inversion H5.
          destruct H, H6; subst; congruence.
      }
- inversion H_eval; subst.
  + apply IHH_typing1 in H8; try assumption || reflexivity.
    destruct H8 as [ Psi' ].
    destruct H, H0.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_Set; try eassumption.
    eapply reactive_typing_weakening_t; eassumption.
  + apply IHH_typing2 in H9; try assumption || reflexivity.
    destruct H9 as [ Psi' ].
    destruct H, H0.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_Set; try eassumption.
    eapply reactive_typing_weakening_t; eassumption.
  + inversion H_typing1.
    subst.
    pose proof reactive_typing_update.
    specialize H with program Psi emptyPlaceEnv emptyVarEnv rho r P t2 T.
    apply H in H_reactive_typing as H1; try assumption.
    exists Psi.
    split.
    * apply reactive_typing_extends_refl.
    * split; try assumption.
      apply T_Unit.
- inversion H_eval.
Qed.


Theorem preservation_s: forall s s' theta program Psi rho rho',
  program :: Psi; emptyPlaceEnv |- s ->
  program :: Psi; emptyPlaceEnv; emptyVarEnv |- rho ->
  program :: s; rho == theta ==> s'; rho' ->
  exists Psi',
    Psi' extends Psi /\
    program :: Psi'; emptyPlaceEnv |- s' /\
    program :: Psi'; emptyPlaceEnv; emptyVarEnv |- rho'.
Proof.
intros until rho'.
intros H_typing H_reactive_typing H_eval.
remember emptyPlaceEnv as Delta.
generalize dependent s'.
destruct H_typing; intros; subst.
- inversion H_eval.
- inversion H_eval; subst.
  + eapply preservation_t in H10; try eassumption.
    * destruct H10 as [ Psi' ].
      destruct H0, H1.
      exists Psi'.
      do 2 (split; try assumption).
      apply T_Place; try assumption.
      eapply reactive_typing_weakening_s; eassumption.
    * apply List.incl_refl.
  + exists Psi.
    split.
    * apply reactive_typing_extends_refl.
    * split; try assumption.
      eapply substitution_s; eassumption.
Qed.
