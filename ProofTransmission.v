Require Import Syntax.
Require Import SemanticsStatic.
Require Import SemanticsDynamic.

Lemma transmission : forall program Psi Delta Delta' Gamma Gamma' P P' theta v T,
  value_t v ->
  transmittable_type T ->
  peers_tied program P' P ->
  List.incl theta (peer_instances_of_type program P) ->
  program :: Psi; Delta; Gamma; P |- v : T ->
  program :: Psi; Delta'; Gamma'; P' |- zeta P theta v T : T.
Proof.
intros until T.
intros H_value H_transmittable H_tied H_instance H_typing.
generalize dependent T.
induction v; intros; inversion H_value; inversion H_typing; subst.
- inversion H_transmittable.
- apply T_Unit.
- apply T_None.
- inversion H_transmittable.
  simpl.
  apply T_Some.
  apply IHv; assumption.
- apply T_Nil.
- inversion H_transmittable.
  simpl.
  apply T_Cons.
  + apply IHv1; assumption.
  + apply IHv2; assumption.
- apply T_Peer. assumption.
- destruct H7; subst.
  + simpl.
    apply T_Signal.
    apply T_ComFrom with (T0 := Unit).
    * inversion H_transmittable.
      assumption.
    * apply U_Unit.
    * apply T_Unit.
    * apply T_Now with (T0 := Signal T1); try (left; reflexivity).
      apply T_Reactive with (T1 := T1); try (left; reflexivity).
      assumption.
    * assumption.
    * apply T_Peer.
      assumption.
  + inversion H_transmittable.
- apply T_Nat.
Qed.
