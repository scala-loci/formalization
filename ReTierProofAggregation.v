Require Import ReTierSyntax.
Require Import ReTierStaticSemantics.
Require Import ReTierDynamicSemantics.
Require Import ReTierProofTransmission.

Lemma aggregation_multiple:
  forall program Psi Delta Delta' Gamma Gamma' P0 P1 peers v v_agg v_type,
  peers_tied program P0 P1 ->
  peer_ties program (P0, P1) = Multiple ->
  value v ->
  transmittable_type v_type ->
  List.incl peers (peer_instances_of_type program P1) ->
  program :: Psi; Delta; Gamma; P1 |- v : v_type ->
  Phi (peer_ties program) P0 P1 peers v v_type = Some v_agg ->
  program :: Psi; Delta'; Gamma'; P0 |- v_agg : List v_type.
Proof.
intros until v_type.
intros H_tied H_multiple H_value H_transmittable H_instances H_type H_Phi.
generalize dependent v_agg.
induction peers as [| peer0 peers IH_peers ]; intros v_agg H_Phi.
- simpl in H_Phi.
  rewrite H_multiple in H_Phi.
  inversion H_Phi.
  apply T_Nil.
- assert (H : exists v_agg, Phi (peer_ties program) P0 P1 peers v v_type = Some v_agg).
  + clear IH_peers H_instances H_Phi.
    induction peers as [| peer1 peers IH_peers ].
    * simpl.
      rewrite H_multiple.
      exists (nil v_type).
      reflexivity.
    * simpl.
      rewrite H_multiple.
      destruct IH_peers as [ v_agg2 H_Phi ].
      rewrite H_Phi.
      esplit.
      reflexivity.
  + inversion H as [ v_agg2 H_Phi2 ].
    simpl in H_Phi.
    rewrite H_multiple in H_Phi.
    rewrite H_Phi2 in H_Phi.
    rewrite H_Phi2 in IH_peers.
    clear H_Phi2.
    inversion H_Phi.
    apply T_Cons.
    * eapply transmission; try eassumption.
      unfold List.incl.
      intros.
      simpl in H0.
      destruct H0; try contradiction.
      subst.
      apply H_instances.
      simpl.
      left. reflexivity.
    * apply IH_peers; try reflexivity.
      unfold List.incl.
      intros.
      apply H_instances.
      simpl.
      right. assumption.
Qed.

Lemma aggregation_optional:
  forall program Psi Delta Delta' Gamma Gamma' P0 P1 peers v v_agg v_type,
  peers_tied program P0 P1 ->
  peer_ties program (P0, P1) = Optional ->
  value v ->
  transmittable_type v_type ->
  List.incl peers (peer_instances_of_type program P1) ->
  program :: Psi; Delta; Gamma; P1 |- v : v_type ->
  Phi (peer_ties program) P0 P1 peers v v_type = Some v_agg ->
  program :: Psi; Delta'; Gamma'; P0 |- v_agg : Option v_type.
Proof.
intros until v_type.
intros H_tied H_optional H_value H_transmittable H_instances H_type H_Phi.
destruct peers.
- simpl in H_Phi.
  rewrite H_optional in H_Phi.
  inversion H_Phi.
  apply T_None.
- simpl in H_Phi.
  rewrite H_optional in H_Phi.
  destruct peers.
  + inversion H_Phi.
    apply T_Some.
    eapply transmission; eassumption.
  + congruence.
Qed.

Lemma aggregation_single:
  forall program Psi Delta Delta' Gamma Gamma' P0 P1 peers v v_agg v_type,
  peers_tied program P0 P1 ->
  peer_ties program (P0, P1) = Single ->
  value v ->
  transmittable_type v_type ->
  List.incl peers (peer_instances_of_type program P1) ->
  program :: Psi; Delta; Gamma; P1 |- v : v_type ->
  Phi (peer_ties program) P0 P1 peers v v_type = Some v_agg ->
  program :: Psi; Delta'; Gamma'; P0 |- v_agg : v_type.
Proof.
intros until v_type.
intros H_tied H_single H_value H_transmittable H_instances H_type H_Phi.
destruct peers.
- simpl in H_Phi.
  rewrite H_single in H_Phi.
  congruence.
- simpl in H_Phi.
  rewrite H_single in H_Phi.
  destruct peers.
  + inversion H_Phi.
    eapply transmission; eassumption.
  + congruence.
Qed.

Lemma aggregation:
  forall program Psi Delta Delta' Gamma Gamma' P0 P1 peers v v_agg v_type v_agg_type,
  peers_tied program P0 P1 ->
  Phi (peer_ties program) P0 P1 peers v v_type = Some v_agg ->
  phi (peer_ties program) P0 P1 v_type = Some v_agg_type ->
  value v ->
  transmittable_type v_type ->
  List.incl peers (peer_instances_of_type program P1) ->
  program :: Psi; Delta; Gamma; P1 |- v : v_type ->
  program :: Psi; Delta'; Gamma'; P0 |- v_agg : v_agg_type.
Proof.
intros until v_agg_type.
intros H_tied H_Phi H_phi_type H_value H_transmittable H_instances H_type.
unfold phi in H_phi_type.
destruct (peer_ties program (P0, P1)) eqn: H_tie; inversion H_phi_type; subst.
- eapply aggregation_multiple; eassumption.
- eapply aggregation_optional; eassumption.
- eapply aggregation_single; eassumption.
Qed.

