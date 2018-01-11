Require Import ReTierSyntax.
Require Import ReTierStaticSemantics.
Require Import ReTierDynamicSemantics.

Lemma aggregation_multiple:
  forall program Psi Delta Gamma P P0 P1 peers v v_agg v_type,
  peer_ties program (P0, P1) = Multiple ->
  value v ->
  transmittable_type v_type ->
  program :: Psi; Delta; Gamma; P |- v : v_type ->
  Phi (peer_ties program) P0 P1 peers v v_type = Some v_agg ->
    value v_agg /\
    transmittable_type (List v_type) /\
    program :: Psi; Delta; Gamma; P |- v_agg : List v_type.
Proof.
intros until v_type.
intros H_multiple H_value H_transmittable H_type H_Phi.
generalize dependent v_agg.
induction peers as [| peer0 peers IH_peers ]; intros v_agg H_Phi.
- simpl in H_Phi.
  rewrite H_multiple in H_Phi.
  inversion H_Phi.
  repeat split.
  + apply v_nil.
  + apply U_List. assumption.
  + apply T_Nil.
- assert (H : exists v_agg, Phi (peer_ties program) P0 P1 peers v v_type = Some v_agg).
  + clear IH_peers H_Phi.
    induction peers as [| peer1 peers IH_peers ].
    * simpl.
      rewrite H_multiple.
      exists (nil v_type).
      reflexivity.
    * simpl.
      rewrite H_multiple.
      inversion IH_peers as [ v_agg2 H_Phi2 ].
      rewrite H_Phi2.
      exists (cons v v_agg2).
      reflexivity.
  + inversion H as [ v_agg2 H_Phi2 ].
    simpl in H_Phi.
    rewrite H_multiple in H_Phi.
    rewrite H_Phi2 in H_Phi.
    rewrite H_Phi2 in IH_peers.
    clear H_Phi2.
    inversion H_Phi.
    repeat split.
    * apply v_cons; try assumption.
      apply IH_peers.
      reflexivity.
    * apply U_List. assumption.
    * apply T_Cons; try assumption.
      apply IH_peers.
      reflexivity.
Qed.

Lemma aggregation_optional:
  forall program Psi Delta Gamma P P0 P1 peers v v_agg v_type,
  peer_ties program (P0, P1) = Optional ->
  value v ->
  transmittable_type v_type ->
  program :: Psi; Delta; Gamma; P |- v : v_type ->
  Phi (peer_ties program) P0 P1 peers v v_type = Some v_agg ->
    value v_agg /\
    transmittable_type (Option v_type) /\
    program :: Psi; Delta; Gamma; P |- v_agg : Option v_type.
Proof.
intros until v_type.
intros H_multiple H_value H_transmittable H_type H_Phi.
destruct peers.
- simpl in H_Phi.
  rewrite H_multiple in H_Phi.
  inversion H_Phi.
  repeat split.
  + apply v_none.
  + apply U_Option. assumption.
  + apply T_None.
- simpl in H_Phi.
  rewrite H_multiple in H_Phi.
  destruct peers.
  + inversion H_Phi.
    repeat split.
    * apply v_some. assumption.
    * apply U_Option. assumption.
    * apply T_Some. assumption.
  + contradict H_Phi.
    congruence.
Qed.

Lemma aggregation_single:
  forall program Psi Delta Gamma P P0 P1 peers v v_agg v_type,
  peer_ties program (P0, P1) = Single ->
  value v ->
  transmittable_type v_type ->
  program :: Psi; Delta; Gamma; P |- v : v_type ->
  Phi (peer_ties program) P0 P1 peers v v_type = Some v_agg ->
    value v_agg /\
    transmittable_type v_type /\
    program :: Psi; Delta; Gamma; P |- v_agg : v_type.
Proof.
intros until v_type.
intros H_multiple H_value H_transmittable H_type H_Phi.
destruct peers.
- simpl in H_Phi.
  rewrite H_multiple in H_Phi.
  contradict H_Phi.
  congruence.
- simpl in H_Phi.
  rewrite H_multiple in H_Phi.
  destruct peers.
  + inversion H_Phi.
    subst.
    repeat split; assumption.
  + contradict H_Phi.
    congruence.
Qed.

Lemma aggregation:
  forall program Psi Delta Gamma P P0 P1 peers v v_agg v_type v_agg_type,
  peers_tied program P0 P1 ->
  Phi (peer_ties program) P0 P1 peers v v_type = Some v_agg ->
  phi (peer_ties program) P0 P1 v_type = Some v_agg_type ->
  value v ->
  transmittable_type v_type ->
  program :: Psi; Delta; Gamma; P |- v : v_type ->
    value v_agg /\
    transmittable_type v_agg_type /\
    program :: Psi; Delta; Gamma; P |- v_agg : v_agg_type.
Proof.
intros until v_agg_type.
intros H_tied H_Phi H_phi_type H_value H_transmittable H_type.
unfold phi in H_phi_type.
remember (peer_ties program (P0, P1)) as multiplicity eqn:H_tie.
symmetry in H_tie.
destruct multiplicity; inversion H_phi_type; subst.
- eapply aggregation_multiple; eassumption.
- eapply aggregation_optional; eassumption.
- eapply aggregation_single; eassumption.
Qed.

