Require Import ReTierSyntax.
Require Import ReTierStaticSemantics.
Require Import ReTierDynamicSemantics.

Lemma aggregation_multiple : forall
    (c: context)
    (p0 p1 : P)
    (peers: Coq.Lists.ListSet.set p)
    (v v_agg: t)
    (v_type: T),
  getTieMult c (p0, p1) = Some multiple ->
  transmittable_value v ->
  c |- v \in v_type ->
  Phi (getTies c) p0 p1 peers v v_type = Some v_agg ->
  transmittable_value v_agg /\ c |- v_agg \in (List v_type).
Proof.
intros until v_type.
intros H_multiple H_value H_v_type H_Phi.
unfold getTieMult in H_multiple.
generalize dependent v_agg.
induction peers as [| peer0 peers IH_peers ]; intros v_agg H_Phi.
- simpl in H_Phi.
  rewrite H_multiple in H_Phi.
  inversion H_Phi.
  split.
  + apply w_nil.
  + apply T_Nil.
- assert (H : exists v_agg, Phi (getTies c) p0 p1 peers v v_type = Some v_agg).
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
    simpl in IH_peers, H_Phi, H_Phi2.
    rewrite H_multiple in H_Phi.
    rewrite H_Phi2 in H_Phi.
    rewrite H_Phi2 in IH_peers.
    clear H_Phi2.
    inversion H_Phi.
    split.
    * apply w_cons; try assumption.
      apply IH_peers.
      reflexivity.
    * apply T_Cons; try assumption.
      apply IH_peers.
      reflexivity.
Qed.

Lemma aggregation_optional : forall
    (c: context)
    (p0 p1 : P)
    (peers: Coq.Lists.ListSet.set p)
    (v v_agg: t)
    (v_type: T),
  getTieMult c (p0, p1) = Some optional ->
  transmittable_value v ->
  c |- v \in v_type ->
  Phi (getTies c) p0 p1 peers v v_type = Some v_agg ->
  transmittable_value v_agg /\ c |- v_agg \in (Option v_type).
Proof.
intros until v_type.
intros H_multiple H_value H_v_type H_Phi.
unfold getTieMult in H_multiple.
destruct peers.
- simpl in H_Phi.
  rewrite H_multiple in H_Phi.
  inversion H_Phi.
  split.
  + apply w_none.
  + apply T_None.
- simpl in H_Phi.
  rewrite H_multiple in H_Phi.
  destruct peers.
  + inversion H_Phi.
    split.
    * apply w_some. assumption.
    * apply T_Some. assumption.
  + contradict H_Phi.
    congruence.
Qed.

Lemma aggregation_single : forall
    (c: context)
    (p0 p1 : P)
    (peers: Coq.Lists.ListSet.set p)
    (v v_agg: t)
    (v_type: T),
  getTieMult c (p0, p1) = Some single ->
  transmittable_value v ->
  c |- v \in v_type ->
  Phi (getTies c) p0 p1 peers v v_type = Some v_agg ->
  transmittable_value v_agg /\ c |- v_agg \in v_type.
Proof.
intros until v_type.
intros H_multiple H_value H_v_type H_Phi.
unfold getTieMult in H_multiple.
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
    split; assumption.
  + contradict H_Phi.
    congruence.
Qed.

Lemma aggregation : forall
    (c: context)
    (p0 p1 : P)
    (peers: Coq.Lists.ListSet.set p)
    (v v_agg: t)
    (v_type v_agg_type: T),
  getTieMult c (p0, p1) <> None ->
  getTieMult c (p0, p1) <> Some mNone ->
  Phi (getTies c) p0 p1 peers v v_type = Some v_agg ->
  phi c p0 p1 v_type = Some v_agg_type ->
  transmittable_value v ->
  c |- v \in v_type ->
  transmittable_value v_agg /\ c |- v_agg \in v_agg_type.
Proof.
intros until v_agg_type.
intros H_tie0 H_tie1 H_Phi H_phi_type H_value H_v_type.
case_eq (getTieMult c (p0, p1)).
- intros multiplicity H_tie.
  unfold phi in H_phi_type.
  rewrite H_tie in H_phi_type.
  destruct multiplicity; inversion H_phi_type as [ H_type ]; subst.
  + eapply aggregation_multiple; eassumption.
  + eapply aggregation_optional; eassumption.
  + eapply aggregation_single; eassumption.
- contradiction.
Qed.

