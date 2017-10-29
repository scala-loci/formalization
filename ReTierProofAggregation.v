Require Import ReTierSyntax.
Require Import ReTierStaticSemantics.
Require Import ReTierDynamicSemantics.

Lemma aggregation_multiple : forall
    (c: context)
    (p0 p1 : P)
    (peers: Coq.Lists.ListSet.set p)
    (term: t)
    (value: t)
    (value_type: T),
  getTieMult c (p0, p1) = Some multiple ->
  c |- value \in value_type ->
  Phi (getTies c) p0 p1 peers value value_type = Some term ->
  c |- term \in (List value_type).
Proof.
intros c p0 p1 peers term value value_type.
intros H_multiple H_value_type H_Phi_term.
unfold getTieMult in H_multiple.
generalize dependent term.
induction peers as [| peer0 peers IH_peers ]; intros term H_Phi_term.
- simpl in H_Phi_term.
  rewrite H_multiple in H_Phi_term.
  inversion H_Phi_term.
  apply T_Nil.
- assert (H : exists term, Phi (getTies c) p0 p1 peers value value_type = Some term).
  + clear IH_peers H_Phi_term.
    induction peers as [| peer1 peers IH_peers ].
    * simpl.
      rewrite H_multiple.
      exists (nil value_type).
      reflexivity.
    * simpl.
      rewrite H_multiple.
      inversion IH_peers as [ term2 H_Phi_term2 ].
      rewrite H_Phi_term2.
      exists (cons value term2).
      reflexivity.
  + inversion H as [ term2 H_Phi_term2 ].
    simpl in IH_peers, H_Phi_term, H_Phi_term2.
    rewrite H_multiple in H_Phi_term.
    rewrite H_Phi_term2 in H_Phi_term.
    rewrite H_Phi_term2 in IH_peers.
    clear H_Phi_term2.
    inversion H_Phi_term.
    apply T_Cons.
    * assumption.
    * apply IH_peers.
      reflexivity.
Qed.

Lemma aggregation_optional : forall
    (c: context)
    (p0 p1 : P)
    (peers: Coq.Lists.ListSet.set p)
    (term: t)
    (value: t)
    (value_type: T),
  getTieMult c (p0, p1) = Some optional ->
  c |- value \in value_type ->
  Phi (getTies c) p0 p1 peers value value_type = Some term ->
  c |- term \in (Option value_type).
Proof.
intros c p0 p1 peers term value value_type.
intros H_multiple H_value_type H_Phi_term.
unfold getTieMult in H_multiple.
destruct peers.
- simpl in H_Phi_term.
  rewrite H_multiple in H_Phi_term.
  inversion H_Phi_term.
  apply T_None.
- simpl in H_Phi_term.
  rewrite H_multiple in H_Phi_term.
  destruct peers.
  + inversion H_Phi_term.
    apply T_Some.
    assumption.
  + contradict H_Phi_term.
    congruence.
Qed.

Lemma aggregation_single : forall
    (c: context)
    (p0 p1 : P)
    (peers: Coq.Lists.ListSet.set p)
    (term: t)
    (value: t)
    (value_type: T),
  getTieMult c (p0, p1) = Some single ->
  c |- value \in value_type ->
  Phi (getTies c) p0 p1 peers value value_type = Some term ->
  c |- term \in value_type.
Proof.
intros c p0 p1 peers term value value_type.
intros H_multiple H_value_type H_Phi_term.
unfold getTieMult in H_multiple.
destruct peers.
- simpl in H_Phi_term.
  rewrite H_multiple in H_Phi_term.
  contradict H_Phi_term.
  congruence.
- simpl in H_Phi_term.
  rewrite H_multiple in H_Phi_term.
  destruct peers.
  + inversion H_Phi_term.
    congruence.
  + contradict H_Phi_term.
    congruence.
Qed.

Lemma aggregation : forall
    (c: context)
    (p0 p1 : P)
    (peers: Coq.Lists.ListSet.set p)
    (value: t)
    (value_type: T)
    (term: t)
    (term_type: T),
  getTieMult c (p0, p1) <> None ->
  getTieMult c (p0, p1) <> Some mNone ->
  Phi (getTies c) p0 p1 peers value value_type = Some term ->
  phi c p0 p1 value_type = Some term_type ->
  c |- value \in value_type ->
  c |- term \in term_type.
Proof.
intros c p0 p1 peers value value_type term term_type.
intros H_tie0 H_tie1 H_Phi_term H_phi_term_type H_value_type.
case_eq (getTieMult c (p0, p1)).
- intros multiplicity H_tie.
  unfold phi in H_phi_term_type.
  rewrite H_tie in H_phi_term_type.
  destruct multiplicity; inversion H_phi_term_type as [ H_term_type ]; subst.
  + eapply aggregation_multiple; eassumption.
  + eapply aggregation_optional; eassumption.
  + eapply aggregation_single; eassumption.
- contradiction.
Qed.

