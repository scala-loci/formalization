Require Import ReTierSyntax.
Require Import ReTierStaticSemantics.
Require Import ReTierDynamicSemantics.
Require Coq.Lists.ListSet.

Theorem Aggregation_Multiple : forall
    (c: context)
    (p0 p1 : P)
    (peers: Coq.Lists.ListSet.set p)
    (term: t)
    (value: t)
    (value_type: T),
  getTieMult c (p0, p1) = Some multiple ->
  has_type c value value_type ->
  Phi (getTies c) p0 p1 peers value value_type = Some term ->
    has_type c term (List value_type).
Proof.
intros c p0 p1 peers term value value_type.
intros H_multiple H_value_type H_Phi_term.
unfold getTieMult in H_multiple.
generalize dependent term.
induction peers as [| peer0 peers IH_peers ].
- intros term H_Phi_term.
  unfold Phi in H_Phi_term.
  rewrite H_multiple in H_Phi_term.
  inversion H_Phi_term.
  apply T_Nil.
- intros term H_Phi_term.
  assert (H : exists term, Phi (getTies c) p0 p1 peers value value_type = Some term).
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
    unfold Phi in IH_peers, H_Phi_term, H_Phi_term2.
    rewrite H_multiple in H_Phi_term.
    rewrite H_Phi_term2 in H_Phi_term.
    rewrite H_Phi_term2 in IH_peers.
    clear H_Phi_term2.
    inversion H_Phi_term.
    apply T_Cons.
    * exact H_value_type.
    * apply IH_peers.
      reflexivity.
Qed.


Theorem Aggregation_Optional : forall
    (c: context)
    (p0 p1 : P)
    (peers: Coq.Lists.ListSet.set p)
    (term: t)
    (value: t)
    (value_type: T),
  getTieMult c (p0, p1) = Some optional ->
  has_type c value value_type ->
  Phi (getTies c) p0 p1 peers value value_type = Some term ->
    has_type c term (Option value_type).
Proof.
intros c p0 p1 peers term value value_type.
intros H_multiple H_value_type H_Phi_term.
unfold getTieMult in H_multiple.
destruct peers.
- unfold Phi in H_Phi_term.
  rewrite H_multiple in H_Phi_term.
  inversion H_Phi_term.
  apply T_None.
- unfold Phi in H_Phi_term.
  rewrite H_multiple in H_Phi_term.
  destruct peers.
  + inversion H_Phi_term.
    apply T_Some.
    exact H_value_type.
  + contradict H_Phi_term.
    congruence.
Qed.

Theorem Aggregation_Single : forall
    (c: context)
    (p0 p1 : P)
    (peers: Coq.Lists.ListSet.set p)
    (term: t)
    (value: t)
    (value_type: T),
  getTieMult c (p0, p1) = Some single ->
  has_type c value value_type ->
  Phi (getTies c) p0 p1 peers value value_type = Some term ->
    has_type c term value_type.
Proof.
intros c p0 p1 peers term value value_type.
intros H_multiple H_value_type H_Phi_term.
unfold getTieMult in H_multiple.
destruct peers.
- unfold Phi in H_Phi_term.
  rewrite H_multiple in H_Phi_term.
  contradict H_Phi_term.
  congruence.
- unfold Phi in H_Phi_term.
  rewrite H_multiple in H_Phi_term.
  destruct peers.
  + inversion H_Phi_term.
    congruence.
  + contradict H_Phi_term.
    congruence.
Qed.

Theorem Aggregation : forall
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
  has_type c value value_type ->
  has_type c term term_type.
Proof.
intros c p0 p1 peers value value_type term term_type.
intros H_tie0 H_tie1 H_Phi_term H_phi_term_type H_value_type.
case_eq (getTieMult c (p0, p1)).
- intros multiplicity H_tie.
  destruct multiplicity.
  + unfold phi in H_phi_term_type.
    rewrite H_tie in H_phi_term_type.
    inversion H_phi_term_type as [ H_term_type ].
    apply Aggregation_Multiple with p0 p1 peers value.
    * exact H_tie.
    * exact H_value_type.
    * exact H_Phi_term.
  + unfold phi in H_phi_term_type.
    rewrite H_tie in H_phi_term_type.
    inversion H_phi_term_type as [ H_term_type ].
    apply Aggregation_Optional with p0 p1 peers value.
    * exact H_tie.
    * exact H_value_type.
    * exact H_Phi_term.
  + unfold phi in H_phi_term_type.
    rewrite H_tie in H_phi_term_type.
    inversion H_phi_term_type as [ H_term_type ].
    rewrite <- H_term_type.
    apply Aggregation_Single with p0 p1 peers value.
    * exact H_tie.
    * exact H_value_type.
    * exact H_Phi_term.
  + contradiction.
- contradiction.
Qed.

