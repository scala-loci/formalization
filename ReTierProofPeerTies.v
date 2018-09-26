Require Import ReTierSyntax.

Lemma mutualTiesSymmetric: forall program P P',
  peers_tied program P P' -> peers_tied program P' P.
Proof.
  intros program P P' H_tied.
  inversion H_tied.
  unfold peers_tied; auto.
Qed.