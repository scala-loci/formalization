Require Import Syntax.
Require Import SemanticsStatic.

Lemma explicit_remote_access: forall t t' T program Psi Delta Gamma P,
  program :: Psi; Delta; Gamma; P |- t : T ->
  is_subterm_t t' t ->
  exists T' Psi' Delta' Gamma' P',
   program :: Psi'; Delta'; Gamma'; P' |- t' : T' /\
   (is_remote_subterm t' t \/ P' = P).
Proof.
intros until P.
pose (term := t).
intros H_typing H_subterm.
destruct H_typing; simpl in H_subterm; subst.
- contradiction.
- destruct H_subterm as [ H_subterm | H_subterm ]; subst.
  + exists (T2 ~> T1), Psi, Delta, Gamma, P.
    split; try assumption.
    right. reflexivity.
  + exists T2, Psi, Delta, Gamma, P.
    split; try assumption.
    right. reflexivity.
- exists T2, Psi, Delta, (idUpdate x T1 Gamma), P.
  split; try assumption.
  right. reflexivity.
- destruct H_subterm as [ H_subterm | H_subterm ]; subst.
  + exists T, Psi, Delta, Gamma, P.
    split; try assumption.
    right. reflexivity.
  + exists (List T), Psi, Delta, Gamma, P.
    split; try assumption.
    right. reflexivity.
- contradiction.
- exists T, Psi, Delta, Gamma, P.
  split; try assumption.
  right. reflexivity.
- contradiction.
- contradiction.
- contradiction.
- exists T1, Psi, Delta, emptyVarEnv, P1.
  split; try assumption.
  left. reflexivity.
- destruct H_subterm as [ H_subterm | H_subterm ]; subst.
  + exists T, Psi, Delta, emptyVarEnv, P1.
    split; try assumption.
    left. reflexivity.
  + exists (Remote P1), Psi, Delta, Gamma, P0.
    split; try assumption.
    right. reflexivity.
- destruct H_subterm as [ H_subterm | H_subterm ]; subst.
  + exists T0, Psi, Delta, Gamma, P0.
    split; try assumption.
    right. reflexivity.
  + exists T1, Psi, Delta, (idUpdate x T0 emptyVarEnv), P1.
    split; try assumption.
    left. reflexivity.
- destruct H_subterm as [ H_subterm | H_subterm ]; subst.
  + exists T0, Psi, Delta, Gamma, P0.
    split; try assumption.
    right. reflexivity.
  + destruct H_subterm as [ H_subterm | H_subterm ]; subst.
    * exists T1, Psi, Delta, (idUpdate x T0 emptyVarEnv), P1.
      split; try assumption.
      left. reflexivity.
    * exists (Remote P1), Psi, Delta, Gamma, P0.
      split; try assumption.
      right. reflexivity.
- contradiction.
- exists T, Psi, Delta, Gamma, P.
  split; try assumption.
  right. reflexivity.
- exists T, Psi, Delta, Gamma, P.
  split; try assumption.
  right. reflexivity.
- exists T0, Psi, Delta, Gamma, P.
  split; try assumption.
  right. reflexivity.
- destruct H_subterm as [ H_subterm | H_subterm ]; subst.
  + exists (Var T), Psi, Delta, Gamma, P.
    split; try assumption.
    right. reflexivity.
  + exists T, Psi, Delta, Gamma, P.
    split; try assumption.
    right. reflexivity.
- contradiction.
Qed.
