Require Import Syntax.
Require Import SemanticsStatic.
Require Import SemanticsDynamic.

Lemma static_placement_t: forall t_i t t' T program Psi Delta Gamma P theta theta' rho rho',
  program :: Psi; Delta; Gamma; P |- t : T ->
  program :: theta : P |> t; rho == theta' ==> t'; rho' ->
  List.incl theta (peer_instances_of_type program P) ->
  is_reducing_subterm_t t_i t ->
  (exists t_i' T_i Psi_i Delta_i Gamma_i P_i P_i' theta_i theta_i' rho_i rho_i',
   program :: Psi_i; Delta_i; Gamma_i; P_i |- t_i : T_i /\
   program :: theta_i : P_i' |> t_i; rho_i == theta_i' ==> t_i'; rho_i' /\
   List.incl theta_i (peer_instances_of_type program P_i') /\
   P_i = P_i').
Proof.
intros until rho'.
intros H_typing H_eval H_subset H_subterm.
assert (no_value_reduction:
  forall t t' program P theta theta' rho rho',
  program :: theta : P |> t; rho == theta' ==> t'; rho' -> ~ value_t t);
  [ > intros; induction H; intro; solve [ inversion H0; contradiction | inversion H1; contradiction ] | ].
destruct H_typing; simpl in H_subterm; subst.
- contradiction.
- destruct H_subterm as [ H_subterm | H_subterm ].
  + destruct H_subterm as [ H_subterm H_subterm_no_value ].
    inversion H_eval; subst.
    * exists t0', (T2 ~> T1), Psi, Delta, Gamma, P, P, theta, theta', rho, rho'.
      repeat split; reflexivity || assumption.
    * contradiction.
    * contradict H_subterm_no_value.
      apply v_lambda.
  + destruct
      H_subterm as [ H_subterm H_subterm_value ],
      H_subterm_value as [ H_subterm_no_value H_subterm_value ].
    inversion H_eval; subst.
    * apply no_value_reduction in H8.
      contradiction.
    * exists t1', T2, Psi, Delta, Gamma, P, P, theta, theta', rho, rho'.
      repeat split; reflexivity || assumption.
    * contradiction.
- contradiction.
- destruct H_subterm as [ H_subterm | H_subterm ].
  + destruct H_subterm as [ H_subterm H_subterm_no_value ].
    inversion H_eval; subst.
    * exists t0', T, Psi, Delta, Gamma, P, P, theta, theta', rho, rho'.
      repeat split; reflexivity || assumption.
    * contradiction.
  + destruct
      H_subterm as [ H_subterm H_subterm_value ],
      H_subterm_value as [ H_subterm_no_value H_subterm_value ].
    inversion H_eval; subst.
    * apply no_value_reduction in H8.
      contradiction.
    * exists t1', (List T), Psi, Delta, Gamma, P, P, theta, theta', rho, rho'.
      repeat split; reflexivity || assumption.
- contradiction.
- destruct H_subterm.
  inversion H_eval; subst.
  exists t'0, T, Psi, Delta, Gamma, P, P, theta, theta', rho, rho'.
  repeat split; reflexivity || assumption.
- contradiction.
- contradiction.
- contradiction.
- destruct H_subterm.
  inversion H_eval; subst.
  + contradiction.
  + exists t'0, T1, Psi, Delta, emptyVarEnv, P1, P1, (peer_instances_of_type program P1), theta', rho, rho'.
    repeat split; try reflexivity || assumption.
    apply List.incl_refl.
- destruct H_subterm as [ H_subterm | H_subterm ].
  + destruct
      H_subterm as [ H_subterm H_subterm_value ],
      H_subterm_value as [ H_subterm_no_value H_subterm_value ].
    inversion H_eval; subst.
    * apply no_value_reduction in H11.
      contradiction.
    * contradiction.
    * exists t'0, T, Psi, Delta, emptyVarEnv, P1, P1, theta'', theta', rho, rho'.
      inversion H_typing2.
      repeat split; try reflexivity || assumption.
  + destruct H_subterm as [ H_subterm H_subterm_no_value ].
    inversion H_eval; subst.
    * exists t1', (Remote P1), Psi, Delta, Gamma, P0, P0, theta, theta', rho, rho'.
      repeat split; reflexivity || assumption.
    * contradict H_subterm_no_value.
      apply v_peerApp.
    * contradict H_subterm_no_value.
      apply v_peerApp.
- destruct H_subterm as [ H_subterm H_subterm_no_value ].
  inversion H_eval; subst.
  + exists t0', T0, Psi, Delta, Gamma, P0, P0, theta, theta', rho, rho'.
    repeat split; reflexivity || assumption.
  + contradiction.
- destruct H_subterm as [ H_subterm | H_subterm ].
  + destruct
      H_subterm as [ H_subterm H_subterm_value ],
      H_subterm_value as [ H_subterm_no_value H_subterm_value ].
    inversion H_eval; subst.
    * apply no_value_reduction in H15.
      contradiction.
    * exists t0', T0, Psi, Delta, Gamma, P0, P0, theta, theta', rho, rho'.
      repeat split; reflexivity || assumption.
    * contradiction.
  + destruct H_subterm as [ H_subterm H_subterm_no_value ].
    inversion H_eval; subst.
    * exists t2', (Remote P1), Psi, Delta, Gamma, P0, P0, theta, theta', rho, rho'.
      repeat split; reflexivity || assumption.
    * contradiction.
    * contradict H_subterm_no_value.
      apply v_peerApp.
- contradiction.
- contradiction.
- destruct H_subterm.
  inversion H_eval; subst.
  * exists t'0, T, Psi, Delta, Gamma, P, P, theta, theta', rho, rho'.
    repeat split; reflexivity || assumption.
  * contradiction.
- destruct H_subterm.
  inversion H_eval; subst.
  * exists t'0, T0, Psi, Delta, Gamma, P, P, theta, theta', rho, rho'.
    repeat split; reflexivity || assumption.
  * contradict H1.
    apply v_reactApp.
- destruct H_subterm as [ H_subterm | H_subterm ].
  + destruct H_subterm as [ H_subterm H_subterm_no_value ].
    inversion H_eval; subst.
    * exists t0', (Var T), Psi, Delta, Gamma, P, P, theta, theta', rho, rho'.
      repeat split; reflexivity || assumption.
    * contradiction.
    * contradict H_subterm_no_value.
      apply v_reactApp.
  + destruct
      H_subterm as [ H_subterm H_subterm_value ],
      H_subterm_value as [ H_subterm_no_value H_subterm_value ].
    inversion H_eval; subst.
    * apply no_value_reduction in H8.
      contradiction.
    * exists t1', T, Psi, Delta, Gamma, P, P, theta, theta', rho, rho'.
      repeat split; reflexivity || assumption.
    * contradiction.
- contradiction.
Qed.


Lemma static_placement_s: forall t_i s s' program Psi Delta theta rho rho',
  program :: Psi; Delta |- s ->
  program :: s; rho == theta ==> s'; rho' ->
  is_reducing_subterm_s t_i s ->
  (exists t_i' T_i Psi_i Delta_i Gamma_i P_i P_i' theta_i theta_i' rho_i rho_i',
   program :: Psi_i; Delta_i; Gamma_i; P_i |- t_i : T_i /\
   program :: theta_i : P_i' |> t_i; rho_i == theta_i' ==> t_i'; rho_i' /\
   List.incl theta_i (peer_instances_of_type program P_i') /\
   P_i = P_i').
Proof.
intros until rho'.
intros H_typing H_eval H_subterm.
destruct H_typing; simpl in H_subterm; subst.
- contradiction.
- destruct H_subterm as [ H_subterm H_subterm_no_value ].
  inversion H_eval; subst.
  + exists t', T, Psi, Delta, emptyVarEnv, P, P, (peer_instances_of_type program P), theta, rho, rho'.
    repeat split; try reflexivity || assumption.
    apply List.incl_refl.
  + contradiction.
Qed.
