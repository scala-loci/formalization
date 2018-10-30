Require Import Syntax.
Require Import SemanticsStatic.
Require Import SemanticsDynamic.
Require Import ProofReactiveSystem.


Definition config_complete program :=
  forall P0 P1,
  ((peer_ties program) (P0, P1) = Single ->
   length (peer_instances_of_type program P1) = 1) /\
  ((peer_ties program) (P0, P1) = Optional ->
   length (peer_instances_of_type program P1) <= 1).


Lemma some_phi: forall program t T P0 P1,
  config_complete program ->
  peers_tied program P0 P1 ->
  exists t', Phi (peer_ties program) P0 P1 (peer_instances_of_type program P1) t T = Some t'.
Proof.
intros until P1.
intros H_complete H_tied.
destruct program as [ ties peers ].
unfold peers_tied in H_tied.
destruct H_tied as [ H_P0_tied H_P1_tied ].
simpl in H_P0_tied.
clear H_P1_tied.
unfold config_complete, peer_ties in H_complete.
destruct (ties (P0, P1)) eqn: H_tie.
- clear H_complete.
  induction (peer_instances_of_type (Program ties peers) P1) as [| p peers' IH_peers ].
  + simpl.
    rewrite H_tie.
    esplit.
    reflexivity.
  + simpl.
    rewrite H_tie.
    destruct IH_peers.
    simpl in H.
    rewrite H.
    esplit.
    reflexivity.
- apply H_complete in H_tie as H_peers_length.
  destruct (peer_instances_of_type (Program ties peers) P1) as [| p peers' ].
  + simpl.
    rewrite H_tie.
    esplit.
    reflexivity.
  + destruct peers'.
    * simpl.
      rewrite H_tie.
      esplit.
      reflexivity.
    * simpl in H_peers_length.
      apply le_S_n in H_peers_length.
      inversion H_peers_length.
- apply H_complete in H_tie as H_peers_length.
  destruct (peer_instances_of_type (Program ties peers) P1) as [| p peers' ].
  + inversion H_peers_length.
  + destruct peers'.
    * simpl.
      rewrite H_tie.
      esplit.
      reflexivity.
    * simpl in H_peers_length.
      congruence.
- congruence.
Qed.


Theorem progress_t: forall t T theta program Psi P rho,
  config_complete program ->
  program :: Psi; emptyPlaceEnv; emptyVarEnv; P |- t : T ->
  program :: Psi; emptyPlaceEnv; emptyVarEnv |- rho ->
  value_t t \/ exists t' theta' rho', program :: theta : P |> t; rho == theta' ==> t'; rho'.
Proof.
intros until rho.
intros H_complete H_typing H_reactive_typing.
remember emptyPlaceEnv as Delta.
remember emptyVarEnv as Gamma.
generalize dependent theta.
induction H_typing; intros; subst.
- destruct H.
  + unfold emptyVarEnv, idEmpty, Maps.p_empty in H.
    congruence.
  + destruct H.
    unfold emptyPlaceEnv, idEmpty, Maps.p_empty in H0.
    congruence.
- edestruct IHH_typing1; try assumption || reflexivity.
  + edestruct IHH_typing2; try assumption || reflexivity.
    * { inversion H; subst; inversion H_typing1; subst.
        - right. repeat esplit.
          apply E_App. assumption.
        - destruct H8; congruence.
      }
    * destruct H0 as [ t2' ], H0 as [ theta' ], H0 as [ rho' ].
      right. repeat esplit.
      apply EC_App_Right; eassumption.
  + destruct H as [ t1' ], H as [ theta' ], H as [ rho' ].
    right. repeat esplit.
    apply EC_App_Left. eassumption.
- left. apply v_lambda.
- edestruct IHH_typing1; try assumption || reflexivity.
  + edestruct IHH_typing2; try assumption || reflexivity.
    * left. apply v_cons; assumption.
    * destruct H0 as [ t1' ], H0 as [ theta' ], H0 as [ rho' ].
      right. repeat esplit.
      apply EC_Cons_Right; eassumption.
  + destruct H as [ t0' ], H as [ theta' ], H as [ rho' ].
    right. repeat esplit.
    apply EC_Cons_Left. eassumption.
- left. apply v_nil.
- edestruct IHH_typing; try assumption || reflexivity.
  + left. apply v_some. assumption.
  + destruct H as [ t' ], H as [ theta' ], H as [ rho' ].
    right. repeat esplit.
    apply EC_Some. eassumption.
- left. apply v_none.
- left. apply v_unit.
- left. apply v_peerApp.
- edestruct IHH_typing; try assumption || reflexivity.
  + pose proof some_phi.
    eapply H3 in H0; try assumption.
    destruct H0 as [ t' ].
    right. repeat esplit.
    eapply E_AsLocal; eassumption.
  + destruct H2 as [ t' ], H2 as [ theta' ], H2 as [ rho' ].
    right. repeat esplit.
    apply E_Remote. eassumption.
- edestruct IHH_typing2; try assumption || reflexivity.
  + inversion H1; subst; inversion H_typing2; subst.
    * { edestruct IHH_typing1; try assumption || reflexivity.
        - right. repeat esplit.
          apply E_AsLocalFrom; assumption || reflexivity.
        - destruct H2 as [ t0' ], H2 as [ theta' ], H2 as [ rho' ].
          right. repeat esplit.
          apply E_RemoteFrom. eassumption.
      }
    * destruct H9; congruence.
  + destruct H1 as [ t1' ], H1 as [ theta' ], H1 as [ rho' ].
    right. repeat esplit.
    apply EC_AsLocalFrom. eassumption.
- edestruct IHH_typing1; try assumption || reflexivity.
  + right. repeat esplit.
    apply E_Comp; assumption || reflexivity.
  + destruct H3 as [ t0' ], H3 as [ theta' ], H3 as [ rho' ].
    right. repeat esplit.
    apply EC_Comp. eassumption.
- edestruct IHH_typing3; try assumption || reflexivity.
  + inversion H2; subst; inversion H_typing3; subst.
    * { edestruct IHH_typing1; try assumption || reflexivity.
        - right. repeat esplit.
          apply E_CompFrom; assumption || reflexivity.
        - destruct H3 as [ t0' ], H3 as [ theta' ], H3 as [ rho' ].
          right. repeat esplit.
          apply EC_CompFrom_Left; eassumption.
      }
    * destruct H10; congruence.
  + destruct H2 as [ t2' ], H2 as [ theta' ], H2 as [ rho' ].
    right. repeat esplit.
    apply EC_CompFrom_Right. eassumption.
- left. apply v_reactApp.
- right. repeat esplit.
  eapply E_Signal.
  reflexivity.
- edestruct IHH_typing; try assumption || reflexivity.
  + right. repeat esplit.
    apply E_ReactiveVar; assumption || reflexivity.
  + destruct H as [ t' ], H as [ theta' ], H as [ rho' ].
    right. repeat esplit.
    eapply EC_Var. eassumption.
- edestruct IHH_typing; try assumption || reflexivity.
  + inversion H0; subst; inversion H_typing; subst;
      try solve [ destruct H; congruence ].
    unfold reactive_system_well_typed in H_reactive_typing.
    destruct H_reactive_typing as [ H1 H3 ].
    specialize H3 with r.
    assert (reactive_type r Psi <> Datatypes.None).
    * congruence.
    * apply reactive_env_type_domain in H4.
      rewrite <- H1 in H4.
      apply H3 in H4.
      destruct H4 as [ t' ], H4 as [ T' ], H4 as [ T'' ], H4 as [ P' ], H4.
      right. repeat esplit.
      eapply E_Now. eassumption.
  + destruct H0 as [ t' ], H0 as [ theta' ], H0 as [ rho' ].
    right. repeat esplit.
    eapply EC_Now. eassumption.
- edestruct IHH_typing1; try assumption || reflexivity.
  + edestruct IHH_typing2; try assumption || reflexivity.
    * inversion H; subst; inversion H_typing1; subst.
      right. repeat esplit.
      eapply E_Set; assumption || reflexivity.
    * destruct H0 as [ t2' ], H0 as [ theta' ], H0 as [ rho' ].
      right. repeat esplit.
      apply EC_Set_Right; eassumption.
  + destruct H as [ t1' ], H as [ theta' ], H as [ rho' ].
    right. repeat esplit.
    apply EC_Set_Left. eassumption.
- left. apply v_tnat.
Qed.


Theorem progress_s: forall s program Psi rho,
  config_complete program ->
  program :: Psi; emptyPlaceEnv |- s ->
  program :: Psi; emptyPlaceEnv; emptyVarEnv |- rho ->
  value_s s \/ exists s' theta rho', program :: s; rho == theta ==> s'; rho'.
Proof.
intros until rho.
intros H_complete H_typing H_reactive_typing.
remember emptyPlaceEnv as Delta.
destruct H_typing; intros; subst.
- left. apply v_pUnit.
- eapply progress_t in H_complete; try eassumption.
  destruct H_complete.
  + right. repeat esplit.
    apply E_Placed_Val.
    assumption.
  + destruct H0 as [ t' ], H0 as [ theta' ], H0 as [ rho' ].
    right. repeat esplit.
    eapply E_Placed.
    eassumption.
Qed.
