Require Import ReTierSyntax.
Require Import ReTierStaticSemantics.


Lemma transmittable_value_typing : forall typing ties Psi Delta Delta' Gamma Gamma' P P' t T,
  transmittable_value t ->
  Context typing ties Psi Delta Gamma P |- t \in T ->
  Context typing ties Psi Delta' Gamma' P' |- t \in T.
Proof.
intros until T.
intros H_transmittable H_typing.
generalize dependent T.
induction H_transmittable; intros; inversion H_typing.
- apply T_Unit.
- apply T_None.
- apply T_Some.
  apply IHH_transmittable. assumption.
- apply T_Nil.
- apply T_Cons.
  + apply IHH_transmittable1. assumption.
  + apply IHH_transmittable2. assumption.
- apply T_Peer. assumption.
- apply T_Reactive. assumption.
- apply T_Nat.
Qed.


Lemma free_in_context_t : forall typing ties Psi Delta Gamma P t T x,
   appears_free_in_t x t ->
   Context typing ties Psi Delta Gamma P |- t \in T ->
   exists T', Gamma x = Some T' \/ Delta x = Some (T' on P).
Proof.
intros until x.
intros H_free_x H_typing.
generalize dependent Gamma.
generalize dependent T.
induction t; (intros; inversion H_typing; subst).
- simpl in H_free_x.
  case_eq (beq_id x i); intros H_eq.
  + rewrite H_eq in H_free_x.
    contradiction.
  + rewrite H_eq in H_free_x.
    eapply IHt in H_free_x.
    * { instantiate (1 := (idUpdate i t Gamma)) in H_free_x.
        inversion H_free_x as [ T' H_lookup ].
        destruct H_lookup as [ H_lookup | H_lookup ].
        - exists T'.
          left.
          rewrite <- H_lookup.
          unfold idUpdate, Maps.p_update, Maps.t_update.
          rewrite H_eq.
          reflexivity.
        - exists T'.
          right.
          assumption.
      }
    * unfold addVarDec in H4.
      eassumption.
- destruct H_free_x.
  + eapply IHt1; eassumption.
  + eapply IHt2; eassumption.
- simpl in H_free_x.
  case_eq (beq_id x i); intros H_eq.
  + rewrite beq_id_eq in H_eq.
    subst.
    unfold getVarEnv, getVarEnv, getPlaceEnv, getPeer in H1.
    exists T.
    destruct H1.
    * left. assumption.
    * destruct H.
      right; assumption.
  + rewrite H_eq in H_free_x.
    contradiction.
- contradiction.
- contradiction.
- eapply IHt; eassumption.
- contradiction.
- destruct H_free_x.
  + eapply IHt1; eassumption.
  + eapply IHt2; eassumption.
- eapply IHt; eassumption.
- destruct H_free_x.
  + eapply IHt1; eassumption.
  + eapply IHt2; eassumption.
- simpl in H_free_x.
  case_eq (beq_id x i); intros H_eq.
  + rewrite H_eq in H_free_x.
    eapply IHt1; eassumption.
  + rewrite H_eq in H_free_x.
    destruct H_free_x as [ H_free_x | H_free_x ].
    * eapply IHt1; eassumption.
    * { eapply IHt2 in H_free_x as H_exists_lookup.
        - instantiate (1 := (idUpdate i T0 Gamma)) in H_exists_lookup.
          inversion H_exists_lookup as [ T' H_lookup ].
          destruct H_lookup as [ H_lookup | H_lookup ].
          + exists T'.
            left.
            rewrite <- H_lookup.
            unfold idUpdate, Maps.p_update, Maps.t_update.
            rewrite H_eq.
            reflexivity.
          + exists T'.
            right.
            assumption.
        - unfold addVarDec in H7.
          eassumption.
      }
- simpl in H_free_x.
  case_eq (beq_id x i); intros H_eq.
  + rewrite H_eq in H_free_x.
    destruct H_free_x.
    * eapply IHt1; eassumption.
    * eapply IHt3; eassumption.
  + rewrite H_eq in H_free_x.
    destruct H_free_x as [ H_free_x | H_free_x ].
    * eapply IHt1; eassumption.
    * { destruct H_free_x as [ H_free_x | H_free_x ].
        - eapply IHt2 in H_free_x as H_exists_lookup.
          + instantiate (1 := (idUpdate i T0 Gamma)) in H_exists_lookup.
            inversion H_exists_lookup as [ T' H_lookup ].
            destruct H_lookup as [ H_lookup | H_lookup ].
            * exists T'.
              left.
              rewrite <- H_lookup.
              unfold idUpdate, Maps.p_update, Maps.t_update.
              rewrite H_eq.
              reflexivity.
            * exists T'.
              right.
              assumption.
          + unfold addVarDec in H7.
            eassumption.
        - eapply IHt3; eassumption.
      }
- eapply IHt; eassumption.
- eapply IHt; eassumption.
- eapply IHt; eassumption.
- destruct H_free_x.
  + eapply IHt1; eassumption.
  + eapply IHt2; eassumption.
- contradiction.
- contradiction.
- contradiction.
Qed.


Lemma free_in_context_s : forall typing ties Psi Delta s x,
   appears_free_in_s x s ->
   PlacementContext typing ties Psi Delta |~ s ->
   exists S, Delta x = Some S.
Proof.
intros until x.
intros H_free_x H_typing.
generalize dependent Delta.
induction s; (intros; inversion H_typing; subst).
- simpl in H_free_x.
  case_eq (beq_id x i); intros H_eq.
  + rewrite H_eq in H_free_x.
    eapply free_in_context_t in H5 as H_exists_lookup; try eassumption.
    destruct H_exists_lookup as [ T' H_lookup ].
    destruct H_lookup as [ H_lookup | H_lookup ].
    * unfold emptyVarEnv, idEmpty, Maps.p_empty in H_lookup.
      congruence.
    * exists (T' on P).
      assumption.
  + rewrite H_eq in H_free_x.
    destruct H_free_x as [ H_free_x | H_free_x ].
    * { simpl in *.
        eapply free_in_context_t in H5 as H_exists_lookup; try eassumption.
        destruct H_exists_lookup as [ T' H_lookup ].
        destruct H_lookup as [ H_lookup | H_lookup ].
        - unfold emptyVarEnv, idEmpty, Maps.p_empty in H_lookup.
          congruence.
        - exists (T' on P).
          assumption.
      }
    * { eapply IHs in H_free_x as H_exists_lookup.
        - destruct H_exists_lookup as [ T' H_lookup ].
          exists T'.
          instantiate (1 := (idUpdate i (T on P) Delta)) in H_lookup.
          unfold idUpdate, Maps.p_update, Maps.t_update in H_lookup.
          rewrite H_eq in H_lookup.
          assumption.
        - assumption.
      }
- contradiction.
Qed.


Lemma context_invariance_t : forall typing ties Psi Delta Delta' Gamma Gamma' P t T,
  Context typing ties Psi Delta Gamma P |- t \in T ->
  (forall x, appears_free_in_t x t ->
   Gamma x = Gamma' x /\ (Gamma x = None -> Delta x = Delta' x)) ->
  Context typing ties Psi Delta' Gamma' P |- t \in T.
Proof.
intros until T.
intros H_typing H_free_x.
generalize dependent Gamma.
generalize dependent Gamma'.
generalize dependent T.
induction t; intros; (intros; inversion H_typing).
- eapply IHt in H4.
  + apply T_Abs. simpl. eassumption.
  + intros.
    subst.
    unfold idUpdate, Maps.p_update, Maps.t_update.
    case_eq (beq_id x0 i); intros H_eq.
    * split; congruence.
    * apply H_free_x.
      simpl.
      rewrite H_eq.
      assumption.
- eapply IHt1 in H2.
  + eapply IHt2 in H4.
    * eapply T_App; eassumption.
    * intros. apply H_free_x. simpl. right. assumption.
  + intros. apply H_free_x. simpl. left. assumption.
- simpl in H1.
  apply T_Var.
  simpl.
  specialize H_free_x with i.
  simpl in H_free_x.
  rewrite beq_id_refl in H_free_x.
  destruct H_free_x as [ H_Gamma H_Gamma_Delta ]; try reflexivity.
  rewrite <- H_Gamma.
  destruct H1 as [ H_lookup_Gamma | H_lookup_Delta ].
  + left. assumption.
  + destruct H_lookup_Delta as [ H_lookup_Gamma H_lookup_Delta ].
    apply H_Gamma_Delta in H_lookup_Gamma as H_Delta.
    rewrite <- H_Delta.
    right. split; assumption.
- apply T_Unit.
- apply T_None.
- eapply IHt in H1.
  + eapply T_Some; eassumption.
  + intros. apply H_free_x. assumption.
- apply T_Nil.
- eapply IHt1 in H2.
  + eapply IHt2 in H4.
    * eapply T_Cons; eassumption.
    * intros. apply H_free_x. right. assumption.
  + intros. apply H_free_x. left. assumption.
- eapply IHt in H2.
  + eapply T_AsLocal; eassumption.
  + intros. apply H_free_x. assumption.
- eapply IHt1 in H4.
  + eapply IHt2 in H7.
    * eapply T_AsLocalFrom; eassumption.
    * intros. apply H_free_x. right. assumption.
  + intros. apply H_free_x. left. assumption.
- eapply IHt1 in H5.
  + eapply IHt2 in H7.
    * eapply T_Comp; eassumption.
    * { intros.
        subst.
        unfold idUpdate, Maps.p_update, Maps.t_update.
        case_eq (beq_id x0 i); intros H_eq.
        - split; reflexivity || congruence.
        - apply H_free_x.
          simpl.
          rewrite H_eq.
          right. assumption.
      }
  + intros.
    apply H_free_x.
    simpl.
    case (beq_id x0 i); try assumption.
    left. assumption.
- eapply IHt1 in H7.
  + eapply IHt2 in H8.
    * { eapply IHt3 in H10.
        - eapply T_ComFrom; eassumption.
        - intros.
          apply H_free_x.
          simpl.
          case (beq_id x0 i).
          + right. assumption.
          + right. right. assumption.
      }
    * { intros.
        unfold idUpdate, Maps.p_update, Maps.t_update.
        case_eq (beq_id x0 i); intros H_eq.
        - split; reflexivity || congruence.
        - apply H_free_x.
          simpl.
          rewrite H_eq.
          right. left. assumption.
      }
  + intros.
    apply H_free_x.
    simpl.
    case (beq_id x0 i); left; assumption.
- eapply IHt in H1.
  + eapply T_Signal; eassumption.
  + intros. apply H_free_x. assumption.
- eapply IHt in H1.
  + eapply T_ReactiveVar; eassumption.
  + intros. apply H_free_x. assumption.
- eapply IHt in H0.
  + eapply T_Now; eassumption.
  + intros. apply H_free_x. assumption.
- eapply IHt1 in H2.
  + eapply IHt2 in H4.
    * eapply T_Set; eassumption.
    * intros. apply H_free_x. right. assumption.
  + intros. apply H_free_x. left. assumption.
- apply T_Peer.
  assumption.
- apply T_Reactive.
  assumption.
- apply T_Nat.
Qed.


Lemma context_invariance_s : forall typing ties Psi Delta' Delta s,
  PlacementContext typing ties Psi Delta |~ s ->
  (forall x, appears_free_in_s x s -> Delta x = Delta' x) ->
  PlacementContext typing ties Psi Delta' |~ s.
Proof.
intros until s.
intros H_typing H_free_x.
generalize dependent Delta.
generalize dependent Delta'.
induction s; (intros; inversion H_typing; subst).
- eapply IHs in H2.
  + eapply T_Place; try eassumption.
    simpl.
    eapply context_invariance_t; try eassumption.
    split; try reflexivity.
    unfold emptyVarEnv, idEmpty, Maps.p_empty.
    intros.
    apply H_free_x.
    simpl.
    case (beq_id x i); try assumption.
    left. assumption.
  + intros.
    unfold idUpdate, Maps.p_update, Maps.t_update.
    case_eq (beq_id x i); intros H_eq; try reflexivity.
    apply H_free_x.
    simpl.
    rewrite H_eq.
    right. assumption.
- apply T_End.
Qed.


Lemma typable_empty_closed_t : forall typing ties Psi P t T,
  Context typing ties Psi emptyPlaceEnv emptyVarEnv P |- t \in T ->
  closed_t t.
Proof.
unfold closed_t, not.
intros until T.
intros H_typing x H_free_x.
eapply free_in_context_t in H_free_x; try eassumption.
unfold emptyVarEnv, emptyPlaceEnv, idEmpty, Maps.p_empty in H_free_x.
inversion H_free_x.
destruct H; congruence.
Qed.


Lemma typable_empty_closed_s : forall typing ties Psi s,
  PlacementContext typing ties Psi emptyPlaceEnv |~ s ->
  closed_s s.
Proof.
unfold closed_t, not.
intros until s.
intros H_typing x H_free_x.
eapply free_in_context_s in H_free_x; try eassumption.
unfold emptyPlaceEnv, idEmpty, Maps.p_empty in H_free_x.
inversion H_free_x.
congruence.
Qed.
