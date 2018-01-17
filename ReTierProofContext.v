Require Import ReTierSyntax.
Require Import ReTierStaticSemantics.


Lemma transmittable_value_typing : forall program Psi Delta Delta' Gamma Gamma' P P' v T,
  value v ->
  transmittable_type T ->
  program :: Psi; Delta; Gamma; P |- v : T ->
  program :: Psi; Delta'; Gamma'; P' |- v : T.
Proof.
intros until T.
intros H_value H_transmittable H_typing.
generalize dependent T.
induction v; intros; inversion H_value; inversion H_typing; subst.
- inversion H_transmittable.
- apply T_Unit.
- apply T_None.
- inversion H_transmittable.
  apply T_Some.
  apply IHv; assumption.
- apply T_Nil.
- inversion H_transmittable.
  apply T_Cons.
  + apply IHv1; assumption.
  + apply IHv2; assumption.
- apply T_Peer. assumption.
- apply T_Reactive.
  admit.
- apply T_Nat.
Admitted.


Lemma gamma_typing : forall (Gamma: varEnv) (x: id),
  Gamma x = Datatypes.None \/ (exists T, Gamma x = Datatypes.Some T).
Proof.
intros.
destruct Gamma as [ T' |].
- right. exists T'. reflexivity.
- left. reflexivity.
Qed.


Lemma delta_typing : forall (Delta: placeEnv) (x: id),
  Delta x = Datatypes.None \/ (exists T P, Delta x = Datatypes.Some (T on P)).
Proof.
intros.
destruct Delta.
- right.
  destruct s as [ T' P' ].
  exists T', P'.
  reflexivity.
- left.
  reflexivity.
Qed.


Lemma appears_free_locally_or_remotely : forall t x,
  appears_free_in_t_locality x t RemoteVar ->
  appears_free_in_t_locality x t LocalOrRemoteVar.
Proof.
intros t x H.
induction t; simpl; simpl in H.
- destruct id_dec; try assumption.
  apply IHt in H.
  assumption.
- destruct H.
  + apply IHt1 in H. left. assumption.
  + apply IHt2 in H. right. assumption.
- contradiction.
- contradiction.
- contradiction.
- apply IHt in H. assumption.
- contradiction.
- destruct H.
  + apply IHt1 in H. left. assumption.
  + apply IHt2 in H. right. assumption.
- assumption.
- destruct H.
  + left. assumption.
  + apply IHt2 in H. right. assumption.
- destruct id_dec; destruct H.
  + apply IHt1 in H. left. assumption.
  + right. assumption.
  + apply IHt1 in H. left. assumption.
  + right. assumption.
- destruct id_dec; destruct H.
  + apply IHt1 in H. left. assumption.
  + destruct H.
    * right. left. assumption.
    * apply IHt3 in H. right. right. assumption.
  + apply IHt1 in H. left. assumption.
  + destruct H.
    * right. left. assumption.
    * apply IHt3 in H. right. right. assumption.
- apply IHt in H. assumption.
- apply IHt in H. assumption.
- apply IHt in H. assumption.
- destruct H.
  + apply IHt1 in H. left. assumption.
  + apply IHt2 in H. right. assumption.
- contradiction.
- contradiction.
- contradiction.
Qed.


Lemma free_in_context_t : forall program Psi Delta Gamma P t T x,
  program :: Psi; Delta; Gamma; P |- t : T ->
  (appears_free_in_t_locality x t LocalOrRemoteVar ->
   exists T' P', Gamma x = Some T' \/ Delta x = Some (T' on P')) /\
  (appears_free_in_t_locality x t RemoteVar ->
   exists T' P', Delta x = Some (T' on P')).
Proof.
intros until x.
intros H_typing.
generalize dependent Gamma.
generalize dependent T.
generalize dependent P.
induction t; intros; inversion H_typing; subst; split; intros H_free_x; simpl in H_free_x.
- destruct id_dec.
  + eapply IHt in H_free_x; try eassumption.
    destruct H_free_x as [ T' H_lookup ], H_lookup as [ P' H_lookup ].
    exists T', P'.
    right. assumption.
  + eapply IHt with (Gamma := (idUpdate i t Gamma)) in H_free_x; try eassumption.
    destruct
        H_free_x as [ T' H_lookup ],
        H_lookup as [ P' H_lookup ],
        H_lookup as [ H_lookup | H_lookup ].
    * exists T', P'.
      left.
      rewrite <- H_lookup.
      unfold idUpdate, Maps.p_update, Maps.t_update.
      destruct id_dec; try contradiction.
      reflexivity.
    * exists T', P'.
      right. assumption.
- destruct id_dec.
  + eapply IHt in H_free_x; eassumption.
  + eapply IHt in H_free_x; eassumption.
- destruct H_free_x.
  + eapply IHt1; eassumption.
  + eapply IHt2; eassumption.
- destruct H_free_x.
  + eapply IHt1; eassumption.
  + eapply IHt2; eassumption.
- destruct id_dec.
  + exists T, P.
    subst.
    destruct H5.
    * left. assumption.
    * destruct H.
      right; assumption.
  + contradiction.
- contradiction.
- contradiction.
- contradiction.
- contradiction.
- contradiction.
- eapply IHt; eassumption.
- eapply IHt; eassumption.
- contradiction.
- contradiction.
- destruct H_free_x.
  + eapply IHt1; eassumption.
  + eapply IHt2; eassumption.
- destruct H_free_x.
  + eapply IHt1; eassumption.
  + eapply IHt2; eassumption.
- eapply IHt with (Gamma := emptyVarEnv) in H_free_x; try eassumption.
  destruct
      H_free_x as [ T' H_lookup ],
      H_lookup as [ P' H_lookup ],
      H_lookup as [ H_lookup | H_lookup ].
  + unfold emptyVarEnv, idEmpty, Maps.p_empty in H_lookup.
    congruence.
  + exists T', P'.
    right. assumption.
- eapply IHt with (Gamma := emptyVarEnv) in H_free_x; try eassumption.
  destruct
      H_free_x as [ T' H_lookup ],
      H_lookup as [ P' H_lookup ],
      H_lookup as [ H_lookup | H_lookup ].
  + unfold emptyVarEnv, idEmpty, Maps.p_empty in H_lookup.
    congruence.
  + exists T', P'.
    assumption.
- destruct H_free_x as [ H_free_x | H_free_x ].
  + eapply IHt1 with (Gamma := emptyVarEnv) in H_free_x; try eassumption.
    destruct
        H_free_x as [ T' H_lookup ],
        H_lookup as [ P' H_lookup ],
        H_lookup as [ H_lookup | H_lookup ].
    * unfold emptyVarEnv, idEmpty, Maps.p_empty in H_lookup.
      congruence.
    * exists T', P'.
      right. assumption.
  + eapply IHt2; eassumption.
- destruct H_free_x as [ H_free_x | H_free_x ].
  + eapply IHt1 with (Gamma := emptyVarEnv) in H_free_x; try eassumption.
    destruct
        H_free_x as [ T' H_lookup ],
        H_lookup as [ P' H_lookup ],
        H_lookup as [ H_lookup | H_lookup ].
    * unfold emptyVarEnv, idEmpty, Maps.p_empty in H_lookup.
      congruence.
    * exists T', P'.
      assumption.
  + eapply IHt2; eassumption.
- destruct id_dec.
  + destruct H_free_x as [ H_free_x | H_free_x ].
    * eapply IHt1; eassumption.
    * eapply IHt2 with (Gamma := (idUpdate i T0 emptyVarEnv)) in H_free_x; try eassumption.
      destruct H_free_x as [ T' H_lookup ], H_lookup as [ P' H_lookup ].
      exists T', P'.
      right. assumption.
  + destruct H_free_x as [ H_free_x | H_free_x ].
    * eapply IHt1; eassumption.
    * { eapply IHt2 with (Gamma := (idUpdate i T0 emptyVarEnv)) in H_free_x; try eassumption.
        destruct
            H_free_x as [ T' H_lookup ],
            H_lookup as [ P' H_lookup ],
            H_lookup as [ H_lookup | H_lookup ].
        - unfold
            idUpdate, Maps.p_update, Maps.t_update,
            emptyVarEnv, idEmpty, Maps.p_empty in H_lookup.
          destruct id_dec; try contradiction.
          congruence.
        - exists T', P'.
          right. assumption.
      }
- destruct id_dec.
  + destruct H_free_x.
    * eapply IHt1; eassumption.
    * eapply IHt2; eassumption.
  + destruct H_free_x as [ H_free_x | H_free_x ].
    * eapply IHt1; eassumption.
    * { eapply IHt2 with (Gamma := (idUpdate i T0 emptyVarEnv)) in H_free_x; try eassumption.
        destruct
            H_free_x as [ T' H_lookup ],
            H_lookup as [ P' H_lookup ],
            H_lookup as [ H_lookup | H_lookup ].
        - unfold
            idUpdate, Maps.p_update, Maps.t_update,
            emptyVarEnv, idEmpty, Maps.p_empty in H_lookup.
          destruct id_dec; try contradiction.
          congruence.
        - exists T', P'.
          assumption.
      }
- destruct id_dec.
  * { destruct H_free_x as [ H_free_x | H_free_x ].
      - eapply IHt1; eassumption.
      - destruct H_free_x as [ H_free_x | H_free_x ].
        + eapply IHt2 with (Gamma := (idUpdate i T0 emptyVarEnv)) in H_free_x; try eassumption.
          destruct H_free_x as [ T' H_lookup ], H_lookup as [ P' H_lookup ].
          exists T', P'.
          right. assumption.
        + eapply IHt3; eassumption.
    }
  * { destruct H_free_x as [ H_free_x | H_free_x ].
      - eapply IHt1; eassumption.
      - destruct H_free_x as [ H_free_x | H_free_x ].
        + eapply IHt2 with (Gamma := (idUpdate i T0 emptyVarEnv)) in H_free_x; try eassumption.
          destruct
              H_free_x as [ T' H_lookup ],
              H_lookup as [ P' H_lookup ],
              H_lookup as [ H_lookup | H_lookup ].
          * unfold
              idUpdate, Maps.p_update, Maps.t_update,
              emptyVarEnv, idEmpty, Maps.p_empty in H_lookup.
            destruct id_dec; try contradiction.
            congruence.
          * exists T', P'.
            right. assumption.
        + eapply IHt3; eassumption.
    }
- destruct id_dec.
  + destruct H_free_x as [ H_free_x | H_free_x ].
    * eapply IHt1; eassumption.
    * { destruct H_free_x as [ H_free_x | H_free_x ].
        - eapply IHt2; eassumption.
        - eapply IHt3; eassumption.
      }
  + destruct H_free_x as [ H_free_x | H_free_x ].
    * eapply IHt1; eassumption.
    * { destruct H_free_x as [ H_free_x | H_free_x ].
        - eapply IHt2 with (Gamma := (idUpdate i T0 emptyVarEnv)) in H_free_x; try eassumption.
          destruct
              H_free_x as [ T' H_lookup ],
              H_lookup as [ P' H_lookup ],
              H_lookup as [ H_lookup | H_lookup ].
          + unfold
              idUpdate, Maps.p_update, Maps.t_update,
              emptyVarEnv, idEmpty, Maps.p_empty in H_lookup.
            destruct id_dec; try contradiction.
            congruence.
          + exists T', P'.
            assumption.
        - eapply IHt3; eassumption.
      }
- eapply IHt; eassumption.
- eapply IHt; eassumption.
- eapply IHt; eassumption.
- eapply IHt; eassumption.
- eapply IHt; eassumption.
- eapply IHt; eassumption.
- destruct H_free_x.
  + eapply IHt1; eassumption.
  + eapply IHt2; eassumption.
- destruct H_free_x.
  + eapply IHt1; eassumption.
  + eapply IHt2; eassumption.
- contradiction.
- contradiction.
- contradiction.
- contradiction.
- contradiction.
- contradiction.
Qed.


Lemma free_in_context_s : forall program Psi Delta s x,
   appears_free_in_s x s ->
   program :: Psi; Delta |- s ->
   exists S, Delta x = Some S.
Proof.
intros until x.
intros H_free_x H_typing.
generalize dependent Delta.
induction s; intros; inversion H_typing; subst; simpl in H_free_x.
- destruct id_dec.
  + eapply free_in_context_t in H7 as H_lookup; try eassumption.
    destruct H_lookup as [ H_lookup_Gamma H_lookup_Delta ].
    destruct H_lookup_Gamma as [ T' H_lookup ]. try eassumption.
    destruct
        H_lookup as [ P' H_lookup ],
        H_lookup as [ H_lookup | H_lookup ].
    * unfold emptyVarEnv, idEmpty, Maps.p_empty in H_lookup.
      congruence.
    * exists (T' on P').
      assumption.
  + destruct H_free_x as [ H_free_x | H_free_x ].
    * { eapply free_in_context_t in H7 as H_lookup; try eassumption.
        destruct H_lookup as [ H_lookup_Gamma H_lookup_Delta ].
        destruct H_lookup_Gamma as [ T' H_lookup ]. try eassumption.
        destruct
            H_lookup as [ P' H_lookup ],
            H_lookup as [ H_lookup | H_lookup ].
        - unfold emptyVarEnv, idEmpty, Maps.p_empty in H_lookup.
          congruence.
        - exists (T' on P').
          assumption.
      }
    * { eapply IHs in H_free_x as H_lookup.
        - destruct H_lookup as [ S' H_lookup ].
          exists S'.
          instantiate (1 := (idUpdate i (T on P) Delta)) in H_lookup.
          unfold idUpdate, Maps.p_update, Maps.t_update in H_lookup.
          destruct id_dec; try contradiction.
          assumption.
        - assumption.
      }
- contradiction.
Qed.


Lemma context_invariance_t : forall program Psi Delta Delta' Gamma Gamma' P t T,
  program :: Psi; Delta; Gamma; P |- t : T ->
  (forall x, appears_free_in_t_locality x t LocalOrRemoteVar ->
   Gamma x = Gamma' x /\ (Gamma x = Datatypes.None -> Delta x = Delta' x)) ->
  (forall x, appears_free_in_t_locality x t RemoteVar ->
   Delta x = Delta' x) ->
  program :: Psi; Delta'; Gamma'; P |- t : T.
Proof.
intros until T.
intros H_typing H_free_x_Gamma H_free_x_Delta.
generalize dependent Gamma.
generalize dependent Gamma'.
generalize dependent T.
generalize dependent P.
induction t; intros; inversion H_typing; subst.
- eapply IHt in H8.
  + apply T_Abs. eassumption.
  + intros y H_free_y.
    apply H_free_x_Delta.
    simpl.
    destruct id_dec; assumption.
  + intros y H_free_y.
    unfold idUpdate, Maps.p_update, Maps.t_update.
    destruct id_dec.
    * split; congruence.
    * apply H_free_x_Gamma.
      simpl.
      destruct id_dec; try contradiction.
      assumption.
- eapply IHt1 in H6.
  + eapply IHt2 in H8.
    * eapply T_App; eassumption.
    * intros. apply H_free_x_Delta. simpl. right. assumption.
    * intros. apply H_free_x_Gamma. simpl. right. assumption.
  + intros. apply H_free_x_Delta. simpl. left. assumption.
  + intros. apply H_free_x_Gamma. simpl. left. assumption.
- apply T_Var.
  specialize H_free_x_Gamma with i.
  simpl in H_free_x_Gamma.
  destruct id_dec; try contradiction.
  destruct H_free_x_Gamma as [ H_Gamma H_Gamma_Delta ]; try reflexivity.
  rewrite <- H_Gamma.
  destruct H5 as [ H_lookup_Gamma | H_lookup_Delta ].
  + left. assumption.
  + destruct H_lookup_Delta as [ H_lookup_Gamma H_lookup_Delta ].
    apply H_Gamma_Delta in H_lookup_Gamma as H_Delta.
    rewrite <- H_Delta.
    right. split; assumption.
- apply T_Unit.
- apply T_None.
- eapply IHt in H5.
  + eapply T_Some; eassumption.
  + intros. apply H_free_x_Delta. assumption.
  + intros. apply H_free_x_Gamma. assumption.
- apply T_Nil.
- eapply IHt1 in H6.
  + eapply IHt2 in H8.
    * eapply T_Cons; eassumption.
    * intros. apply H_free_x_Delta. simpl. right. assumption.
    * intros. apply H_free_x_Gamma. simpl. right. assumption.
  + intros. apply H_free_x_Delta. simpl. left. assumption.
  + intros. apply H_free_x_Gamma. simpl. left. assumption.
- eapply IHt in H2.
  + eapply T_AsLocal; eassumption.
  + intros.
    apply H_free_x_Delta.
    simpl.
    apply appears_free_locally_or_remotely in H.
    assumption.
  + intros.
    split; try reflexivity.
    intros.
    apply H_free_x_Delta. simpl. assumption.
- eapply IHt1 in H8.
  + eapply IHt2 in H11.
    * eapply T_AsLocalFrom; eassumption.
    * intros. apply H_free_x_Delta. simpl. right. assumption.
    * intros. apply H_free_x_Gamma. simpl. right. assumption.
  + intros.
    apply H_free_x_Delta.
    simpl.
    left.
    apply appears_free_locally_or_remotely in H.
    assumption.
  + intros.
    split; try reflexivity.
    intros.
    apply H_free_x_Delta. simpl. left. assumption.
- eapply IHt1 in H10.
  + eapply IHt2 in H12.
    * eapply T_Comp; eassumption.
    * { intros y H_free_y.
        apply H_free_x_Delta.
        simpl.
        destruct id_dec.
        - right. assumption.
        - apply appears_free_locally_or_remotely in H_free_y.
          right. assumption.
      }
    * { intros y H_free_y.
        split; try reflexivity.
        intros H_empty.
        apply H_free_x_Delta.
        simpl.
        unfold idUpdate, Maps.p_update, Maps.t_update in H_empty.
        destruct id_dec.
        - congruence.
        - right. assumption.
      }
  + intros y H_free_y.
    apply H_free_x_Delta.
    simpl.
    destruct id_dec; left; assumption.
  + intros y H_free_y.
    apply H_free_x_Gamma.
    simpl.
    destruct id_dec; left; assumption.
- eapply IHt1 in H12.
  + eapply IHt2 in H13.
    * { eapply IHt3 in H15.
        - eapply T_ComFrom; eassumption.
        - intros y H_free_y.
          apply H_free_x_Delta.
          simpl.
          destruct id_dec; right; right; assumption.
        - intros y H_free_y.
          apply H_free_x_Gamma.
          simpl.
          destruct id_dec; right; right; assumption.
      }
    * { intros y H_free_y.
        apply H_free_x_Delta.
        simpl.
        destruct id_dec.
        - right. left. assumption.
        - apply appears_free_locally_or_remotely in H_free_y.
          right. left. assumption.
      }
    * { intros y H_free_y.
        split; try reflexivity.
        intros H_empty.
        apply H_free_x_Delta.
        simpl.
        unfold idUpdate, Maps.p_update, Maps.t_update in H_empty.
        destruct id_dec.
        - congruence.
        - right. left. assumption.
      }
  + intros y H_free_y.
    apply H_free_x_Delta.
    simpl.
    destruct id_dec; left; assumption.
  + intros y H_free_y.
    apply H_free_x_Gamma.
    simpl.
    destruct id_dec; left; assumption.
- eapply IHt in H5.
  + eapply T_Signal; eassumption.
  + intros. apply H_free_x_Delta. assumption.
  + intros. apply H_free_x_Gamma. assumption.
- eapply IHt in H5.
  + eapply T_ReactiveVar; eassumption.
  + intros. apply H_free_x_Delta. assumption.
  + intros. apply H_free_x_Gamma. assumption.
- eapply IHt in H0.
  + eapply T_Now; eassumption.
  + intros. apply H_free_x_Delta. assumption.
  + intros. apply H_free_x_Gamma. assumption.
- eapply IHt1 in H6.
  + eapply IHt2 in H8.
    * eapply T_Set; eassumption.
    * intros. apply H_free_x_Delta. simpl. right. assumption.
    * intros. apply H_free_x_Gamma. simpl. right. assumption.
  + intros. apply H_free_x_Delta. simpl. left. assumption.
  + intros. apply H_free_x_Gamma. simpl. left. assumption.
- apply T_Peer; assumption.
- apply T_Reactive; assumption.
- apply T_Nat.
Qed.


Lemma context_invariance_s : forall program Psi Delta' Delta s,
  program :: Psi; Delta |- s ->
  (forall x, appears_free_in_s x s -> Delta x = Delta' x) ->
  program :: Psi; Delta' |- s.
Proof.
intros until s.
intros H_typing H_free_x.
generalize dependent Delta.
generalize dependent Delta'.
induction s; intros; inversion H_typing; subst.
- eapply IHs in H4.
  + eapply T_Place; try eassumption.
    eapply context_invariance_t; try eassumption; intros.
    * split; try reflexivity.
      intros.
      apply H_free_x.
      simpl.
      destruct id_dec; try assumption.
      left. assumption.
    * apply H_free_x.
      simpl.
      apply appears_free_locally_or_remotely in H.
      destruct id_dec; try assumption.
      left. assumption.
  + intros.
    unfold idUpdate, Maps.p_update, Maps.t_update.
    destruct id_dec; try reflexivity.
    apply H_free_x.
    simpl.
    destruct id_dec; try contradiction.
    right. assumption.
- apply T_End.
Qed.


Lemma typable_empty_closed_t : forall program Psi P t T,
  program :: Psi; emptyPlaceEnv; emptyVarEnv; P |- t : T ->
  closed_t t.
Proof.
unfold closed_t, not.
intros until T.
intros H_typing x H_free_x.
eapply free_in_context_t in H_free_x; try eassumption.
unfold emptyVarEnv, emptyPlaceEnv, idEmpty, Maps.p_empty in H_free_x.
destruct H_free_x as [ T' H_lookup ], H_lookup as [ P' H_lookup ].
destruct H_lookup; congruence.
Qed.


Lemma typable_empty_closed_s : forall program Psi s,
  program :: Psi; emptyPlaceEnv |- s ->
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
