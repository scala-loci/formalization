Require Import ReTierSyntax.
Require Import ReTierStaticSemantics.
Require Import ReTierDynamicSemantics.
Require Import Coq.Lists.List.

Definition reactive_index r := match r with Reactive n => n end.

Definition reactive_domain {T: Type} system_or_env := @length T system_or_env.

Definition reactive_system_well_typed program Psi Delta Gamma rho :=
  reactive_domain rho = reactive_domain Psi  /\
  (forall r, reactive_index r < reactive_domain rho ->
    (exists t T T' P,
      reactive_system_lookup r rho = Some t /\
      reactive_type r Psi = Some (T on P) /\
      (T = Var T' \/ T = Signal T') /\
      program :: Psi; Delta; Gamma; P |- t : T')).

Notation "program :: Psi ; Delta ; Gamma |- rho" := (reactive_system_well_typed program Psi Delta Gamma rho)
  (at level 40, Psi at next level, Delta at next level, Gamma at next level).

Definition reactive_env_extends (Psi: reactiveEnv) (Psi': reactiveEnv) :=
  firstn (reactive_domain Psi') Psi = Psi'.

Notation "Psi 'extends' Psi'" := (reactive_env_extends Psi Psi') (at level 40).


(** auxiliary properties for reactive system **)

Proposition reactive_system_update_domain : forall r t rho,
  reactive_domain (reactive_system_update r t rho) = reactive_domain rho.
Proof.
intros until rho.
destruct r.
generalize dependent n.
induction rho; intros; destruct n; try reflexivity.
simpl.
rewrite IHrho.
reflexivity.
Qed.

Proposition reactive_system_lookup_update_eq : forall r t rho,
  reactive_index r < reactive_domain rho ->
  reactive_system_lookup r (reactive_system_update r t rho) = Some t.
Proof.
intros until rho.
intros H_domain.
destruct r.
generalize dependent n.
induction rho; intros.
- inversion H_domain.
- destruct n; try reflexivity.
  apply IHrho.
  simpl in H_domain.
  apply le_S_n in H_domain.
  assumption.
Qed.

Proposition reactive_system_lookup_update_neq : forall r0 r1 t rho,
  r0 <> r1 ->
    reactive_system_lookup r0 (reactive_system_update r1 t rho) =
    reactive_system_lookup r0 rho.
Proof.
intros until rho.
intros H_neq.
destruct r0 as [ n0 ], r1 as [ n1 ].
generalize dependent n1.
generalize dependent rho.
induction n0; intros; destruct rho, n1; try reflexivity.
- congruence.
- apply IHn0.
  congruence.
Qed.

Proposition reactive_system_add_properties : forall rho t, exists r rho',
  reactive_system_add t rho = (r, rho') /\
  r = Reactive (reactive_domain rho) /\
  reactive_domain rho' = Datatypes.S (reactive_domain rho) /\
  reactive_system_lookup r rho' = Some t /\
  forall r, reactive_index r < reactive_domain rho ->
    reactive_system_lookup r rho = reactive_system_lookup r rho'.
Proof.
intros until t.
assert (minus_n_n : forall n, n - n = 0);
  [ > induction n; reflexivity || assumption | ].
exists (Reactive (reactive_domain rho)), (List.app rho (Datatypes.cons t Datatypes.nil)).
unfold reactive_system_add.
rewrite app_length.
simpl.
rewrite <- plus_n_Sm, <- plus_n_O.
repeat split; try reflexivity.
- rewrite nth_error_app2; try reflexivity.
  rewrite minus_n_n.
  reflexivity.
- intros.
  destruct r.
  simpl.
  rewrite nth_error_app1; reflexivity || assumption.
Qed.


(** auxiliary properties for reactive typing environment **)

Proposition reactive_env_add_properties : forall Psi T, exists r Psi',
  reactive_type_add T Psi = (r, Psi') /\
  Psi' extends Psi /\
  r = Reactive (reactive_domain Psi) /\
  reactive_domain Psi' = Datatypes.S (reactive_domain Psi) /\
  reactive_type r Psi' = Some T /\
  forall r, reactive_index r < reactive_domain Psi ->
    reactive_type r Psi = reactive_type r Psi'.
Proof.
intros until T.
assert (minus_n_n : forall n, n - n = 0);
  [ > induction n; reflexivity || assumption | ].
exists (Reactive (reactive_domain Psi)), (List.app Psi (Datatypes.cons T Datatypes.nil)).
unfold reactive_type_add.
rewrite app_length.
simpl.
rewrite <- plus_n_Sm, <- plus_n_O.
repeat split; try reflexivity.
- unfold reactive_env_extends.
  rewrite firstn_app, firstn_all.
  rewrite minus_n_n.
  simpl.
  apply app_nil_r.
- rewrite nth_error_app2; try reflexivity.
  rewrite minus_n_n.
  reflexivity.
- intros.
  destruct r.
  simpl.
  rewrite nth_error_app1; reflexivity || assumption.
Qed.

Proposition reactive_env_extends_type : forall r Psi Psi',
  reactive_index r < reactive_domain Psi ->
  Psi' extends Psi ->
  reactive_type r Psi' = reactive_type r Psi.
Proof.
intros until Psi'.
intros H_domain H_extends.
unfold reactive_env_extends in H_extends.
destruct r.
generalize dependent Psi'.
generalize dependent n.
induction Psi; intros.
- inversion H_domain.
- destruct Psi'; inversion H_extends.
  subst.
  destruct n; try reflexivity.
  simpl in H_extends, H_domain.
  rewrite H_extends.
  apply le_S_n in H_domain.
  simpl.
  apply IHPsi; assumption.
Qed.


(** reactive system typing **)

Lemma reactive_system_lookup_domain : forall r rho,
  reactive_system_lookup r rho <> Datatypes.None <->
  reactive_index r < reactive_domain rho.
Proof.
intros r rho.
destruct r.
simpl.
apply nth_error_Some.
Qed.

Lemma reactive_env_type_domain : forall Psi r,
  reactive_type r Psi <> Datatypes.None <->
  reactive_index r < reactive_domain Psi.
Proof.
intros Psi r.
destruct r.
simpl.
apply nth_error_Some.
Qed.

Lemma reactive_typing_extends_refl : forall Psi,
  Psi extends Psi.
Proof.
intros Psi.
unfold reactive_env_extends.
apply firstn_all.
Qed.

Lemma reactive_typing_weakening_t : forall program Psi Psi' Delta Gamma P t T,
  Psi' extends Psi ->
  program :: Psi; Delta; Gamma; P |- t : T ->
  program :: Psi'; Delta; Gamma; P |- t : T.
Proof.
intros until T.
intros H_extends H_typing.
induction H_typing.
- eapply T_Var; assumption.
- eapply T_App; apply IHH_typing1 || apply IHH_typing2; assumption.
- eapply T_Abs; apply IHH_typing; assumption.
- eapply T_Cons; apply IHH_typing1 || apply IHH_typing2; assumption.
- eapply T_Nil.
- eapply T_Some; apply IHH_typing; assumption.
- eapply T_None.
- eapply T_Unit.
- eapply T_Peer; assumption.
- eapply T_AsLocal; try apply IHH_typing; assumption.
- eapply T_AsLocalFrom; try apply IHH_typing1 || apply IHH_typing2; assumption.
- eapply T_Comp; try apply IHH_typing1 || apply IHH_typing2; assumption.
- eapply T_ComFrom; try apply IHH_typing1 || apply IHH_typing2 || apply IHH_typing3; assumption.
- eapply T_Reactive; try eassumption.
  erewrite reactive_env_extends_type; try eassumption.
  apply reactive_env_type_domain.
  congruence.
- eapply T_Signal; apply IHH_typing; assumption.
- eapply T_ReactiveVar; apply IHH_typing; assumption.
- eapply T_Now; try apply IHH_typing; assumption.
- eapply T_Set; apply IHH_typing1 || apply IHH_typing2; assumption.
- eapply T_Nat.
Qed.

Lemma reactive_typing_weakening_s : forall program Psi Psi' Delta s,
  Psi' extends Psi ->
  program :: Psi; Delta |- s ->
  program :: Psi'; Delta |- s.
Proof.
intros until s.
intros H_extends H_typing.
induction H_typing.
- apply T_End.
- apply T_Place; try (apply IHH_typing; assumption).
  eapply reactive_typing_weakening_t; eassumption.
Qed.

Lemma reactive_typing_update : forall program Psi Delta Gamma rho r P t T,
  program :: Psi; Delta; Gamma |- rho ->
  program :: Psi; Delta; Gamma; P |- t : T ->
  reactive_type r Psi = Some (Var T on P) ->
  program :: Psi; Delta; Gamma |- reactive_system_update r t rho.
Proof.
intros until T.
intros H_reactive_typing H_typing H_reactive_type.
destruct r.
inversion H_reactive_typing as [ H_domain_eq H_well_typed ].
unfold reactive_system_well_typed.
split.
- rewrite <- H_domain_eq.
  apply reactive_system_update_domain.
- intros r H_domain.
  destruct r as [ n' ].
  rewrite reactive_system_update_domain in H_domain.
  assert (H : {n' = n} + {n' <> n}); try decide equality.
  destruct H.
  + subst.
    apply H_well_typed with (Reactive n) in H_domain as H.
    destruct H as [ t0 H ], H as [ T0 H ], H as [ T' H ], H as [ P' H ],
      H as [ H_lookup H ], H as [ H_type H ], H as [ H_reactive H ].
    rewrite H_reactive_type in H_type.
    inversion H_type.
    subst.
    destruct H_reactive as [ H_reactive | ]; try congruence.
    inversion H_reactive.
    subst.
    rewrite reactive_system_lookup_update_eq; try assumption.
    exists t, (Var T'), T', P'.
    repeat split; try reflexivity || assumption.
    left. reflexivity.
  + rewrite reactive_system_lookup_update_neq; try assumption.
    * apply H_well_typed with (Reactive n') in H_domain as H.
      assumption.
    * congruence.
Qed.

Lemma reactive_typing_add : forall program Psi Delta Gamma rho P t T T',
  program :: Psi; Delta; Gamma |- rho ->
  program :: Psi; Delta; Gamma; P |- t : T ->
  T' = Var T \/ T' = Signal T ->
  (exists Psi' rho' r,
   reactive_type_add (T' on P) Psi = (r, Psi') /\
   reactive_system_add t rho = (r, rho') /\
   reactive_type r Psi' = Some (T' on P) /\
   Psi' extends Psi /\
   program :: Psi'; Delta; Gamma |- rho').
Proof.
intros until T'.
intros H_reactive_typing H_typing H_reactive_type.
inversion H_reactive_typing as [ H_domain_eq H_well_typed ].
pose proof reactive_system_add_properties as H_rho.
specialize H_rho with rho t.
destruct H_rho as [ r_rho H_rho ], H_rho as [ rho' H_rho ],
  H_rho as [ H_rho_add H_rho ], H_rho as [ H_rho_reactive H_rho ],
  H_rho as [ H_rho_domain H_rho ], H_rho as [ H_rho_lookup H_rho ].
pose proof reactive_env_add_properties as H_Psi.
specialize H_Psi with Psi (T' on P).
destruct H_Psi as [ r_Psi H_Psi ], H_Psi as [ Psi' H_Psi ],
  H_Psi as [ H_Psi_add H_Psi ], H_Psi as [ H_Psi_extends H_Psi ],
  H_Psi as [ H_Psi_reactive H_Psi ], H_Psi as [ H_Psi_domain H_Psi ],
  H_Psi as [ H_Psi_type H_Psi ].
subst.
exists Psi', rho', (Reactive (reactive_domain rho)).
repeat split.
- rewrite H_domain_eq. assumption.
- assumption.
- rewrite H_domain_eq. assumption.
- assumption.
- rewrite H_domain_eq, <- H_Psi_domain in H_rho_domain.
  assumption.
- intros r H_domain.
  rewrite H_rho_domain in H_domain.
  apply le_S_n in H_domain.
  inversion H_domain as [ H_eq | m H_le H_eq].
  + destruct r.
    simpl in H_eq.
    subst.
    eapply reactive_typing_weakening_t in H_Psi_extends; try eassumption.
    exists t, T', T, P.
    rewrite H_domain_eq at 2.
    repeat split; assumption.
  + apply le_n_S in H_le.
    rewrite H_eq in H_le.
    apply H_well_typed with r in H_le as H.
    destruct H as [ t0 H ], H as [ T0 H ], H as [ T0' H ], H as [ P0 H ],
      H as [ H_lookup H ], H as [ H_type H ], H as [ H_reactive H ].
    apply H_rho in H_le as H_lookup_eq.
    rewrite <- H_lookup_eq.
    rewrite H_domain_eq in H_le.
    apply H_Psi in H_le as H_type_eq.
    rewrite <- H_type_eq.
    eapply reactive_typing_weakening_t  in H_Psi_extends; try eassumption.
    exists t0, T0, T0', P0.
    repeat split; assumption.
Qed.
