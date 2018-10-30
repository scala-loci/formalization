Require Import Maps.
Require Import Syntax.
Require Coq.Lists.List.


Definition placeEnv := partial_map id S.
Definition emptyPlaceEnv: placeEnv := idEmpty.

Definition varEnv := partial_map id T.
Definition emptyVarEnv: varEnv := idEmpty.


Reserved Notation "program :: Psi ; Delta ; Gamma ; P |- t : T"
  (at level 40,
   Psi at next level, Delta at next level, Gamma at next level,
   P at next level, t at next level).

Reserved Notation "program :: Psi ; Delta |- s"
  (at level 40, Psi at next level, Delta at next level).



(** auxiliary functions for aggegation **)

Definition phi (ties: ties) (P0 P1: P) (T: T) :=
  match ties (P0, P1) with
  | Multiple => Datatypes.Some (List T)
  | Optional => Datatypes.Some (Option T)
  | Single   => Datatypes.Some T
  | None     => Datatypes.None
  end.


Definition reactiveEnv := list S.

Definition reactive_type (r: r) (env: reactiveEnv): option S :=
  match r with Reactive n => List.nth_error env n end.

Definition reactive_type_add (S: S) (env: reactiveEnv): r * reactiveEnv :=
  (Reactive (length env), List.app env (Datatypes.cons S Datatypes.nil)).


Inductive typing_t : program -> reactiveEnv -> placeEnv -> varEnv -> P -> t -> T -> Prop :=

  (* rules for local evaluation *)

  | T_Var: forall program Psi Delta Gamma P x T,
      Gamma x = Datatypes.Some T \/ Gamma x = Datatypes.None /\ Delta x = Datatypes.Some (T on P) ->
      program :: Psi; Delta; Gamma; P |- (idApp x) : T

  | T_App: forall program Psi Delta Gamma P t1 t2 T1 T2,
      program :: Psi; Delta; Gamma; P |- t1 : T2 ~> T1 ->
      program :: Psi; Delta; Gamma; P |- t2 : T2 ->
      program :: Psi; Delta; Gamma; P |- app t1 t2 : T1

  | T_Abs: forall program Psi Delta Gamma P x t T1 T2,
      program :: Psi; Delta; idUpdate x T1 Gamma; P |- t : T2 ->
      program :: Psi; Delta; Gamma; P |- lambda x T1 t : T1 ~> T2

  | T_Cons: forall program Psi Delta Gamma P t0 t1 T,
      program :: Psi; Delta; Gamma; P |- t0 : T ->
      program :: Psi; Delta; Gamma; P |- t1 : List T ->
      program :: Psi; Delta; Gamma; P |- cons t0 t1 : List T

  | T_Nil: forall program Psi Delta Gamma P T,
      program :: Psi; Delta; Gamma; P |- nil T : List T

  | T_Some: forall program Psi Delta Gamma P t T,
      program :: Psi; Delta; Gamma; P |- t : T ->
      program :: Psi; Delta; Gamma; P |- some t : Option T

  | T_None: forall program Psi Delta Gamma P T,
      program :: Psi; Delta; Gamma; P |- none T : Option T

  | T_Unit: forall program Psi Delta Gamma P,
      program :: Psi; Delta; Gamma; P |- unit : Unit

  (* rules for remote access *)

  | T_Peer: forall program Psi Delta Gamma P0 P1 theta,
      List.incl theta (peer_instances_of_type program P1) ->
      program :: Psi; Delta; Gamma; P0 |- peerApp theta : Remote P1

  | T_AsLocal: forall program Psi Delta Gamma P0 P1 t T0 T1,
      transmittable_type T1 ->
      program :: Psi; Delta; emptyVarEnv; P1 |- t : T1 ->
      peers_tied program P0 P1 ->
      phi (peer_ties program) P0 P1 T1 = Some T0 ->
      program :: Psi; Delta; Gamma; P0 |- asLocal t (T1 on P1) : T0

  | T_AsLocalFrom: forall program Psi Delta Gamma P0 P1 t0 t1 T,
      transmittable_type T ->
      program :: Psi; Delta; emptyVarEnv; P1 |- t0 : T ->
      peers_tied program P0 P1 ->
      program :: Psi; Delta; Gamma; P0 |- t1 : Remote P1 ->
      program :: Psi; Delta; Gamma; P0 |- asLocalFrom t0 (T on P1) t1 : T

  | T_Comp: forall program Psi Delta Gamma P0 P1 x t0 t1 T0 T1 T2,
      transmittable_type T1 ->
      transmittable_type T0 ->
      program :: Psi; Delta; Gamma; P0 |- t0 : T0 ->
      program :: Psi; Delta; idUpdate x T0 emptyVarEnv; P1 |- t1 : T1 ->
      peers_tied program P0 P1 ->
      phi (peer_ties program) P0 P1 T1 = Some T2 ->
      program :: Psi; Delta; Gamma; P0 |- asLocalIn x T0 t0 t1 (T1 on P1) : T2

  | T_ComFrom: forall program Psi Delta Gamma P0 P1 x t0 t1 t2 T0 T1,
      transmittable_type T1 ->
      transmittable_type T0 ->
      program :: Psi; Delta; Gamma; P0 |- t0 : T0 ->
      program :: Psi; Delta; idUpdate x T0 emptyVarEnv; P1 |- t1 : T1 ->
      peers_tied program P0 P1 ->
      program :: Psi; Delta; Gamma; P0 |- t2 : Remote P1 ->
      program :: Psi; Delta; Gamma; P0 |- asLocalInFrom x T0 t0 t1 (T1 on P1) t2 : T1

  (* rules for reactives *)

  | T_Reactive: forall program Psi Delta Gamma P r T0 T1,
      reactive_type r Psi = Some (T0 on P) ->
      T0 = Signal T1 \/ T0 = Var T1 ->
      program :: Psi; Delta; Gamma; P |- reactApp r : T0

  | T_Signal: forall program Psi Delta Gamma P t T,
      program :: Psi; Delta; Gamma; P |- t : T ->
      program :: Psi; Delta; Gamma; P |- signal t : Signal T

  | T_ReactiveVar: forall program Psi Delta Gamma P t T,
      program :: Psi; Delta; Gamma; P |- t : T ->
      program :: Psi; Delta; Gamma; P |- var t : Var T

  | T_Now: forall program Psi Delta Gamma P t T1 T0,
      program :: Psi; Delta; Gamma; P |- t : T0 ->
      T0 = Signal T1 \/ T0 = Var T1 ->
      program :: Psi; Delta; Gamma; P |- now t : T1

  | T_Set: forall program Psi Delta Gamma P t1 t2 T,
      program :: Psi; Delta; Gamma; P |- t1 : Var T ->
      program :: Psi; Delta; Gamma; P |- t2 : T ->
      program :: Psi; Delta; Gamma; P |- set t1 t2 : Unit

  | T_Nat: forall program Psi Delta Gamma P n,
      program :: Psi; Delta; Gamma; P |- tnat n : Tnat

where "program :: Psi ; Delta ; Gamma ; P |- t : T" := (typing_t program Psi Delta Gamma P t T).


Inductive typing_s : program -> reactiveEnv -> placeEnv -> s -> Prop :=
  | T_End: forall program Psi Delta,
      program :: Psi; Delta |- pUnit

  | T_Place: forall program Psi Delta x t s T P,
      program :: Psi; idUpdate x (T on P) Delta |- s ->
      program :: Psi; Delta; emptyVarEnv; P |- t : T ->
      program :: Psi; Delta |- placed x (T on P) t s

where "program :: Psi ; Delta |- s" := (typing_s program Psi Delta s).
