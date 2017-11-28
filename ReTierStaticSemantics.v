Require Import ReTierSyntax.
Require Import Maps.

(*
Definition idMap := 
*)

(** Typing environment for reactives, named Psi in informal specification. **)
Definition reactEnv := partial_map r T.
Definition emptyReactEnv: reactEnv := reactEmpty.

(** Typing environment for placed variables, named Delta in informal specification. **)

Definition placeEnv := partial_map id S.
Definition emptyPlaceEnv: placeEnv := idEmpty.

(** Typing environment for normal variables, named Gamma in informal specification. **)
Definition varEnv   := partial_map id T.
Definition emptyVarEnv: varEnv := idEmpty.


(**
 ----------------------------------------------------------------------------
  Below we use the following notation taken from the informal specification.

  Psi   : typing environment for reactives       
  Delta : typing environment for placed variables
  Gamma : typing environment for variables
  P     : current peer
 ----------------------------------------------------------------------------
**)



Reserved Notation "plContext |~ s" (at level 40).



(** Notation seems to work only for at most two arguments on the left.
    Hence we have to encapsulate all environments in an ADT instance.
    See env or context below. **)
Reserved Notation "context '|-' t '\in' T" (at level 40).

(*
Inductive env: Type :=
  | Env: reactEnv -> placeEnv -> varEnv -> env.
*)

(* ----------------------------------------------------------------------- *)

(** context parameter for prop [plt_isWellTyped] **)
Inductive placementContext :=
  | PlacementContext: peerTyping ->Ties -> reactEnv -> placeEnv -> placementContext.
Definition emptyPlContext := PlacementContext noPeers noTies emptyReactEnv emptyPlaceEnv.


(** auxiliary functions for the manipulation of [placementContext] **)
Definition addPlVarDec (x: id) (type: S) (plContext: placementContext): placementContext :=
  match plContext with
  | PlacementContext pT t r pl => PlacementContext pT t r (idUpdate x type pl)
  end.




(* ----------------------------------------------------------------------- *)




(** context for prop [has_type] **)
Inductive context: Type :=
  | Context: peerTyping -> Ties -> reactEnv -> placeEnv -> varEnv -> P -> context.
Definition emptyContext := Context noPeers noTies emptyReactEnv emptyPlaceEnv emptyVarEnv (Peer "dummy").


(** auxiliary functions for the manipulation of [context] **)

(** getters **)
  Definition getVarEnv (c: context): varEnv :=
    match c with
    | Context _ _ _ _ vars _ => vars
    end.

  Definition getPlaceEnv (c: context): placeEnv :=
    match c with
    | Context _ _ _ placedVars _ _ => placedVars
    end.

  Definition getReactEnv (c: context): reactEnv :=
    match c with
    | Context _ _ reactEnv _ _ _ => reactEnv
    end.

  Definition getPeer (c: context): P :=
    match c with
    | Context _ _ _ _ _ p => p
    end.

  Definition getTies (c: context): Ties :=
    match c with
    | Context _ ties _ _ _ _ => ties
    end.

  Definition getTieMult (c: context) (p: P*P): (option multiplicity) :=
    (getTies c) p.

  Definition getPeerType (c: context) (peerInst: p): (option P) :=
    match c with
    | Context peerTyping _ _ _ _ _ => peerTyping peerInst
    end.

  Definition getReactType (c: context) (react: r): (option T) :=
    match c with
    | Context _ _ reactEnv _ _ _ => reactEnv react
    end.

(** add variable declarations to context **)
  Definition addVarDec (x: id) (type: T) (cont: context): context :=
    match cont with
    | Context pT t r pl vars p => Context pT t r pl (idUpdate x type vars) p
    end.


(** conversions from partial data to full [context] **)
  Definition plcToContext (plContext: placementContext) (currentPeer: P): context :=
    match plContext with
    | PlacementContext pT t r pl => Context pT t r pl emptyVarEnv currentPeer
    end.

  Definition reToContext (re: reactEnv) (p: P): context :=
    Context noPeers noTies re emptyPlaceEnv emptyVarEnv p.

  Definition peToContext (pe: placeEnv) (p: P): context :=
    Context noPeers noTies emptyReactEnv pe emptyVarEnv p.

  Definition veToContext (ve: varEnv) (p: P): context :=
    Context noPeers noTies emptyReactEnv emptyPlaceEnv ve p.

  Definition tiesToContext (ties: Ties) (p: P): context :=
    Context noPeers ties emptyReactEnv emptyPlaceEnv emptyVarEnv p.



(** auxiliary functions for aggegation **)

  Definition phi (c: context) (p0 p1: P) (type: T) :=
    match getTieMult c (p0, p1) with
    | Some multiple => Some (List type)
    | Some optional => Some (Option type)
    | Some single   => Some type
    | Some mNone    => None
    | None          => None
    end.



(* --------------------------------------------------------------------- *)


Definition areTied (c: context) (p1 p2: P): bool :=
  match getTieMult c (p1, p2) with
  | None        => false
  | Some mNone  => false
  | Some _      => true
  end.
  


(* TODO: implement rule T-Peer *)

Inductive has_type : context -> t -> T -> Prop :=
  (* rules for local evaluation *)
      | T_Var:  forall context,
                  forall x T,
            ((getVarEnv context) x = Some T \/
             ((getVarEnv context) x = None) /\
              (getPlaceEnv context) x = Some (T on (getPeer context))) ->
            context |- (idApp x) \in T

        | T_App:  forall context,
                  forall t1 t2 T1 T2,
            context |- t1 \in (T2 ~> T1) ->
            context |- t2 \in T2 ->
            context |- app t1 t2 \in T1

        | T_Abs:  forall context,
                  forall x T1 t T2,
            (addVarDec x T1 context) |- t \in T2 ->
            context |- (lambda x T1 t) \in (Arrow T1 T2)

        | T_Cons: forall context,
                  forall t0 t1 T,
            context |- t0 \in T ->
            context |- t1 \in List T ->
            context |- (cons t0 t1) \in List T

        | T_Nil:  forall context,
                  forall T,
            context |- (nil T) \in List T

        | T_Some: forall context,
                  forall t T,
            context |- t \in T ->
            context |- (some t) \in Option T

        | T_None: forall context,
                  forall T,
            context |- none T \in Option T

        | T_Unit: forall context,
            context |- unit \in Unit

        
  (* rules for remote access *)

        | T_Peer: forall context,
                  forall p P1,
            Some P1 = (getPeerType context p) ->
            context |- peerApp p \in Remote P1

        | T_AsLocal: forall context,
                     forall P0 P1 t T0 T1,
            (P0 = (getPeer context)) ->   (* just for better readability *)
            context |- t \in T1 ->
            (areTied context P0 P1) = true ->
            (phi context P0 P1 T1) = Some T0 ->
            context |- (asLocal t (T1 on P1)) \in T0

        | T_AsLocalFrom: forall context,
                         forall P0 P1 t0 t1 T,
            (P0 = (getPeer context)) ->   (* just for better readability *)
            context |- t0 \in T ->
            (areTied context P0 P1) = true ->
            context |- t1 \in Remote P1 ->
            context |- asLocalFrom t0 (T on P1) t1 \in T

        | T_Comp: forall context,
                  forall x t0 t1 T0 T1 T2 P0 P1,
            (P0 = (getPeer context)) ->   (* just for better readability *)
            context |- t0 \in T0 ->
            (addVarDec x T0 context) |- t1 \in T1 ->
            (areTied context P0 P1) = true ->
            Some T2 = (phi context P0 P1 T1) ->
            context |- asLocalIn x t0 t1 (T1 on P1) \in T2

        | T_ComFrom:  forall context,
                      forall x t0 t1 t2 T0 T1 P0 P1,
            (P0 = (getPeer context)) ->   (* just for better readability *)
            context |- t0 \in T0 ->
            (addVarDec x T0 context) |- t1 \in T1 ->
            (areTied context P0 P1) = true ->
            context |- t2 \in Remote P1 ->
            context |- asLocalInFrom x t0 t1 (T1 on P1) t2 \in T1

  (* rules for reactives *)
        | T_Reactive: forall context,
                      forall r T,
            (getReactEnv context) r = Some T -> 
            context |- (reactApp r) \in T

        | T_Signal:   forall context,
                      forall t T,
            context |- t \in T ->
            context |- signal t \in Signal T

        | T_ReactiveVar:  forall context,
                          forall t T,
            context |- t \in T ->
            context |- var t \in Var T

        | T_Now:  forall context,
                  forall t T1 T0,
            (context |- t \in T0) ->
            (T0 = Signal T1 \/ T0 = Var T1) ->
            context |- now t \in T1

        | T_Set:  forall context,
                  forall t1 t2 T,
            context |- t1 \in Var T ->
            context |- t2 \in T ->
            context |- set t1 t2 \in Unit

        | T_Nat:  forall context,
                  forall n: nat,
            context |- tnat n \in Tnat

where "context '|-' t '\in' T" := (has_type context t T).

Hint Constructors has_type.

Inductive plt_isWellTyped : placementContext -> s -> Prop :=
  | T_End:   forall plContext,
      plContext |~ pUnit

  | T_Place: forall plContext,
             forall x T P t s,
      (addPlVarDec x (T on P) plContext) |~ s ->
      (plcToContext plContext P) |- t \in T ->
      (plContext |~ (placed x (T on P) t s))

where "plContext |~ s" := (plt_isWellTyped plContext s).


