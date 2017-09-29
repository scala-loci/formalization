Require Import ReTierSyntax.
Require Import Maps.

(*
Definition idMap := 
*)

(** Typing environment for reactives, named Psi in informal specification. **)
Definition reactEnv := partial_map id T.
Definition emptyReactEnv: reactEnv := idEmpty.

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
  | PlacementContext pT t r pl => PlacementContext pT t r (update x type pl)
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

  Definition getTieMult (c: context) (p: P*P): (option multiplicity) :=
    match c with
    | Context _ ties _ _ _ _ => ties p
    end.

  Definition getPeerType (c: context) (peerInst: p): (option P) :=
    match c with
    | Context peerTyping _ _ _ _ _ => peerTyping peerInst
    end.

  Definition getReactType (c: context) (r: id): (option T) :=
    match c with
    | Context _ _ reactEnv _ _ _ => reactEnv r
    end.

(** add variable declarations to context **)
  Definition addVarDec (x: id) (type: T) (cont: context): context :=
    match cont with
    | Context pT t r pl vars p => Context pT t r pl (update x type vars) p
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

Inductive plt_isWellTyped : placementContext -> s -> Prop :=
  | T_End:   forall plContext,
      plContext |~ pUnit

  | T_Place: forall plContext,
             forall x T P t s,
      (addPlVarDec x (T on P) plContext) |~ s ->
      (plcToContext plContext P) |- t \in T ->
      (plContext |~ (placed x (T on P) t s))

where "plContext |~ s" := (plt_isWellTyped plContext s)

  with  has_type : context -> t -> T -> Prop :=
  (* rules for local evaluation *)
      | T_Var:  forall context,
                  forall x T,
            ((getVarEnv context) x = Some T \/ (getPlaceEnv context ) x = Some (T on (getPeer context))) ->
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
            context |- interPeerApp p \in Remote P1

        | T_AsLocal: forall context,
                     forall P0 P1 t T0 T1,
            (P0 = (getPeer context)) ->   (* just for better readability *)
            context |- t \in T1 ->
            (areTied context P0 P1) = true ->
            (phi context P0 P1 T1) = Some T0 ->
            context |- (interAsLocalTerm t (T1 on P1)) \in T0

        (* Added because missing in informal specification.
           TODO: Check if necessary!
              In informal specification no explicit rule for 'asLocal x : T1 on P1'
              exists. Rule T_AsLocal talks about terms in general and therefore 
              implicitely about variables. The BNF syntax specification contains separate
              'asLocal x: S' and 'asLocal t: S' productions. While the former one may
              occur in regular programs the latter one may only occur as an intermediate
              result during evaluation.
              => Hence we need separate rules in Coq-formalization.
        *)
        | T_AsLocalVar: forall context,
                        forall P0 P1 x T0 T1,
            (P0 = (getPeer context)) ->   (* just for better readability *)
            (areTied context P0 P1) = true ->
            (phi context P0 P1 T1) = Some T0 ->
            context |- (asLocal x (T1 on P1)) \in T0

        | T_AsLocalFrom: forall context,
                         forall P0 P1 t0 t1 T,
            (P0 = (getPeer context)) ->   (* just for better readability *)
            context |- t0 \in T ->
            (areTied context P0 P1) = true ->
            context |- t1 \in Remote P1 ->
            context |- interAsLocalTermFrom t0 (T on P1) t1 \in T

        (* Added because missing in informal specification.
           TODO: Check if necessary!
           See description for [T_AsLocalVar].
         *)
        | T_AsLocalFromVar: forall context,
                            forall P0 P1 x t1 T,
            (P0 = (getPeer context)) ->   (* just for better readability *)
            (areTied context P0 P1) = true ->
            context |- t1 \in Remote P1 ->
            context |- asLocalFrom x (T on P1) t1 \in T

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
            context |- (idApp r) \in T

        | T_Signal:   forall context,
                      forall t T,
            context |- t \in T ->
            context |- signal t \in Signal T

        | T_ReactiveVar:  forall context,
                          forall t T,
            context |- t \in T ->
            context |- var t \in Var T

        | T_Now:  forall context,
                  forall t T,
            (context |- t \in Signal T \/ context |- t \in Var T) ->
            context |- now t \in T

        | T_Set:  forall context,
                  forall t1 t2 T,
            context |- t1 \in Var T ->
            context |- t2 \in T ->
            context |- set t1 t2 \in Unit

where "context '|-' t '\in' T" := (has_type context t T).





(* -------------------------------------------------------------------------
  Tests
 * -------------------------------------------------------------------------*)





(** In the following [plt_isWellTyped] and [has_type] are tested.
  The tests are ordered such that every test case's proof only relies on tested
  inference rules.
**)


Definition testPsi1: reactEnv   := update (Id "r") Unit idEmpty.
Definition testGamma1: varEnv   := update (Id "x") Tnat (update (Id "y") Unit idEmpty).
Definition testDelta1: placeEnv := update (Id "x") (Unit on (Peer "px")) idEmpty.
Definition testPlCont1_NoTies := PlacementContext noPeers noTies testGamma1 testDelta1.
Definition testTies1  :=  (tie_update (Peer "p0" *-> Peer "pm")
                            (tie_update (Peer "p0" ?-> Peer "po")
                              (tie_update (Peer "p0" S-> Peer "ps")
                                (tie_update ((Peer "p0") N-> (Peer "pn"))
                                  noTies)))).
Definition testPeerTyping1 := (pT_update (PeerInst 4) (Peer "pm")
                                (pT_update (PeerInst 3) (Peer "po")
                                  (pT_update (PeerInst 2) (Peer "ps")
                                    (pT_update (PeerInst 1) (Peer "pn")
                                      (pT_update (PeerInst 0) (Peer "p0")
                                      noPeers))))).
Definition testTies1Context := tiesToContext testTies1 (Peer "p0").
Definition testPeerTyping1Ties1Context := 
              Context testPeerTyping1 testTies1 emptyReactEnv emptyPlaceEnv emptyVarEnv (Peer "p0").
Definition testReactContext1 := reToContext testPsi1 (Peer "_").


Example test_pltIsWellTyped_TEnd_1: emptyPlContext |~ pUnit.
Proof. apply T_End. Qed.


Example test_pltIsWellTyped_TEnd_2: testPlCont1_NoTies |~ pUnit.
Proof. apply T_End. Qed.


(* Tested earlier because next test's proof relies inference rule T_Unit it. *)
Example test_hasType_TUnit_1: (emptyContext |- unit \in Unit).
Proof. apply T_Unit. Qed.


Example test_pltIsWellTyped_TPlace_1:
  testPlCont1_NoTies |~ (placed (Id "x") (Unit on (Peer "px")) unit pUnit).
Proof.
  apply T_Place.
  - apply T_End.
  - apply T_Unit.
Qed.


Example test_hasType_TVar_normalVar_1: 
    (veToContext testGamma1 (Peer "p1")) |- (idApp (Id "x")) \in Tnat.
Proof. apply T_Var. left. reflexivity. Qed.


Example test_hasType_TVar_placedVar_2:
    (peToContext testDelta1 (Peer "px")) |- (idApp (Id "x")) \in Unit.
Proof. apply T_Var. right. reflexivity. Qed.


Example test_hasType_TAbs_1: 
    emptyContext |- (lambda (Id "x") Tnat unit) \in (Arrow Tnat Unit).
Proof. apply T_Abs. apply T_Unit. Qed.


Example test_hasType_TAbs_2: 
    emptyContext |- (lambda (Id "x") Tnat (idApp (Id "x"))) \in (Arrow Tnat Tnat).
Proof. apply T_Abs. apply T_Var. left. reflexivity. Qed.


(** Tests variable shadowing **)
Example test_hasType_TAbs_3:  
    (testGamma1 (Id "x")) = Some Tnat /\ (veToContext testGamma1 (Peer "_"))
    |- (lambda (Id "x") Unit (idApp (Id "x"))) \in (Arrow Unit Unit).
Proof.
  split.
  - reflexivity.
  - apply T_Abs. apply T_Var. left. reflexivity.
Qed.


Example test_hasType_TApp_1:
    emptyContext |- (app (lambda (Id "x") Unit unit) unit) \in Unit.
Proof.
  apply T_App with (T2 := Unit).
  - apply T_Abs. apply T_Unit.
  - apply T_Unit.
Qed.


Example test_hasType_TApp_2: 
    emptyContext |- (app (lambda (Id "x") Unit (idApp (Id "x"))) unit) \in Unit.
Proof.
  apply T_App with (T2 := Unit).
  - apply T_Abs. apply T_Var. left. reflexivity.
  - apply T_Unit.
Qed.


Example test_hasType_TNil_1: 
    emptyContext |- (nil Unit) \in List Unit.
Proof. apply T_Nil. Qed.


Example test_hasType_TCons_1: 
    emptyContext |- (cons unit (nil Unit)) \in List Unit.
Proof.
  apply T_Cons.
  - apply T_Unit.
  - apply T_Nil.
Qed.


Example test_hasType_TSome_1: 
    emptyContext |- (some unit) \in Option Unit.
Proof. apply T_Some. apply T_Unit. Qed.


Example test_hasType_TNone_1: 
    emptyContext |- (none Unit) \in Option Unit.
Proof. apply T_None. Qed.


Example test_hasType_TPeer_1:
    (* ensure test setup is correct ... *)
    getPeerType testPeerTyping1Ties1Context (PeerInst 0) = Some (Peer "p0") /\
    (* actual test ... *)
    testPeerTyping1Ties1Context |- interPeerApp (PeerInst 0) \in Remote (Peer "p0").
Proof.
  split.
  - reflexivity.
  - apply T_Peer. reflexivity.
Qed.


Example test_hasType_TAsLocalVar_single_1:
    (* ensure test setup is correct ... *)
    getPeer testTies1Context = Peer "p0" /\
    getTieMult testTies1Context (Peer "p0", Peer "ps") = Some single /\
    (* actual test ... *)
    testTies1Context |- (asLocal (Id "x") (Unit on (Peer "ps"))) \in Unit.
Proof.
  split.
  - reflexivity.  (* current peer set correctly *)
  - split.
    + reflexivity.  (* ties set up correctly *)
    + { apply T_AsLocalVar with (P0 := (Peer "p0")).
        - reflexivity.
        - reflexivity.
        - reflexivity.
      }
Qed.


Example test_hasType_TAsLocalVar_optional_1:
    (* ensure test setup is correct ... *)
    getPeer testTies1Context = Peer "p0" /\
    getTieMult testTies1Context (Peer "p0", Peer "po") = Some optional /\
    (* actual test ... *)
    testTies1Context |- (asLocal (Id "x") (Unit on (Peer "po"))) \in Option Unit.
Proof.
  split.
  - reflexivity.  (* current peer set correctly *)
  - split.
    + reflexivity.  (* ties set up correctly *)
    + { apply T_AsLocalVar with (P0 := (Peer "p0")).
        - reflexivity.
        - reflexivity.
        - reflexivity.
      }
Qed.


Example test_hasType_TAsLocalVar_multiple_1:
    (* ensure test setup is correct ... *)
    getPeer testTies1Context = Peer "p0" /\
    getTieMult testTies1Context (Peer "p0", Peer "pm") = Some multiple /\
    (* actual test ... *)
    testTies1Context |- (asLocal (Id "x") (Unit on (Peer "pm"))) \in List Unit.
Proof.
  split.
  - reflexivity.  (* current peer set correctly *)
  - split.
    + reflexivity.  (* ties set up correctly *)
    + { apply T_AsLocalVar with (P0 := (Peer "p0")).
        - reflexivity.
        - reflexivity.
        - reflexivity.
      }
Qed.

Example test_hasType_TAsLocal_single_1:
    (* ensure test setup is correct ... *)
    getPeer testTies1Context = Peer "p0" /\
    getTieMult testTies1Context (Peer "p0", Peer "ps") = Some single /\
    (* actual test ... *)
    testTies1Context |- (interAsLocalTerm unit (Unit on (Peer "ps"))) \in Unit.
Proof.
  split.
  - reflexivity.  (* current peer set correctly *)
  - split.
    + reflexivity.  (* ties set up correctly *)
    + { apply T_AsLocal with (P0 := (Peer "p0")).
        - reflexivity.
        - apply T_Unit.
        - reflexivity.
        - reflexivity.
      }
Qed.


Example test_hasType_TAsLocal_optional_1:
    (* ensure test setup is correct ... *)
    getPeer testTies1Context = Peer "p0" /\
    getTieMult testTies1Context (Peer "p0", Peer "po") = Some optional /\
    (* actual test ... *)
    testTies1Context |- (interAsLocalTerm unit (Unit on (Peer "po"))) \in Option Unit.
Proof.
  split.
  - reflexivity.  (* current peer set correctly *)
  - split.
    + reflexivity.  (* ties set up correctly *)
    + { apply T_AsLocal with (P0 := (Peer "p0")).
        - reflexivity.
        - apply T_Unit.
        - reflexivity.
        - reflexivity.
      }
Qed.


Example test_hasType_TAsLocal_multiple_1:
    (* ensure test setup is correct ... *)
    getPeer testTies1Context = Peer "p0" /\
    getTieMult testTies1Context (Peer "p0", Peer "pm") = Some multiple /\
    (* actual test ... *)
    testTies1Context |- (interAsLocalTerm unit (Unit on (Peer "pm"))) \in List Unit.
Proof.
  split.
  - reflexivity.  (* current peer set correctly *)
  - split.
    + reflexivity.  (* ties set up correctly *)
    + { apply T_AsLocal with (P0 := (Peer "p0")).
        - reflexivity.
        - apply T_Unit.
        - reflexivity.
        - reflexivity.
      }
Qed.


Example test_hasType_TAsLocalFromVar_single_1:
    (* ensure test setup is correct ... *)
    getPeer testPeerTyping1Ties1Context = Peer "p0" /\
    getPeerType testPeerTyping1Ties1Context (PeerInst 2) = Some (Peer "ps") /\
    getTieMult testPeerTyping1Ties1Context (Peer "p0", Peer "ps") = Some single /\
    (* actual test ... *)
    testPeerTyping1Ties1Context |- asLocalFrom (Id "x") (Unit on (Peer "ps")) (interPeerApp (PeerInst 2)) \in Unit.
Proof.
  split.
  - reflexivity.
  - split. 
    + reflexivity.
    + { split.
        - reflexivity.
        - apply T_AsLocalFromVar with (P0 := Peer "p0").
          + reflexivity.
          + reflexivity.
          + apply T_Peer. reflexivity.
      }
Qed.


Example test_hasType_TAsLocalFromVar_optional_1:
    (* ensure test setup is correct ... *)
    getPeer testPeerTyping1Ties1Context = Peer "p0" /\
    getPeerType testPeerTyping1Ties1Context (PeerInst 3) = Some (Peer "po") /\
    getTieMult testPeerTyping1Ties1Context (Peer "p0", Peer "po") = Some optional /\
    (* actual test ... *)
    testPeerTyping1Ties1Context |- asLocalFrom (Id "x") (Unit on (Peer "po")) (interPeerApp (PeerInst 3)) \in Unit.
Proof.
  split.
  - reflexivity.
  - split. 
    + reflexivity.
    + { split.
        - reflexivity.
        - apply T_AsLocalFromVar with (P0 := Peer "p0").
          + reflexivity.
          + reflexivity.
          + apply T_Peer. reflexivity.
      }
Qed.


Example test_hasType_TAsLocalFromVar_multiple_1:
    (* ensure test setup is correct ... *)
    getPeer testPeerTyping1Ties1Context = Peer "p0" /\
    getPeerType testPeerTyping1Ties1Context (PeerInst 4) = Some (Peer "pm") /\
    getTieMult testPeerTyping1Ties1Context (Peer "p0", Peer "pm") = Some multiple /\
    (* actual test ... *)
    testPeerTyping1Ties1Context |- asLocalFrom (Id "x") (Unit on (Peer "pm")) (interPeerApp (PeerInst 4)) \in Unit.
Proof.
  split.
  - reflexivity.
  - split. 
    + reflexivity.
    + { split.
        - reflexivity.
        - apply T_AsLocalFromVar with (P0 := Peer "p0").
          + reflexivity.
          + reflexivity.
          + apply T_Peer. reflexivity.
      }
Qed.


Example test_hasType_TAsLocalFrom_single_1:
    (* ensure test setup is correct ... *)
    getPeer testPeerTyping1Ties1Context = Peer "p0" /\
    getPeerType testPeerTyping1Ties1Context (PeerInst 2) = Some (Peer "ps") /\
    getTieMult testPeerTyping1Ties1Context (Peer "p0", Peer "ps") = Some single /\
    (* actual test ... *)
    testPeerTyping1Ties1Context |- interAsLocalTermFrom unit (Unit on (Peer "ps")) (interPeerApp (PeerInst 2)) \in Unit.
Proof.
  split.
  - reflexivity.
  - split. 
    + reflexivity.
    + { split.
        - reflexivity.
        - apply T_AsLocalFrom with (P0 := Peer "p0").
          + reflexivity.
          + apply T_Unit.
          + reflexivity.
          + apply T_Peer. reflexivity.
      }
Qed.


Example test_hasType_TAsLocalFrom_optional_1:
    (* ensure test setup is correct ... *)
    getPeer testPeerTyping1Ties1Context = Peer "p0" /\
    getPeerType testPeerTyping1Ties1Context (PeerInst 3) = Some (Peer "po") /\
    getTieMult testPeerTyping1Ties1Context (Peer "p0", Peer "po") = Some optional /\
    (* actual test ... *)
    testPeerTyping1Ties1Context |- interAsLocalTermFrom unit (Unit on (Peer "po")) (interPeerApp (PeerInst 3)) \in Unit.
Proof.
  split.
  - reflexivity.
  - split. 
    + reflexivity.
    + { split.
        - reflexivity.
        - apply T_AsLocalFrom with (P0 := Peer "p0").
          + reflexivity.
          + apply T_Unit.
          + reflexivity.
          + apply T_Peer. reflexivity.
      }
Qed.


Example test_hasType_TAsLocalFrom_multiple_1:
    (* ensure test setup is correct ... *)
    getPeer testPeerTyping1Ties1Context = Peer "p0" /\
    getPeerType testPeerTyping1Ties1Context (PeerInst 4) = Some (Peer "pm") /\
    getTieMult testPeerTyping1Ties1Context (Peer "p0", Peer "pm") = Some multiple /\
    (* actual test ... *)
    testPeerTyping1Ties1Context |- interAsLocalTermFrom unit (Unit on (Peer "pm")) (interPeerApp (PeerInst 4)) \in Unit.
Proof.
  split.
  - reflexivity.
  - split. 
    + reflexivity.
    + { split.
        - reflexivity.
        - apply T_AsLocalFrom with (P0 := Peer "p0").
          + reflexivity.
          + apply T_Unit.
          + reflexivity.
          + apply T_Peer. reflexivity.
      }
Qed.


Example test_hasType_TComp_single_1:
    (* ensure test setup is correct ... *)
    getPeer testTies1Context = Peer "p0" /\
    getTieMult testTies1Context (Peer "p0", Peer "ps") = Some single /\
    (* actual test ... *)
    testTies1Context
      |- asLocalIn (Id "x") unit unit (Unit on (Peer "ps")) \in Unit.
Proof.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + { apply T_Comp with (P0 := Peer "p0") (T0 := Unit).
        - reflexivity.
        - apply T_Unit.
        - apply T_Unit.
        - reflexivity.
        - reflexivity.
      }
Qed.


Example test_hasType_TComp_optional_1:
    (* ensure test setup is correct ... *)
    getPeer testTies1Context = Peer "p0" /\
    getTieMult testTies1Context (Peer "p0", Peer "po") = Some optional /\
    (* actual test ... *)
    testTies1Context
      |- asLocalIn (Id "x") unit unit (Unit on (Peer "po")) \in Option Unit.
Proof.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + { apply T_Comp with (P0 := Peer "p0") (T0 := Unit).
        - reflexivity.
        - apply T_Unit.
        - apply T_Unit.
        - reflexivity.
        - reflexivity.
      }
Qed.


Example test_hasType_TComp_multiple_1:
    (* ensure test setup is correct ... *)
    getPeer testTies1Context = Peer "p0" /\
    getTieMult testTies1Context (Peer "p0", Peer "pm") = Some multiple /\
    (* actual test ... *)
    testTies1Context
      |- asLocalIn (Id "x") unit unit (Unit on (Peer "pm")) \in List Unit.
Proof.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + { apply T_Comp with (P0 := Peer "p0") (T0 := Unit).
        - reflexivity.
        - apply T_Unit.
        - apply T_Unit.
        - reflexivity.
        - reflexivity.
      }
Qed.


Example test_hasType_TComp_single_2:
    (* ensure test setup is correct ... *)
    getPeer testTies1Context = Peer "p0" /\
    getTieMult testTies1Context (Peer "p0", Peer "ps") = Some single /\
    (* actual test ... *)
    testTies1Context
      |- asLocalIn (Id "x") unit (idApp (Id "x")) (Unit on (Peer "ps")) \in Unit.
Proof.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + { apply T_Comp with (P0 := Peer "p0") (T0 := Unit).
        - reflexivity.
        - apply T_Unit.
        - apply T_Var. left. reflexivity.
        - reflexivity.
        - reflexivity.
      }
Qed.


Example test_hasType_TCompFrom_single_1:
    (* ensure test setup is correct ... *)
    getPeer testPeerTyping1Ties1Context = Peer "p0" /\
    getPeerType testPeerTyping1Ties1Context (PeerInst 2) = Some (Peer "ps") /\
    getTieMult testPeerTyping1Ties1Context (Peer "p0", Peer "ps") = Some single /\
    (* actual test ... *)
    testPeerTyping1Ties1Context
      |- asLocalInFrom (Id "x") (*=*) unit (*in*) unit (*:*) (Unit on (Peer "ps"))
                       (*from*) (interPeerApp (PeerInst 2))
      \in Unit.
Proof.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + { split.
        - reflexivity.
        - apply T_ComFrom with (T0 := Unit) (P0 := Peer "p0"). split.
          + apply T_Unit.
          + apply T_Unit.
          + reflexivity.
          + apply T_Peer. reflexivity.
      }
Qed.


Example test_hasType_TCompFrom_single_2:
    (* ensure test setup is correct ... *)
    getPeer testPeerTyping1Ties1Context = Peer "p0" /\
    getPeerType testPeerTyping1Ties1Context (PeerInst 2) = Some (Peer "ps") /\
    getTieMult testPeerTyping1Ties1Context (Peer "p0", Peer "ps") = Some single /\
    (* actual test ... *)
    testPeerTyping1Ties1Context
      |- asLocalInFrom (Id "x") (*=*) unit (*in*) (idApp (Id "x"))
                       (*:*) (Unit on (Peer "ps"))
                       (*from*) (interPeerApp (PeerInst 2))
      \in Unit.
Proof.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + { split.
        - reflexivity.
        - apply T_ComFrom with (T0 := Unit) (P0 := Peer "p0"). split.
          + apply T_Unit.
          + apply T_Var. left. reflexivity.
          + reflexivity.
          + apply T_Peer. reflexivity.
      }
Qed.


Example test_hasType_TReactive_1:
    (* ensure test setup is correct ... *)
    getReactType testReactContext1 (Id "r") = Some Unit /\
    (* actual test ... *)
    testReactContext1 |- (idApp (Id "r")) \in Unit.
Proof.
  split.
  - reflexivity.
  - apply T_Reactive. reflexivity.
Qed.


Example test_hasType_TSignal_1: emptyContext |- signal unit \in Signal Unit.
Proof. apply T_Signal. apply T_Unit. Qed.


Example test_hasType_TReactiveVal_1: emptyContext |- var unit \in Var Unit.
Proof. apply T_ReactiveVar. apply T_Unit. Qed.


Example test_hasType_TNow_signal_1: emptyContext |- now (signal unit) \in Unit.
Proof. apply T_Now. left. apply T_Signal. apply T_Unit. Qed.


Example test_hasType_TNow_var_1: emptyContext |- now (var unit) \in Unit.
Proof. apply T_Now. right. apply T_ReactiveVar. apply T_Unit. Qed.


Example test_hasType_TSet_1: emptyContext |- set (var unit) unit \in Unit.
Proof.
  apply T_Set with (T := Unit).
  - apply T_ReactiveVar. apply T_Unit.
  - apply T_Unit.
Qed.


Example test_hasType_TSet_2:
  emptyContext |- set (var (lambda (Id "x") Unit unit))
                      (*:=*) (lambda (Id "x") Unit unit)
                \in Unit.
Proof.
  assert (H: emptyContext |- (lambda (Id "x") Unit unit) \in (Unit ~> Unit)).
  { apply T_Abs. apply T_Unit. }
  apply T_Set with (T := Unit ~> Unit).
  - apply T_ReactiveVar. assumption.
  - assumption.
Qed.

