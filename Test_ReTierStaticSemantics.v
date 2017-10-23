Require Import ReTierStaticSemantics.
Require Import ReTierSyntax.


(* -------------------------------------------------------------------------
  Tests for the ReTierStaticSemantics module
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
    testPeerTyping1Ties1Context |- peerApp (PeerInst 0) \in Remote (Peer "p0").
Proof.
  split.
  - reflexivity.
  - apply T_Peer. reflexivity.
Qed.


Example test_hasType_TAsLocal_single_1:
    (* ensure test setup is correct ... *)
    getPeer testTies1Context = Peer "p0" /\
    getTieMult testTies1Context (Peer "p0", Peer "ps") = Some single /\
    (* actual test ... *)
    testTies1Context |- (asLocal unit (Unit on (Peer "ps"))) \in Unit.
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
    testTies1Context |- (asLocal unit (Unit on (Peer "po"))) \in Option Unit.
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
    testTies1Context |- (asLocal unit (Unit on (Peer "pm"))) \in List Unit.
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


Example test_hasType_TAsLocalFrom_single_1:
    (* ensure test setup is correct ... *)
    getPeer testPeerTyping1Ties1Context = Peer "p0" /\
    getPeerType testPeerTyping1Ties1Context (PeerInst 2) = Some (Peer "ps") /\
    getTieMult testPeerTyping1Ties1Context (Peer "p0", Peer "ps") = Some single /\
    (* actual test ... *)
    testPeerTyping1Ties1Context |- asLocalFrom unit (Unit on (Peer "ps")) (peerApp (PeerInst 2)) \in Unit.
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
    testPeerTyping1Ties1Context |- asLocalFrom unit (Unit on (Peer "po")) (peerApp (PeerInst 3)) \in Unit.
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
    testPeerTyping1Ties1Context |- asLocalFrom unit (Unit on (Peer "pm")) (peerApp (PeerInst 4)) \in Unit.
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
                       (*from*) (peerApp (PeerInst 2))
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
                       (*from*) (peerApp (PeerInst 2))
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

