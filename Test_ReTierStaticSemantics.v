Require Import ReTierStaticSemantics.
Require Import ReTierSyntax.


(* -------------------------------------------------------------------------
  Tests for the ReTierStaticSemantics module
 * -------------------------------------------------------------------------*)





(** In the following [plt_isWellTyped] and [has_type] are tested.
  The tests are ordered such that every test case's proof only relies on tested
  inference rules.
**)


Definition testPsi0: reactiveEnv := Datatypes.nil.
Definition testPsi1: reactiveEnv := Datatypes.cons (Unit on Peer "_") Datatypes.nil.
Definition testGamma1: varEnv := idUpdate (Id "x") Tnat (idUpdate (Id "y") Unit idEmpty).
Definition testDelta1: placeEnv := idUpdate (Id "x") (Unit on (Peer "px")) idEmpty.
Definition testTies1 := Ties ["p0" -*-> "pm", "p0" -?-> "po", "p0" -1-> "ps", "p0" -0-> "pn"].
Definition testPeerTyping1 := TypedInstances [4 : "pm", 3 : "po", 2 : "ps", 1 : "pn", 0 : "p0"].

Example test_pltIsWellTyped_TEnd_1:
  (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv |- pUnit.
Proof. apply T_End. Qed.


Example test_pltIsWellTyped_TEnd_2:
  (Program NoTies NoTypedInstances) :: testPsi1; testDelta1 |- pUnit.
Proof. apply T_End. Qed.


Example test_hasType_TUnit_1:
  (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "dummy" |- unit : Unit.
Proof. apply T_Unit. Qed.


Example test_pltIsWellTyped_TPlace_1:
  (Program NoTies NoTypedInstances) :: testPsi1; testDelta1 |- placed (Id "x") (Unit on (Peer "px")) unit pUnit.
Proof.
  apply T_Place.
  - apply T_End.
  - apply T_Unit.
Qed.


Example test_hasType_TVar_normalVar_1:
  (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; testGamma1; Peer "p1" |- idApp (Id "x") : Tnat.
Proof. apply T_Var. left. reflexivity. Qed.


Example test_hasType_TVar_placedVar_2:
  (Program NoTies NoTypedInstances) :: testPsi0; testDelta1; emptyVarEnv; Peer "px" |- idApp (Id "x") : Unit.
Proof. apply T_Var. right. split. - reflexivity. - reflexivity. Qed.


Example test_hasType_TAbs_1: 
    (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "dummy" |- lambda (Id "x") Tnat unit : Tnat ~> Unit.
Proof. apply T_Abs. apply T_Unit. Qed.


Example test_hasType_TAbs_2: 
    (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "dummy" |- lambda (Id "x") Tnat (idApp (Id "x")) : Tnat ~> Tnat.
Proof. apply T_Abs. apply T_Var. left. reflexivity. Qed.


(** Tests variable shadowing **)
Example test_hasType_TAbs_3:
  (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; testGamma1; Peer "_" |- lambda (Id "x") Unit (idApp (Id "x")) : Unit ~> Unit.
Proof. apply T_Abs. apply T_Var. left. reflexivity. Qed.


Example test_hasType_TApp_1:
  (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "dummy" |- app (lambda (Id "x") Unit unit) unit : Unit.
Proof.
  apply T_App with (T2 := Unit).
  - apply T_Abs. apply T_Unit.
  - apply T_Unit.
Qed.


Example test_hasType_TApp_2: 
  (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "dummy" |- app (lambda (Id "x") Unit (idApp (Id "x"))) unit : Unit.
Proof.
  apply T_App with (T2 := Unit).
  - apply T_Abs. apply T_Var. left. reflexivity.
  - apply T_Unit.
Qed.


Example test_hasType_TNil_1: 
  (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "dummy" |- nil Unit : List Unit.
Proof. apply T_Nil. Qed.


Example test_hasType_TCons_1: 
  (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "dummy" |- cons unit (nil Unit) : List Unit.
Proof.
  apply T_Cons.
  - apply T_Unit.
  - apply T_Nil.
Qed.


Example test_hasType_TSome_1: 
    (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "dummy" |- some unit : Option Unit.
Proof. apply T_Some. apply T_Unit. Qed.


Example test_hasType_TNone_1: 
    (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "dummy" |- none Unit : Option Unit.
Proof. apply T_None. Qed.


Example test_hasType_TPeer_1:
  (Program testTies1 testPeerTyping1) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "p0" |- peerApp (PeerInstance 0) : Remote (Peer "p0").
Proof. apply T_Peer. reflexivity. Qed.


Example test_hasType_TAsLocal_single_1:
  (* ensure test setup is correct ... *)
  testTies1 (Peer "p0", Peer "ps") = Single /\
  (* actual test ... *)
  (Program testTies1 NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "p0"
    |- asLocal unit (Unit on (Peer "ps")) : Unit.
Proof.
  split.
  - reflexivity. (* ties set up correctly *)
  - apply T_AsLocal with (P0 := (Peer "p0")).
    + apply U_Unit.
    + apply T_Unit.
    + cbv. congruence.
    + reflexivity.
Qed.


Example test_hasType_TAsLocal_optional_1:
  (* ensure test setup is correct ... *)
  testTies1 (Peer "p0", Peer "po") = Optional /\
  (* actual test ... *)
  (Program testTies1 NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "p0"
    |- asLocal unit (Unit on (Peer "po")) : Option Unit.
Proof.
  split.
  - reflexivity. (* ties set up correctly *)
  - apply T_AsLocal with (P0 := (Peer "p0")).
    + apply U_Unit.
    + apply T_Unit.
    + cbv. congruence.
    + reflexivity.
Qed.


Example test_hasType_TAsLocal_multiple_1:
  (* ensure test setup is correct ... *)
  testTies1 (Peer "p0", Peer "pm") = Multiple /\
  (* actual test ... *)
  (Program testTies1 NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "p0"
    |- asLocal unit (Unit on (Peer "pm")) : List Unit.
Proof.
  split.
  - reflexivity.  (* current peer set correctly *)
  - apply T_AsLocal with (P0 := (Peer "p0")).
    + apply U_Unit.
    + apply T_Unit.
    + cbv. congruence.
    + reflexivity.
Qed.


Example test_hasType_TAsLocalFrom_single_1:
  (* ensure test setup is correct ... *)
  typed_peer_instances_type testPeerTyping1 (PeerInstance 2) = Some (Peer "ps") /\
  testTies1 (Peer "p0", Peer "ps") = Single /\
  (* actual test ... *)
  (Program testTies1 testPeerTyping1) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "p0"
    |- asLocalFrom unit (Unit on (Peer "ps")) (peerApp (PeerInstance 2)) : Unit.
Proof.
  split.
  - reflexivity.
  - split. 
    + reflexivity.
    + apply T_AsLocalFrom with (P0 := Peer "p0").
      * apply U_Unit.
      * apply T_Unit.
      * cbv. congruence.
      * apply T_Peer. reflexivity.
Qed.


Example test_hasType_TAsLocalFrom_optional_1:
  (* ensure test setup is correct ... *)
  typed_peer_instances_type testPeerTyping1 (PeerInstance 3) = Some (Peer "po") /\
  testTies1 (Peer "p0", Peer "po") = Optional /\
  (* actual test ... *)
  (Program testTies1 testPeerTyping1) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "p0"
    |- asLocalFrom unit (Unit on (Peer "po")) (peerApp (PeerInstance 3)) : Unit.
Proof.
  split.
  - reflexivity.
  - split. 
    + reflexivity.
    + apply T_AsLocalFrom with (P0 := Peer "p0").
      * apply U_Unit.
      * apply T_Unit.
      * cbv. congruence.
      * apply T_Peer. reflexivity.
Qed.


Example test_hasType_TAsLocalFrom_multiple_1:
  (* ensure test setup is correct ... *)
  typed_peer_instances_type testPeerTyping1 (PeerInstance 4) = Some (Peer "pm") /\
  testTies1 (Peer "p0", Peer "pm") = Multiple /\
  (* actual test ... *)
  (Program testTies1 testPeerTyping1) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "p0"
    |- asLocalFrom unit (Unit on (Peer "pm")) (peerApp (PeerInstance 4)) : Unit.
Proof.
  split.
  - reflexivity.
  - split. 
    + reflexivity.
    + apply T_AsLocalFrom with (P0 := Peer "p0").
      * apply U_Unit.
      * apply T_Unit.
      * cbv. congruence.
      * apply T_Peer. reflexivity.
Qed.


Example test_hasType_TComp_single_1:
  (* ensure test setup is correct ... *)
  testTies1 (Peer "p0", Peer "ps") = Single /\
  (* actual test ... *)
  (Program testTies1 NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "p0"
    |- asLocalIn (Id "x") unit unit (Unit on (Peer "ps")) : Unit.
Proof.
  split.
  - reflexivity.
  - apply T_Comp with (P0 := Peer "p0") (T0 := Unit).
    + apply U_Unit.
    + apply U_Unit.
    + apply T_Unit.
    + apply T_Unit.
    + cbv. congruence.
    + reflexivity.
Qed.


Example test_hasType_TComp_optional_1:
  (* ensure test setup is correct ... *)
  testTies1 (Peer "p0", Peer "po") = Optional /\
  (* actual test ... *)
  (Program testTies1 NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "p0"
    |- asLocalIn (Id "x") unit unit (Unit on (Peer "po")) : Option Unit.
Proof.
  split.
  - reflexivity.
  - apply T_Comp with (P0 := Peer "p0") (T0 := Unit).
    + apply U_Unit.
    + apply U_Unit.
    + apply T_Unit.
    + apply T_Unit.
    + cbv. congruence.
    + reflexivity.
Qed.


Example test_hasType_TComp_multiple_1:
  (* ensure test setup is correct ... *)
  testTies1 (Peer "p0", Peer "pm") = Multiple /\
  (* actual test ... *)
  (Program testTies1 NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "p0"
    |- asLocalIn (Id "x") unit unit (Unit on (Peer "pm")) : List Unit.
Proof.
  split.
  - reflexivity.
  - apply T_Comp with (P0 := Peer "p0") (T0 := Unit).
    + apply U_Unit.
    + apply U_Unit.
    + apply T_Unit.
    + apply T_Unit.
    + cbv. congruence.
    + reflexivity.
Qed.


Example test_hasType_TComp_single_2:
  (* ensure test setup is correct ... *)
  testTies1 (Peer "p0", Peer "ps") = Single /\
  (* actual test ... *)
  (Program testTies1 NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "p0"
    |- asLocalIn (Id "x") unit (idApp (Id "x")) (Unit on (Peer "ps")) : Unit.
Proof.
  split.
  - reflexivity.
  - apply T_Comp with (P0 := Peer "p0") (T0 := Unit).
    + apply U_Unit.
    + apply U_Unit.
    + apply T_Unit.
    + apply T_Var. left. reflexivity.
    + cbv. congruence.
    + reflexivity.
Qed.


Example test_hasType_TCompFrom_single_1:
  (* ensure test setup is correct ... *)
  typed_peer_instances_type testPeerTyping1 (PeerInstance 2) = Some (Peer "ps") /\
  testTies1 (Peer "p0", Peer "ps") = Single /\
  (* actual test ... *)
  (Program testTies1 testPeerTyping1) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "p0"
    |- asLocalInFrom (Id "x") (*=*) unit (*in*) unit (*:*) (Unit on (Peer "ps"))
                     (*from*) (peerApp (PeerInstance 2))
    : Unit.
Proof.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + apply T_ComFrom with (T0 := Unit) (P0 := Peer "p0").
      * apply U_Unit.
      * apply U_Unit.
      * apply T_Unit.
      * apply T_Unit.
      * cbv. congruence.
      * apply T_Peer. reflexivity.
Qed.


Example test_hasType_TCompFrom_single_2:
  (* ensure test setup is correct ... *)
  typed_peer_instances_type testPeerTyping1 (PeerInstance 2) = Some (Peer "ps") /\
  testTies1 (Peer "p0", Peer "ps") = Single /\
  (* actual test ... *)
  (Program testTies1 testPeerTyping1) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "p0"
    |- asLocalInFrom (Id "x") (*=*) unit (*in*) (idApp (Id "x"))
                     (*:*) (Unit on (Peer "ps"))
                     (*from*) (peerApp (PeerInstance 2))
    : Unit.
Proof.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + apply T_ComFrom with (T0 := Unit) (P0 := Peer "p0").
      * apply U_Unit.
      * apply U_Unit.
      * apply T_Unit.
      * apply T_Var. left. reflexivity.
      * cbv. congruence.
      * apply T_Peer. reflexivity.
Qed.


Example test_hasType_TReactive_1:
  (* ensure test setup is correct ... *)
  reactive_type (Reactive 0) testPsi1 = Some (Unit on Peer "_") /\
  (* actual test ... *)
  (Program NoTies NoTypedInstances) :: testPsi1; emptyPlaceEnv; emptyVarEnv; Peer "_" |- reactApp (Reactive 0) : Unit.
Proof.
  split.
  - reflexivity.
  - apply T_Reactive. reflexivity.
Qed.


Example test_hasType_TSignal_1:
  (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "dummy" |- signal unit : Signal Unit.
Proof. apply T_Signal. apply T_Unit. Qed.


Example test_hasType_TReactiveVal_1:
  (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "dummy" |- var unit : Var Unit.
Proof. apply T_ReactiveVar. apply T_Unit. Qed.


Example test_hasType_TNow_signal_1:
  (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "dummy" |- now (signal unit) : Unit.
Proof.
  apply T_Now with (T0 := Signal Unit).
  - apply T_Signal. apply T_Unit.
  - left. reflexivity.
Qed.


Example test_hasType_TNow_var_1:
  (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "dummy" |- now (var unit) : Unit.
Proof.
  eapply T_Now.
  - apply T_ReactiveVar. apply T_Unit.
  - right. reflexivity.
Qed.


Example test_hasType_TSet_1:
  (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "dummy" |- set (var unit) unit : Unit.
Proof.
  apply T_Set with (T := Unit).
  - apply T_ReactiveVar. apply T_Unit.
  - apply T_Unit.
Qed.


Example test_hasType_TSet_2:
  (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "dummy"
    |- set (var (lambda (Id "x") Unit unit))
           (*:=*) (lambda (Id "x") Unit unit)
    : Unit.
Proof.
  assert (H: (Program NoTies NoTypedInstances) :: testPsi0; emptyPlaceEnv; emptyVarEnv; Peer "dummy" |- lambda (Id "x") Unit unit : Unit ~> Unit).
  - apply T_Abs.
    apply T_Unit.
  - apply T_Set with (T := Unit ~> Unit).
    + apply T_ReactiveVar. assumption.
    + assumption.
Qed.

