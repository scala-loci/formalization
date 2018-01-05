Require Import ReTierDynamicSemantics.
Require Import ReTierSyntax.



Definition testSet2 := (ListSet.set_add eq_peerInstDec (PeerInst 0)
                        (ListSet.set_add eq_peerInstDec (PeerInst 1)
                          (ListSet.set_add eq_peerInstDec (PeerInst 0)
                            (ListSet.empty_set p)))).
Definition testSet := (pISet_add (PeerInst 1)
                        (pISet_add (PeerInst 0)
                          noPeerInsts)).
Example test_extensionalPeerSetEquality: testSet = testSet2.
Proof. reflexivity. Qed.

Example test_pISetMem: (pISet_mem (PeerInst 0) testSet) = true.
Proof. reflexivity. Qed.




(** tests for substitution
    -------------------------------------------------------------------
**)

Example testSubst_idApp_1: [(Id "x") := unit] (idApp (Id "x")) = unit.
Proof. reflexivity. Qed.

Example testSubst_idApp_2: [(Id "x") := unit] (idApp (Id "y")) = (idApp (Id "y")).
Proof. reflexivity. Qed.


Example testSubst_unit_1: [(Id "x") := (idApp (Id "y"))] unit = unit.
Proof. reflexivity. Qed.


Example testSubst_lambda_1: [(Id "x") := unit] (lambda (Id "z") Unit unit) 
                            = (lambda (Id "z") Unit unit).
Proof. reflexivity. Qed.

Example testSubst_lambda_2: [(Id "x") := unit] (lambda (Id "z") Unit (idApp (Id "x")) )
                            = (lambda (Id "z") Unit unit).
Proof. reflexivity. Qed.

Example testSubst_lambda_3: [(Id "x") := unit] (lambda (Id "x") Unit (idApp (Id "x")))
                            = (lambda (Id "x") Unit (idApp (Id "x"))).
Proof. reflexivity. Qed.


Example testSubst_app_1: [(Id "x") := unit] (app (lambda (Id "z") Unit unit) unit)
                            = (app (lambda (Id "z") Unit unit) unit).
Proof. reflexivity. Qed.

Example testSubst_app_2: [(Id "x") := unit] (app (lambda (Id "z") Unit (idApp (Id "x"))) unit)
                            = (app (lambda (Id "z") Unit unit) unit).
Proof. reflexivity. Qed.

Example testSubst_app_3: [(Id "x") := unit] (app (lambda (Id "z") Unit unit) (idApp (Id "x")))
                            = (app (lambda (Id "z") Unit unit) unit).
Proof. reflexivity. Qed.


Example testSubst_none_1: [(Id "x") := unit] (none Unit) = (none Unit).
Proof. reflexivity. Qed.


Example testSubst_some_1: [(Id "x") := unit] (some unit) = (some unit).
Proof. reflexivity. Qed.

Example testSubst_some_2: [(Id "x") := unit] (some (idApp (Id "y"))) 
                            = (some (idApp (Id "y"))).
Proof. reflexivity. Qed.

Example testSubst_some_3: [(Id "x") := unit] (some (idApp (Id "x"))) 
                            = (some unit).
Proof. reflexivity. Qed.


Example testSubst_nil_1: [(Id "x") := unit] (nil Unit) = (nil Unit).
Proof. reflexivity. Qed.

Example testSubst_nil_2: [(Id "x") := unit] (cons unit (nil Unit)) 
                          = (cons unit (nil Unit)).
Proof. reflexivity. Qed.


Example testSubst_cons_1: [(Id "x") := unit] (cons unit (nil Unit))
                          = (cons unit (nil Unit)).
Proof. reflexivity. Qed.

Example testSubst_cons_2: [(Id "x") := unit] (cons (idApp (Id "x")) (nil Unit))
                          = (cons unit (nil Unit)).
Proof. reflexivity. Qed.


Example testSubst_asLocal_1:
  [(Id "x") := (some unit)] (asLocal (none Unit)) (Option Unit on (Peer "_"))
                          = (asLocal (none Unit)) (Option Unit on (Peer "_")).
Proof. reflexivity. Qed.

Example testSubst_asLocal_2:
  [(Id "x") := unit] (asLocal (idApp (Id "y")) (Unit on (Peer "_")))
                          = (asLocal (idApp (Id "y")) (Unit on (Peer "_"))).
Proof. reflexivity. Qed.

Example testSubst_asLocal_3:
  [(Id "x") := unit] (asLocal (idApp (Id "x")) (Unit on (Peer "_")))
                          = (asLocal unit (Unit on (Peer "_"))).
Proof. reflexivity. Qed.


Example testSubst_asLocalFrom_1:
  [(Id "x") := (some unit)] (asLocalFrom (none Unit) (Option Unit on (Peer "_")) (*from*) (peerApp (PeerInst 0)))
                          = (asLocalFrom (none Unit) (Option Unit on (Peer "_")) (*from*) (peerApp (PeerInst 0))).
Proof. reflexivity. Qed.

Example testSubst_asLocalFrom_2:
  [(Id "x") := (unit)] (asLocalFrom (idApp (Id "y")) (Unit on (Peer "_")) (*from*) (peerApp (PeerInst 0)))
                          = (asLocalFrom (idApp (Id "y")) (Unit on (Peer "_")) (*from*) (peerApp (PeerInst 0))).
Proof. reflexivity. Qed.

Example testSubst_asLocalFrom_3:
  [(Id "x") := (unit)] (asLocalFrom (idApp (Id "x")) (Unit on (Peer "_")) (*from*) (peerApp (PeerInst 0)))
                          = (asLocalFrom unit (Unit on (Peer "_")) (*from*) (peerApp (PeerInst 0))).
Proof. reflexivity. Qed.


Example testSubst_asLocalIn_1:
  [(Id "x") := (some unit)]
  (asLocalIn (Id "z") (*=*) (none Unit) (*in*) (none Unit) (Unit on (Peer "_")))
  = (asLocalIn (Id "z") (*=*) (none Unit) (*in*) (none Unit) (Unit on (Peer "_"))).
Proof. reflexivity. Qed.

Example testSubst_asLocalIn_2:
  [(Id "x") := (some unit)]
  (asLocalIn (Id "z") (*=*) (idApp (Id "y")) (*in*) (none Unit) (Unit on (Peer "_")))
  = (asLocalIn (Id "z") (*=*) (idApp (Id "y")) (*in*) (none Unit) (Unit on (Peer "_"))).
Proof. reflexivity. Qed.

Example testSubst_asLocalIn_3:
  [(Id "x") := (some unit)]
  (asLocalIn (Id "z") (*=*) (none Unit) (*in*) (idApp (Id "y")) (Unit on (Peer "_")))
  = (asLocalIn (Id "z") (*=*) (none Unit) (*in*) (idApp (Id "y")) (Unit on (Peer "_"))).
Proof. reflexivity. Qed.

Example testSubst_asLocalIn_4:
  [(Id "x") := (some unit)]
  (asLocalIn (Id "z") (*=*) (none Unit) (*in*) (none Unit) (Unit on (Peer "_")))
  = (asLocalIn (Id "z") (*=*) (none Unit) (*in*) (none Unit) (Unit on (Peer "_"))).
Proof. reflexivity. Qed.


Example testSubst_asLocalInFrom_1:
  [(Id "x") := (some unit)]
  (asLocalInFrom (Id "x") (*=*) (none Unit) (*in*) (none Unit) (Unit on (Peer "_")) (*from*) (peerApp (PeerInst 0)))
  = (asLocalInFrom (Id "x") (*=*) (none Unit) (*in*) (none Unit) (Unit on (Peer "_")) (*from*) (peerApp (PeerInst 0))).
Proof. reflexivity. Qed.

Example testSubst_asLocalInFrom_2:
  [(Id "x") := (some unit)]
  (asLocalInFrom (Id "x") (*=*) (idApp (Id "y")) (*in*) (none Unit) (Unit on (Peer "_")) (*from*) (peerApp (PeerInst 0)))
  = (asLocalInFrom (Id "x") (*=*) (idApp (Id "y")) (*in*) (none Unit) (Unit on (Peer "_")) (*from*) (peerApp (PeerInst 0))).
Proof. reflexivity. Qed.

Example testSubst_asLocalInFrom_3:
  [(Id "x") := (some unit)]
  (asLocalInFrom (Id "x") (*=*) (idApp (Id "x")) (*in*) (none Unit) (Unit on (Peer "_")) (*from*) (peerApp (PeerInst 0)))
  = (asLocalInFrom (Id "x") (*=*) (some unit) (*in*) (none Unit) (Unit on (Peer "_")) (*from*) (peerApp (PeerInst 0))).
Proof. reflexivity. Qed.

Example testSubst_asLocalInFrom_4:
  [(Id "x") := (some unit)]
  (asLocalInFrom (Id "x") (*=*) (none Unit) (*in*) (idApp (Id "x")) (Unit on (Peer "_")) (*from*) (peerApp (PeerInst 0)))
  = (asLocalInFrom (Id "x") (*=*) (none Unit) (*in*) (idApp (Id "x")) (Unit on (Peer "_")) (*from*) (peerApp (PeerInst 0))).
Proof. reflexivity. Qed.

Example testSubst_asLocalInFrom_5:
  [(Id "x") := (some unit)]
  (asLocalInFrom (Id "z") (*=*) (none Unit) (*in*) (idApp (Id "x")) (Unit on (Peer "_")) (*from*) (peerApp (PeerInst 0)))
  = (asLocalInFrom (Id "z") (*=*) (none Unit) (*in*) (some unit) (Unit on (Peer "_")) (*from*) (peerApp (PeerInst 0))).
Proof. reflexivity. Qed.


Example testSubst_signal_1:
  [(Id "x") := (some unit)]
  (signal (none Unit))
  = (signal (none Unit)).
Proof. reflexivity. Qed.

Example testSubst_signal_2:
  [(Id "x") := (some unit)]
  (signal (idApp (Id "y")))
  = (signal (idApp (Id "y"))).
Proof. reflexivity. Qed.

Example testSubst_signal_3:
  [(Id "x") := (some unit)]
  (signal (idApp (Id "x")))
  = (signal (some unit)).
Proof. reflexivity. Qed.


Example testSubst_val_1:
  [(Id "x") := (some unit)]
  (var (none Unit))
  = (var (none Unit)).
Proof. reflexivity. Qed.

Example testSubst_var_2:
  [(Id "x") := (some unit)]
  (var (idApp (Id "y")))
  = (var (idApp (Id "y"))).
Proof. reflexivity. Qed.

Example testSubst_var_3:
  [(Id "x") := (some unit)]
  (var (idApp (Id "x")))
  = (var (some unit)).
Proof. reflexivity. Qed.


Example testSubst_now_1:
  [(Id "x") := (some unit)]
  (now (signal (none Unit)))
  = (now (signal (none Unit))).
Proof. reflexivity. Qed.

Example testSubst_now_2:
  [(Id "x") := (some unit)]
  (now (signal (idApp (Id "y"))))
  = (now (signal (idApp (Id "y")))).
Proof. reflexivity. Qed.

Example testSubst_now_3:
  [(Id "x") := (some unit)]
  (now (signal (idApp (Id "x"))))
  = (now (signal (some unit))).
Proof. reflexivity. Qed.


Example testSubst_set_1:
  [(Id "x") := (some unit)]
  (set (var (none Unit)) (*:=*) (none Unit))
  = (set (var (none Unit)) (*:=*)  (none Unit)).
Proof. reflexivity. Qed.

Example testSubst_set_2:
  [(Id "x") := (some unit)]
  (set (var (idApp (Id "y"))) (*:=*) (none Unit))
  = (set (var (idApp (Id "y"))) (*:=*)  (none Unit)).
Proof. reflexivity. Qed.

Example testSubst_set_3:
  [(Id "x") := (some unit)]
  (set (var (idApp (Id "x"))) (*:=*) (none Unit))
  = (set (var (some unit)) (*:=*)  (none Unit)).
Proof. reflexivity. Qed.

Example testSubst_set_4:
  [(Id "x") := (some unit)]
  (set (var (none Unit)) (*:=*) (idApp (Id "y")))
  = (set (var (none Unit)) (*:=*) (idApp (Id "y"))).
Proof. reflexivity. Qed.

Example testSubst_set_5:
  [(Id "x") := (some unit)]
  (set (var (none Unit)) (*:=*) (idApp (Id "x")))
  = (set (var (none Unit)) (*:=*)  (some unit)).
Proof. reflexivity. Qed.


Example testSubst_peerApp_1:
  [(Id "x") := (some unit)]
  (peerApp (PeerInst 0))
  = (peerApp (PeerInst 0)).
Proof. reflexivity. Qed.

(*
Example testSubst_remoteApp_1:
  [(Id "x") := (some unit)]
  (remoteApp (remoteInst 0))
  = (remoteApp (remoteInst 0)).
Proof. reflexivity. Qed.
*)



(* ====================================================================
   Tests for implementation of pull based reactive system:
*)
Definition testR1V1 := (some unit).
Definition testR2V1 := (none Unit).
Definition testReactSys_p_1 := reactAlloc testR1V1 emptyReactSys.
Definition testReactSys_p_2 := reactAlloc testR2V1 (snd testReactSys_p_1).

Example testReactAlloc_1:
  match testReactSys_p_1 with
  | (r1, ReactiveSystem _ _ map) => map r1
  end
  = Some (some unit).
Proof.
  reflexivity.
Qed.

Example testReactAlloc_2:
  match testReactSys_p_1 with
  | (r1, _) =>  match testReactSys_p_2 with
                | (r2, ReactiveSystem _ _ map) => (map r1, map r2)
                end
  end
  = (Some (some unit), Some (none Unit)).
Proof.
  reflexivity.
Qed.

(* tests for 'curentValue' implicity also test 'reactAlloc' *)
Definition testCurrentValue_1:
  currentValue (fst testReactSys_p_1) (snd testReactSys_p_1) = (Some testR1V1, (snd testReactSys_p_1)).
Proof. reflexivity. Qed.

Definition testCurentValue_2:
  currentValue (fst testReactSys_p_2) (snd testReactSys_p_2) = (Some testR2V1, (snd testReactSys_p_2)).
Proof. reflexivity. Qed.

Definition testCurentValue_3:
  currentValue (Reactive 99) (snd testReactSys_p_2) = (None,  (snd testReactSys_p_2)).
Proof. reflexivity. Qed.

Definition testR1V2 := (lambda (Id "x") (*:*) Unit (*.*) unit).
Definition testReactSys_3 := updateVar (fst testReactSys_p_1) testR1V2 (snd testReactSys_p_2).

Example testUpdateVar_1:
  currentValue (fst testReactSys_p_1) testReactSys_3 = (Some testR1V2, testReactSys_3).
Proof. reflexivity. Qed.

Example testUpdateVar_2:
  currentValue (fst testReactSys_p_2) testReactSys_3 = (Some testR2V1, testReactSys_3).
Proof. reflexivity. Qed.



(* ====================================================================
   Tests for relation 'localStep':
*)


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
Definition testPeerInsts1 := (pISet_add (PeerInst 4)
                                (pISet_add (PeerInst 3)
                                  (pISet_add (PeerInst 2)
                                    (pISet_add (PeerInst 1)
                                      (pISet_add (PeerInst 0)
                                        noPeerInsts))))).
Definition testTies1Context := LeContext testTies1 testPeerTyping1 testPeerInsts1 (Peer "p0") emptyReactSys.

Example testLocalStep_EApp_1:
  emptyLeContext |> (app (lambda (Id "x") (Option Unit) (unit)) (some unit)) L==> Right _ _ unit.
Proof. apply E_App, v_some, v_unit. Qed.

Example testLocalStep_EApp_2:
  emptyLeContext |> (app (lambda (Id "x") (Option Unit) (idApp (Id "x")))) (some unit)
    L==> Right _ _ (some unit).
Proof. apply E_App, v_some, v_unit. Qed.


Example testLocalStep_EAsLocal_1:
  testTies1Context |> (asLocal unit (*:*) (Unit on (Peer "ps"))) L==> Right _ _ unit.
Proof.
  eapply E_AsLocal.
  - reflexivity.
  - apply v_unit.
  - reflexivity.
  - reflexivity.
Qed.


Example testLocalStep_EComp_1:
  testTies1Context |> asLocalIn (Id "x") (*=*) unit (*in*)  (idApp (Id "x")) (*:*) (Unit on (Peer "ps"))
    L==> Right _ _ (asLocal unit (*:*) (Unit on (Peer "ps"))).
Proof. apply E_Comp, v_unit. Qed.


Example testLocalStep_ERemote_1:
  testTies1Context |> asLocal (app (lambda (Id "x") (Option Unit) (unit)) (some unit)) (*:*) (Unit on (Peer "ps"))
    L==> Right _ _ (asLocal unit (*:*) (Unit on (Peer "ps"))).
Proof.
  eapply E_Remote.
  - reflexivity.
  - reflexivity.
  - apply E_App, v_some, v_unit.
Qed.


Example testLocalStep_EAsLocalFrom_1:
  testTies1Context |> asLocalFrom unit (*:*) (Unit on (Peer "ps")) (*from*) (peerApp (PeerInst 2))
    L==> Right _ _ unit.
Proof. apply E_AsLocalFrom, v_unit. Qed.


Example testLocalStep_ECompFrom_1:
  testTies1Context |> asLocalInFrom (Id "x") (*=*) unit (*in*) (idApp (Id "x")) (*:*) (Unit on (Peer "ps")) (*from*) (peerApp (PeerInst 2))
    L==> Right _ _ (asLocalFrom unit (*:*) (Unit on (Peer "ps")) (*from*) (peerApp (PeerInst 2))).
Proof. apply E_CompFrom, v_unit. Qed.


Example testLocalStep_ERemoteFrom_1:
  testTies1Context |> asLocalFrom (app (lambda (Id "x") (Option Unit) (unit)) (some unit)) (*:*) (Unit on (Peer "ps")) (*from*) (peerApp (PeerInst 2))
  L==> Right _ _ (asLocalFrom unit (*:*) (Unit on (Peer "ps")) (*from*) (peerApp (PeerInst 2))).
Proof.
  eapply E_RemoteFrom.
  - reflexivity.
  - reflexivity.
  - apply E_App, v_some, v_unit.
Qed.
  

(* Tests for reactive rules *)

Definition setReactiveSys (cont: leContext) (sys: reactiveSystem): leContext :=
  match cont with
  | LeContext ties peers peerInsts currentPeerT _ => LeContext ties peers peerInsts currentPeerT sys
  end.

Definition testReactSys_var1_p := reactAlloc (some unit) emptyReactSys.
Definition testVar1 := fst testReactSys_var1_p.
Definition testReactSys_var1 := snd testReactSys_var1_p.
Example testLocalStep_EReactiveVar_1:
  (* ensure test setup is correct ... *)
  (match testReactSys_var1 with ReactiveSystem _ _ map => map testVar1 end)
    = Some (some unit) /\
  (* actual test ... *)
  emptyLeContext ||> var (some unit) Ld==> Left _ _ testVar1, testReactSys_var1. 
Proof.
  split.
  - reflexivity.
  - eapply E_ReactiveVar.
    + reflexivity.
    + apply v_some, v_unit.
Qed.


Definition testReactSys_var1_signal1_p := reactAlloc (reactApp testVar1) testReactSys_var1.
Definition testSignal1 := fst testReactSys_var1_signal1_p.
Definition testReactSys_var1_signal1 := snd testReactSys_var1_signal1_p.
Definition testContext_var1 := setReactiveSys emptyLeContext testReactSys_var1.
Example testLocalStep_ESignal_1:
  testContext_var1 |> signal (reactApp testVar1) L==> Left _ _ testSignal1.
Proof.
  eapply E_Signal. reflexivity.
Qed.


Definition testContext_var1_signal1 := setReactiveSys emptyLeContext testReactSys_var1_signal1.
Definition testReactSys_var1None := updateVar testVar1 (none Unit) testReactSys_var1.
Example testLocalStep_ESet_1:
  (* ensure test setup is correct ... *)
  currentValue testVar1 (getReactSys testContext_var1) = (Some (some unit), testReactSys_var1) /\
  currentValue testVar1 testReactSys_var1None  = (Some (none Unit), testReactSys_var1None) /\
  (* actual test ... *)
  testContext_var1 ||> set (reactApp testVar1) (*:=*) (none Unit) Ld==> (Right _ _ unit), testReactSys_var1None.
Proof.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + eapply E_Set.
      * reflexivity.
      * apply v_none.
Qed.


Definition testReactSys_var1None_signal1 := updateVar testVar1 (none Unit) testReactSys_var1_signal1.
Definition testContext_var1None_signal1 := setReactiveSys emptyLeContext testReactSys_var1None_signal1.
Example testLocalStep_ENow_1:
  (* ensure test setup is correct ... *)
  currentValue testVar1 (getReactSys testContext_var1_signal1) = (Some (some unit), testReactSys_var1_signal1) /\
  (* actual test ... *)
  testContext_var1_signal1 ||> now (reactApp testVar1) Ld==> Right _ _ (some unit), testReactSys_var1_signal1.
Proof.
  split.
  - reflexivity.
  - eapply E_Now. reflexivity.
Qed.

Example testLocalStep_ENow_2:
  (* ensure test setup is correct ... *)
  currentValue testVar1 (getReactSys testContext_var1_signal1) = (Some (some unit), testReactSys_var1_signal1) /\
  currentValue testSignal1 (getReactSys testContext_var1_signal1) = (Some (reactApp testVar1), testReactSys_var1_signal1) /\
  (* actual test ... *)
  testContext_var1_signal1 ||> now (reactApp testVar1) Ld==> Right _ _ (some unit), testReactSys_var1_signal1.
Proof.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + eapply E_Now. reflexivity.
Qed.