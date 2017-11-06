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


Example testSubst_remoteApp_1:
  [(Id "x") := (some unit)]
  (remoteApp (remoteInst 0))
  = (remoteApp (remoteInst 0)).
Proof. reflexivity. Qed.
