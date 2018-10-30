Require Import Syntax.
Require Import Coq.Strings.String.
Require Coq.Lists.ListSet.


Example test_idEmpty: (@idEmpty nat) (Id "x") = Datatypes.None.
Proof. reflexivity. Qed.

Example test_update_1: (idUpdate (Id "x") 1 idEmpty) (Id "x") = Some 1.
Proof. reflexivity. Qed.
Example test_update_2: (idUpdate (Id "x") 1 idEmpty) (Id "y") = Datatypes.None.
Proof. reflexivity. Qed.
Example test_update_3: (idUpdate (Id "x") 2 (idUpdate (Id "x") 1 idEmpty) (Id "x")) = Some 2.
Proof. reflexivity. Qed.
Example test_update_4: (idUpdate (Id "y") 2 (idUpdate (Id "x") 1 idEmpty) (Id "x")) = Some 1.
Proof. reflexivity. Qed.
Example test_update_5: (idUpdate (Id "y") 2 (idUpdate (Id "x") 1 idEmpty) (Id "y")) = Some 2.
Proof. reflexivity. Qed.


Example testNotation_multipleTie: "x" -*-> "y" = Tie (Peer "x") (Peer "y") Multiple.
Proof. reflexivity. Qed.
Example testNotation_optionalTie: "x" -?-> "y" = Tie (Peer "x") (Peer "y") Optional.
Proof. reflexivity. Qed.
Example testNotation_singleTie: "x" -1-> "y" = Tie (Peer "x") (Peer "y") Single.
Proof. reflexivity. Qed.
Example testNotation_noneTie: "x" -0-> "y" = Tie (Peer "x") (Peer "y") None.
Proof. reflexivity. Qed.


Example test_tiesAdd_1: (ties_add ("x" -1-> "y") NoTies) (Peer "x", Peer "y") = Single.
Proof. reflexivity. Qed.
Example test_tiesAdd_2: (ties_add ("x" -1-> "y") NoTies) (Peer "y", Peer "x") = None.
Proof. reflexivity. Qed.


Example test_typedPeerInstancesAdd: typed_peer_instances_type
                                      (typed_peer_instances_add (PeerInstance 1, Peer "x")
                                        (typed_peer_instances_add (PeerInstance 2, Peer "y")
                                          NoTypedInstances))
                                      (PeerInstance 2) = Some (Peer "y").
Proof. reflexivity. Qed.
