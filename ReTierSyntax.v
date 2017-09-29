Require Import Coq.Strings.String.
(*
Require Import Coq.Lists.List.
*)

Require Import Maps.

Inductive id : Type :=
  | Id : string -> id.

Definition beq_id (x y: id): bool :=
  match x, y with
  | Id n, Id m => if string_dec n m then true else false
  end.


Example test_beq_id_1: beq_id (Id "x") (Id "x") = true.
Proof. reflexivity. Qed.

Example test_beq_id_2: beq_id (Id "x") (Id "y") = false.
Proof. reflexivity. Qed.


Definition idMap (V: Type) := partial_map id V.
Definition idEmpty {V: Type} := p_empty id V.
Definition update {V: Type} (k: id) (v: V) (m: idMap V): idMap V :=
  p_update beq_id m k v.
Definition pair_update {V: Type}  (z: id*V) (m: idMap V): idMap V :=
  match z with
  | (k, v) => update k v m
  end.


Example test_idEmpty_1: (@idEmpty nat) (Id "x") = None.
Proof. reflexivity. Qed.

Example test_update_1: (update (Id "x") 1 idEmpty) (Id "x") = Some 1. 
Proof. reflexivity. Qed.
Example test_update_2: (update (Id "x") 1 idEmpty) (Id "y") = None.  
Proof. reflexivity. Qed.
Example test_update_3: (update (Id "x") 2 (update (Id "x") 1 idEmpty) (Id "x")) = Some 2.
Proof. reflexivity. Qed.
Example test_update_4: (update (Id "y") 2 (update (Id "x") 1 idEmpty) (Id "x")) = Some 1.
Proof. reflexivity. Qed.
Example test_update_5: (update (Id "y") 2 (update (Id "x") 1 idEmpty) (Id "y")) = Some 2.
Proof. reflexivity. Qed.


(** peer instances **)
Inductive p : Type :=
  | PeerInst: nat -> p.

Definition beq_peerInst (p1 p2: p): bool :=
  match (p1, p2) with
  | (PeerInst x, PeerInst y) => if Nat.eqb x y then true else false
  end.

(** peer types **)
Inductive P : Type :=
  | Peer: string -> P.

Definition beq_peerType (p1 p2: P): bool :=
  match (p1, p2) with
  | (Peer x, Peer y) => if string_dec x y then true else false
  end.

Example test_beq_peer_1: beq_peerType (Peer "x") (Peer "x") = true.
Proof. reflexivity. Qed.

Example test_beq_peer_2: beq_peerType (Peer "y") (Peer "x") = false.
Proof. reflexivity. Qed.


(** remote instances **)
Inductive r: Type :=
  | remoteInst: nat -> r.


(** types **)
Inductive T : Type :=
  | Arrow  : T -> T -> T
  | Unit   : T
  | Option : T -> T
  | List   : T -> T
  | Remote : P -> T
  | Signal : T -> T
  | Var    : T -> T
  
  | Tnat   : T.   (* Added to make testing easier. *)

Notation "T1 ~> T2" := (Arrow T1 T2) (at level 80, right associativity).


(** placement types **)
Inductive S : Type :=
  | on : T -> P -> S.

Infix "on" := on (at level 20).

(** terms **)
Inductive t : Type := 
  | lambda : id -> T -> t -> t
  | app    : t -> t -> t
  | idApp  : id -> t
  | unit   : t
  | none   : T -> t
  | some   : t -> t
  | nil    : T -> t
  | cons   : t -> t -> t
  | asLocal       : id -> S -> t
  | asLocalFrom   : id -> S -> t -> t
  | asLocalIn     : id -> t -> t -> S -> t
  | asLocalInFrom : id -> t -> t -> S -> t -> t
  | signal : t -> t
  | var    : t -> t
  | now    : t -> t
  | set    : t -> t -> t

  (* May only occur as intermediate steps during evaluation. *)
  | interPeerApp          : p -> t
  | interRemoteApp        : r -> t
  | interAsLocalTerm      : t -> S -> t
  | interAsLocalTermFrom  : t -> S -> t -> t
  
  (* Added to make testing easier. *)
  | tnat   : nat -> t.


(*
Notation "\ x ; T , t" := (lambda (Id x) T t) (at level 80, left associativity).
Example testNotationLambda1: (\ "z" ; Unit , unit) = (lambda (Id "z") Unit unit).
Proof. reflexivity. Qed.
*)


(** placed terms **)
Inductive s : Type :=
  | placed : id -> S -> t -> s -> s
  | pUnit  : s.


Inductive multiplicity : Type :=
  | multiple : multiplicity
  | optional : multiplicity
  | single   : multiplicity
  | mNone    : multiplicity.


Inductive tie : Type :=
  | Tie : P -> P -> multiplicity -> tie.

Notation "P1 *-> P2" := (Tie P1 P2 multiple) (at level 20).
Notation "P1 ?-> P2" := (Tie P1 P2 optional) (at level 20).
Notation "P1 S-> P2" := (Tie P1 P2 single) (at level 20).
Notation "P1 N-> P2" := (Tie P1 P2 mNone) (at level 20).

Example testNotation_multipleTie: Peer "x" *-> Peer "y" = Tie (Peer "x") (Peer "y") multiple.
Proof. reflexivity. Qed.
Example testNotation_optionalTie: Peer "x" ?-> Peer "y" = Tie (Peer "x") (Peer "y") optional.
Proof. reflexivity. Qed.
Example testNotation_singleTie: Peer "x" S-> Peer "y" = Tie (Peer "x") (Peer "y") single.
Proof. reflexivity. Qed.
Example testNotation_noneTie: Peer "x" N-> Peer "y" = Tie (Peer "x") (Peer "y") mNone.
Proof. reflexivity. Qed.


Definition Ties := partial_map (P*P) multiplicity.
Definition noTies: Ties := @p_empty (P*P) multiplicity.
Definition beq_pPair (x y: P*P): bool :=
  match (x, y) with
  | ((px1, px2), (py1, py2)) => andb (beq_peerType px1 py1) (beq_peerType px2 py2)
  end.
Definition tie_update (x: tie) (m: Ties) :=
  match x with
  | Tie p1 p2 mult => @p_update (P*P) multiplicity beq_pPair m (p1, p2) mult
  end.

Example test_tieUpdate_1: (tie_update (Peer "x" S-> Peer "y") noTies) (Peer "x", Peer "y") = Some single.
Proof. reflexivity. Qed.


Definition peerTyping := partial_map p P.
Definition noPeers := @p_empty p P.
Definition pT_update (inst: p) (type: P) (typing: peerTyping) : peerTyping :=
    p_update beq_peerInst typing inst type.

Example test_peerTypingUpdate_1: (pT_update (PeerInst 1) (Peer "x")
                                    (pT_update (PeerInst 2) (Peer "y")
                                      noPeers)) (PeerInst 2) = Some (Peer "y").
Proof. reflexivity. Qed.


(** named 'l' in informal specification **)
Inductive program : Type :=
  | Prog : peerTyping -> Ties -> s -> program.
