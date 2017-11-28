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

Lemma beq_id_eq : forall (x y: id), beq_id x y = true <-> x = y.
Proof.
intros.
destruct x as [ x ], y as [ y ].
simpl.
case (String.string_dec x y); intros; split; congruence.
Qed.

Lemma beq_id_not_eq : forall (x y: id), beq_id x y = false <-> x <> y.
Proof.
intros.
destruct x as [ x ], y as [ y ].
simpl.
case (String.string_dec x y); intros; split; congruence.
Qed.

Lemma beq_id_comm : forall (x y: id), beq_id x y = beq_id y x.
Proof.
intros.
destruct x as [ x ], y as [ y ].
simpl.
case_eq (String.string_dec x y);
  case_eq (String.string_dec y x);
  intros;
  subst;
  reflexivity || contradiction.
Qed.

Lemma beq_id_refl : forall x, beq_id x x = true.
Proof.
intros.
destruct x as [ x ].
simpl.
case (String.string_dec x x); intros; congruence || contradiction.
Qed.


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


(** reactive instances **)
Inductive r: Type :=
  | Reactive: nat -> r.

Definition beq_react (r1 r2: r): bool :=
  match (r1, r2) with
  | (Reactive x, Reactive y) => if Nat.eqb x y then true else false
  end.

Definition idMap (V: Type) := partial_map id V.
Definition idEmpty {V: Type} := p_empty id V.
Definition idUpdate {V: Type} (k: id) (v: V) (m: idMap V): idMap V :=
  p_update beq_id m k v.

Definition reactMap (V: Type) := partial_map r V.
Definition reactEmpty {V: Type} := p_empty r V.
Definition reactUpdate {V: Type} (k: r) (v: V) (m: reactMap V): reactMap V :=
  p_update beq_react m k v.

Example test_idEmpty_1: (@idEmpty nat) (Id "x") = None.
Proof. reflexivity. Qed.

Example test_update_1: (idUpdate (Id "x") 1 idEmpty) (Id "x") = Some 1. 
Proof. reflexivity. Qed.
Example test_update_2: (idUpdate (Id "x") 1 idEmpty) (Id "y") = None.  
Proof. reflexivity. Qed.
Example test_update_3: (idUpdate (Id "x") 2 (idUpdate (Id "x") 1 idEmpty) (Id "x")) = Some 2.
Proof. reflexivity. Qed.
Example test_update_4: (idUpdate (Id "y") 2 (idUpdate (Id "x") 1 idEmpty) (Id "x")) = Some 1.
Proof. reflexivity. Qed.
Example test_update_5: (idUpdate (Id "y") 2 (idUpdate (Id "x") 1 idEmpty) (Id "y")) = Some 2.
Proof. reflexivity. Qed.

Definition beq_r (a b: r): bool :=
  match (a, b) with
  | (Reactive an, Reactive bn) => Nat.eqb an bn
  end.


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

Fixpoint beq_T (a b: T): bool :=
  match (a, b) with
  | (a1 ~> a2, b1 ~> b2) => (beq_T a1 b1) && (beq_T a2 b2)
  | (Unit, Unit) => true
  | (Option a1, Option b1) => beq_T a1 b1
  | (List a1, List b1) => beq_T a1 b1
  | (Remote Pa, Remote Pb) => beq_peerType Pa Pb
  | (Signal a1, Signal b1) => beq_T a1 b1
  | (Var a1, Var b1) => beq_T a1 b1
  | _ => false
  end.


(** placement types **)
Inductive S : Type :=
  | on : T -> P -> S.

Infix "on" := on (at level 20).

Definition beq_S (a b: S): bool :=
  match (a, b) with
  | (aT on aP, bT on bP) => (beq_T aT bT) && (beq_peerType aP bP)
  end.

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
  | asLocal       : t -> S -> t 
  | asLocalFrom   : t -> S -> t -> t
  | asLocalIn     : id -> t -> t -> S -> t
  | asLocalInFrom : id -> t -> t -> S -> t -> t
  | signal : t -> t
  | var    : t -> t
  | now    : t -> t
  | set    : t -> t -> t
  | peerApp          : p -> t
  | reactApp      : r -> t
  
  (* Added to make testing easier. *)
  | tnat   : nat -> t.


Fixpoint beq_t (a b: t): bool :=
  match (a, b) with
  | (lambda ax aT at_, lambda bx bT bt)
      => (beq_id ax bx) && (beq_T aT bT) && (beq_t at_ bt)
  | (app at1 at2, app bt1 bt2)    => (beq_t at1 bt1) && (beq_t at2 bt2)
  | (idApp xa, idApp xb)          => beq_id xa xb
  | (unit, unit)                  => true
  | (none aT, none bT)            => beq_T aT bT
  | (some at1, some bt1)          => beq_t at1 bt1
  | (nil aT, nil bT)              => beq_T aT bT
  | (cons at1 at2, cons bt1 bt2)  => (beq_t at1 bt1) && (beq_t at2 bt2)
  | (asLocal at1 aS, asLocal bt1 bS) 
      => (beq_t at1 bt1) && (beq_S aS bS)
  | (asLocalFrom at1 aS at2, asLocalFrom bt1 bS bt2)
      => (beq_t at1 bt1) && (beq_S aS bS) && (beq_t at2 bt2)
  | (asLocalIn ax at1 at2 aS, asLocalIn bx bt1 bt2 bS)
      => (beq_id ax bx) && (beq_t at1 at2) && (beq_t at2 bt2) && (beq_S aS bS)
  | (asLocalInFrom ax at1 at2 aS at3, asLocalInFrom bx bt1 bt2 bS bt3)
      => (beq_id ax bx) && (beq_t at1 at2) && (beq_t at2 bt2) && (beq_S aS bS) && (beq_t at3 bt3)
  | (signal at1, signal bt1)      => beq_t at1 bt1
  | (var at1, var bt1)            => beq_t at1 bt1
  | (now at1, now bt1)            => beq_t at1 bt1
  | (set at1 at2, set bt1 bt2)    => (beq_t at1 bt1) && (beq_t at2 bt2)
  | (peerApp ap, peerApp bp)      => beq_peerInst ap bp
  | (reactApp ar, reactApp br)  => beq_r ar br
  | (tnat an, tnat bn)            => Nat.eqb an bn
  | _                             => false
  end.

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


Fixpoint appears_free_in_t x t : Prop :=
  match t with
  | lambda x' type t => if beq_id x x' then False else appears_free_in_t x t
  | app t0 t1 => appears_free_in_t x t0 \/ appears_free_in_t x t1
  | idApp x' => if beq_id x x' then True else False
  | unit => False
  | none type => False
  | some t => appears_free_in_t x t
  | nil type => False
  | cons t0 t1 => appears_free_in_t x t0 \/ appears_free_in_t x t1
  | asLocal t type => appears_free_in_t x t
  | asLocalFrom t0 type t1 => appears_free_in_t x t0 \/ appears_free_in_t x t1
  | asLocalIn x' t0 t1 type =>
    if beq_id x x'
      then appears_free_in_t x t0
      else appears_free_in_t x t0 \/ appears_free_in_t x t1
  | asLocalInFrom x' t0 t1 type t2 =>
    if beq_id x x'
      then appears_free_in_t x t0 \/ appears_free_in_t x t2
      else appears_free_in_t x t0 \/ appears_free_in_t x t1 \/ appears_free_in_t x t2
  | signal t => appears_free_in_t x t
  | var t => appears_free_in_t x t
  | now t => appears_free_in_t x t
  | set t0 t1 => appears_free_in_t x t0 \/ appears_free_in_t x t1
  | peerApp peer => False
  | reactApp reactive => False
  | tnat n => False
  end.

Fixpoint appears_free_in_s x s : Prop :=
  match s with
  | placed x' type s0 t0 =>
    if beq_id x x'
      then appears_free_in_t x s0
      else appears_free_in_t x s0 \/ appears_free_in_s x t0
  | pUnit => False
  end.

Definition closed_t t := forall x, ~ appears_free_in_t x t.

Definition closed_s s := forall x, ~ appears_free_in_s x s.
