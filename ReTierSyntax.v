Require Import Coq.Strings.String.
Require Import Maps.
Require Coq.Lists.ListSet.


(** identifier **)

Inductive id : Type := Id : string -> id.

Definition id_dec: forall x y : id, {x = y} + {x <> y}.
  repeat decide equality.
Defined.


(** peer instance **)

Inductive p : Type := PeerInstance: nat -> p.

Definition peer_instance_dec: forall x y : p, {x = y} + {x <> y}.
  repeat decide equality.
Defined.


(** peer type **)

Inductive P : Type := Peer: string -> P.

Definition peer_dec: forall x y : P, {x = y} + {x <> y}.
  repeat decide equality.
Defined.


(** reactive instance **)

Inductive r: Type := Reactive: nat -> r.

Definition reactive_dec: forall x y : r, {x = y} + {x <> y}.
  repeat decide equality.
Defined.


(** environments **)

Definition idMap (V: Type) := partial_map id V.
Definition idEmpty {V: Type} := p_empty id V.
Definition idUpdate {V: Type} (k: id) (v: V) (m: idMap V): idMap V :=
  p_update (fun x y => if id_dec x y then true else false) m k v.

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


(** types **)

Inductive T : Type :=
  | Arrow  : T -> T -> T
  | Unit   : T
  | Option : T -> T
  | List   : T -> T
  | Remote : P -> T
  | Signal : T -> T
  | Var    : T -> T
  | Tnat   : T.

Notation "T1 ~> T2" := (Arrow T1 T2) (at level 30, right associativity).

Fixpoint beq_T (a b: T): bool :=
  match (a, b) with
  | (a1 ~> a2, b1 ~> b2) => (beq_T a1 b1) && (beq_T a2 b2)
  | (Unit, Unit) => true
  | (Option a1, Option b1) => beq_T a1 b1
  | (List a1, List b1) => beq_T a1 b1
  | (Remote Pa, Remote Pb) => if peer_dec Pa Pb then true else false
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
  | (aT on aP, bT on bP) => (beq_T aT bT) && (if peer_dec aP bP then true else false)
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
  | asLocalIn     : id -> T -> t -> t -> S -> t
  | asLocalInFrom : id -> T -> t -> t -> S -> t -> t
  | signal : t -> t
  | var    : t -> t
  | now    : t -> t
  | set    : t -> t -> t
  | peerApp  : (ListSet.set p) -> t
  | reactApp : r -> t
  | tnat     : nat -> t.

(*
Notation "\ x ; T , t" := (lambda (Id x) T t) (at level 80, left associativity).
Example testNotationLambda1: (\ "z" ; Unit , unit) = (lambda (Id "z") Unit unit).
Proof. reflexivity. Qed.
*)

Fixpoint beq_t (a b: t): bool :=
  match (a, b) with
  | (lambda ax aT at_, lambda bx bT bt)
      => (if id_dec ax bx then true else false) && (beq_T aT bT) && (beq_t at_ bt)
  | (app at1 at2, app bt1 bt2)    => (beq_t at1 bt1) && (beq_t at2 bt2)
  | (idApp xa, idApp xb)          => if id_dec xa xb then true else false
  | (unit, unit)                  => true
  | (none aT, none bT)            => beq_T aT bT
  | (some at1, some bt1)          => beq_t at1 bt1
  | (nil aT, nil bT)              => beq_T aT bT
  | (cons at1 at2, cons bt1 bt2)  => (beq_t at1 bt1) && (beq_t at2 bt2)
  | (asLocal at1 aS, asLocal bt1 bS) 
      => (beq_t at1 bt1) && (beq_S aS bS)
  | (asLocalFrom at1 aS at2, asLocalFrom bt1 bS bt2)
      => (beq_t at1 bt1) && (beq_S aS bS) && (beq_t at2 bt2)
  | (asLocalIn ax aT at1 at2 aS, asLocalIn bx bT bt1 bt2 bS)
      => (if id_dec ax bx then true else false) && (beq_T aT bT) && (beq_t at1 at2) && (beq_t at2 bt2) && (beq_S aS bS)
  | (asLocalInFrom ax aT at1 at2 aS at3, asLocalInFrom bx bT bt1 bt2 bS bt3)
      => (if id_dec ax bx then true else false) && (beq_T aT bT) && (beq_t at1 at2) && (beq_t at2 bt2) && (beq_S aS bS) && (beq_t at3 bt3)
  | (signal at1, signal bt1)      => beq_t at1 bt1
  | (var at1, var bt1)            => beq_t at1 bt1
  | (now at1, now bt1)            => beq_t at1 bt1
  | (set at1 at2, set bt1 bt2)    => (beq_t at1 bt1) && (beq_t at2 bt2)
  | (peerApp ap, peerApp bp)      => (Nat.eqb (List.length ap) (List.length bp)) && (Nat.eqb (List.length ap) (List.length (ListSet.set_union peer_instance_dec ap bp)))
  | (reactApp ar, reactApp br)    => if reactive_dec ar br then true else false
  | (tnat an, tnat bn)            => Nat.eqb an bn
  | _                             => false
  end.


(** values **)

Inductive value : t -> Prop :=
  | v_lambda : forall x T t, value (lambda x T t)
  | v_unit : value unit
  | v_none : forall T, value (none T)
  | v_some : forall t, value t -> value (some t)
  | v_nil : forall T, value (nil T)
  | v_cons : forall t0 t1, value t0 -> value t1 -> value (cons t0 t1)
  | v_peerApp : forall p, value (peerApp p)
  | v_reactApp : forall r, value (reactApp r)
  | v_tnat : forall n, value (tnat n).

Inductive transmittable_type : T -> Prop :=
  | U_Unit : transmittable_type Unit
  | U_Option : forall T, transmittable_type T -> transmittable_type (Option T)
  | U_List : forall T, transmittable_type T -> transmittable_type (List T)
  | U_Remote : forall P, transmittable_type (Remote P)
  | U_Signal : forall T, transmittable_type T -> transmittable_type (Signal T)
  | U_Tnat : transmittable_type Tnat.


(** placed terms **)

Inductive s : Type :=
  | placed : id -> S -> t -> s -> s
  | pUnit  : s.


(** ties **)

Inductive multiplicity : Type := Multiple | Optional | Single | None.

Inductive tie : Type := Tie : P -> P -> multiplicity -> tie.

Notation "P1 -*-> P2" := (Tie (Peer P1) (Peer P2) Multiple) (at level 20).
Notation "P1 -?-> P2" := (Tie (Peer P1) (Peer P2) Optional) (at level 20).
Notation "P1 -1-> P2" := (Tie (Peer P1) (Peer P2) Single) (at level 20).
Notation "P1 -0-> P2" := (Tie (Peer P1) (Peer P2) None) (at level 20).

Example testNotation_multipleTie: "x" -*-> "y" = Tie (Peer "x") (Peer "y") Multiple.
Proof. reflexivity. Qed.
Example testNotation_optionalTie: "x" -?-> "y" = Tie (Peer "x") (Peer "y") Optional.
Proof. reflexivity. Qed.
Example testNotation_singleTie: "x" -1-> "y" = Tie (Peer "x") (Peer "y") Single.
Proof. reflexivity. Qed.
Example testNotation_noneTie: "x" -0-> "y" = Tie (Peer "x") (Peer "y") None.
Proof. reflexivity. Qed.

Definition ties := total_map (P * P) multiplicity.

Definition NoTies: ties := t_empty None.

Definition ties_add (new_tie: tie) (current_ties: ties): ties :=
  match new_tie with Tie p1 p2 mult => t_update
    (fun x y => match x, y with (x1, x2), (y1, y2) =>
      if peer_dec x1 y1 then if peer_dec x2 y2 then true else false else false
    end) current_ties (p1, p2) mult
  end.

Example test_tiesAdd_1: (ties_add ("x" -1-> "y") NoTies) (Peer "x", Peer "y") = Single.
Proof. reflexivity. Qed.

Example test_tiesAdd_2: (ties_add ("x" -1-> "y") NoTies) (Peer "y", Peer "x") = None.
Proof. reflexivity. Qed.

Notation "'Ties' [ ]" := NoTies (at level 50).

Notation "'Ties' [ t , .. , u ]" :=
  (ties_add t .. (ties_add u NoTies) ..)
  (at level 50).


(** peer instances **)

Definition typed_peer_instances := ListSet.set (p * P).

Definition NoTypedInstances: typed_peer_instances := Datatypes.nil.

Fixpoint typed_peer_instances_add
    (peer: (p * P)) (instances: typed_peer_instances): typed_peer_instances :=
  match instances, peer with
  | Datatypes.nil, _ => Datatypes.cons peer Datatypes.nil
  | Datatypes.cons (p', P') instances, (p, P) =>
    if peer_instance_dec p p'
      then typed_peer_instances_add peer instances
      else Datatypes.cons (p', P') (typed_peer_instances_add peer instances)
  end.

Fixpoint typed_peer_instances_type
    (instances: typed_peer_instances) (p: p): option P :=
  match instances with
  | Datatypes.nil => Datatypes.None
  | Datatypes.cons (p', P') instances =>
    if peer_instance_dec p p'
      then Datatypes.Some P'
      else typed_peer_instances_type instances p
  end.

Fixpoint typed_peer_instances_all
    (instances: typed_peer_instances): ListSet.set p :=
  match instances with
  | Datatypes.nil =>
    Datatypes.nil
  | Datatypes.cons (p, _) instances =>
    Datatypes.cons p (typed_peer_instances_all instances)
  end.

Fixpoint typed_peer_instances_of_type
    (instances: typed_peer_instances) (P: P): ListSet.set p :=
  match instances with
  | Datatypes.nil =>
    Datatypes.nil
  | Datatypes.cons (p', P') instances =>
    if peer_dec P P'
      then Datatypes.cons p' (typed_peer_instances_of_type instances P)
      else typed_peer_instances_of_type instances P
  end.

Example test_typedPeerInstancesAdd_1: typed_peer_instances_type
                                        (typed_peer_instances_add (PeerInstance 1, Peer "x")
                                          (typed_peer_instances_add (PeerInstance 2, Peer "y")
                                            NoTypedInstances))
                                        (PeerInstance 2) = Some (Peer "y").
Proof. reflexivity. Qed.

Notation "p : P" := (PeerInstance p, Peer P) (at level 40).

Notation "'TypedInstances' [ ]" := NoTypedInstances (at level 50).

Notation "'TypedInstances' [ p , .. , q ]" :=
  (typed_peer_instances_add p .. (typed_peer_instances_add q NoTypedInstances) ..)
  (at level 50).


Definition peer_instances := ListSet.set p.

Definition NoInstances: peer_instances := ListSet.empty_set p.

Definition peer_instances_add
  (instance: p) (instances: ListSet.set p): ListSet.set p :=
  ListSet.set_add peer_instance_dec instance instances.

Notation "'Instance' p" := (peer_instances_add (PeerInstance p) NoInstances) (at level 50).

Notation "'Instances' [ ]" := NoInstances (at level 50).

Notation "'Instances' [ i , .. , j ]" :=
  (peer_instances_add (PeerInstance i) .. (peer_instances_add (PeerInstance j) NoInstances) ..)
  (at level 50).


Inductive program := Program : ties -> typed_peer_instances -> program.

Definition peer_ties program: ties :=
  match program with Program ties _ => ties end.

Definition peer_instances_all program: ListSet.set p :=
  match program with
    Program _ instances => typed_peer_instances_all instances
  end.

Definition peer_instances_of_type program P: ListSet.set p :=
  match program with
    Program _ instances => typed_peer_instances_of_type instances P
  end.

Definition peers_tied program P0 P1: Prop :=
  (peer_ties program) (P0, P1) <> None /\ (peer_ties program) (P1, P0) <> None.


Inductive var_locality : Type := LocalOrRemoteVar | RemoteVar.

Fixpoint appears_free_in_t_locality x t locality : Prop :=
  match t with
  | lambda x' type t => if id_dec x x' then appears_free_in_t_locality x t RemoteVar else appears_free_in_t_locality x t locality
  | app t0 t1 => appears_free_in_t_locality x t0 locality \/ appears_free_in_t_locality x t1 locality
  | idApp x' => match locality with
    | LocalOrRemoteVar => if id_dec x x' then True else False
    | RemoteVar => False
    end
  | unit => False
  | none type => False
  | some t => appears_free_in_t_locality x t locality
  | nil type => False
  | cons t0 t1 => appears_free_in_t_locality x t0 locality \/ appears_free_in_t_locality x t1 locality
  | asLocal t type => appears_free_in_t_locality x t LocalOrRemoteVar
  | asLocalFrom t0 type t1 => appears_free_in_t_locality x t0 LocalOrRemoteVar \/ appears_free_in_t_locality x t1 locality
  | asLocalIn x' type0 t0 t1 type1 =>
    if id_dec x x'
      then appears_free_in_t_locality x t0 locality \/ appears_free_in_t_locality x t1 RemoteVar
      else appears_free_in_t_locality x t0 locality \/ appears_free_in_t_locality x t1 LocalOrRemoteVar
  | asLocalInFrom x' type0 t0 t1 type1 t2 =>
    if id_dec x x'
      then appears_free_in_t_locality x t0 locality \/ appears_free_in_t_locality x t1 RemoteVar \/ appears_free_in_t_locality x t2 locality
      else appears_free_in_t_locality x t0 locality \/ appears_free_in_t_locality x t1 LocalOrRemoteVar \/ appears_free_in_t_locality x t2 locality
  | signal t => appears_free_in_t_locality x t locality
  | var t => appears_free_in_t_locality x t locality
  | now t => appears_free_in_t_locality x t locality
  | set t0 t1 => appears_free_in_t_locality x t0 locality \/ appears_free_in_t_locality x t1 locality
  | peerApp peer => False
  | reactApp reactive => False
  | tnat n => False
  end.

Definition appears_free_in_t x t := appears_free_in_t_locality x t LocalOrRemoteVar.

Fixpoint appears_free_in_s x s : Prop :=
  match s with
  | placed x' type s0 t0 =>
    if id_dec x x'
      then appears_free_in_t x s0
      else appears_free_in_t x s0 \/ appears_free_in_s x t0
  | pUnit => False
  end.

Definition closed_t t := forall x, ~ appears_free_in_t x t.

Definition closed_s s := forall x, ~ appears_free_in_s x s.
