Require Import Maps.
Require Import Coq.Strings.String.
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


(** types **)

Inductive T : Type :=
  | Arrow : T -> T -> T
  | Unit : T
  | Option : T -> T
  | List : T -> T
  | Remote : P -> T
  | Signal : T -> T
  | Var : T -> T
  | Tnat : T.

Notation "T1 ~> T2" := (Arrow T1 T2) (at level 30, right associativity).


(** placement types **)

Inductive S : Type :=
  | on : T -> P -> S.

Infix "on" := on (at level 20).


(** terms **)

Inductive t : Type := 
  | lambda : id -> T -> t -> t
  | app : t -> t -> t
  | idApp : id -> t
  | unit : t
  | none : T -> t
  | some : t -> t
  | nil : T -> t
  | cons : t -> t -> t
  | asLocal : t -> S -> t 
  | asLocalFrom : t -> S -> t -> t
  | asLocalIn : id -> T -> t -> t -> S -> t
  | asLocalInFrom : id -> T -> t -> t -> S -> t -> t
  | signal : t -> t
  | var : t -> t
  | now : t -> t
  | set : t -> t -> t
  | peerApp : (ListSet.set p) -> t
  | reactApp : r -> t
  | tnat : nat -> t.


(** placed terms **)

Inductive s : Type :=
  | placed : id -> S -> t -> s -> s
  | pUnit  : s.


(** values **)

Inductive value_t : t -> Prop :=
  | v_lambda : forall x T t, value_t (lambda x T t)
  | v_unit : value_t unit
  | v_none : forall T, value_t (none T)
  | v_some : forall t, value_t t -> value_t (some t)
  | v_nil : forall T, value_t (nil T)
  | v_cons : forall t0 t1, value_t t0 -> value_t t1 -> value_t (cons t0 t1)
  | v_peerApp : forall p, value_t (peerApp p)
  | v_reactApp : forall r, value_t (reactApp r)
  | v_tnat : forall n, value_t (tnat n).

Inductive value_s : s -> Prop :=
  | v_pUnit : value_s pUnit.

Inductive transmittable_type : T -> Prop :=
  | U_Unit : transmittable_type Unit
  | U_Option : forall T, transmittable_type T -> transmittable_type (Option T)
  | U_List : forall T, transmittable_type T -> transmittable_type (List T)
  | U_Remote : forall P, transmittable_type (Remote P)
  | U_Signal : forall T, transmittable_type T -> transmittable_type (Signal T)
  | U_Tnat : transmittable_type Tnat.



(** ties **)

Inductive multiplicity : Type := Multiple | Optional | Single | None.

Inductive tie : Type := Tie : P -> P -> multiplicity -> tie.

Notation "P1 -*-> P2" := (Tie (Peer P1) (Peer P2) Multiple) (at level 20).
Notation "P1 -?-> P2" := (Tie (Peer P1) (Peer P2) Optional) (at level 20).
Notation "P1 -1-> P2" := (Tie (Peer P1) (Peer P2) Single) (at level 20).
Notation "P1 -0-> P2" := (Tie (Peer P1) (Peer P2) None) (at level 20).

Definition ties := total_map (P * P) multiplicity.

Definition NoTies: ties := t_empty None.

Definition ties_add (new_tie: tie) (current_ties: ties): ties :=
  match new_tie with Tie p1 p2 mult => t_update
    (fun x y => match x, y with (x1, x2), (y1, y2) =>
      if peer_dec x1 y1 then if peer_dec x2 y2 then true else false else false
    end) current_ties (p1, p2) mult
  end.

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

Definition is_remote_subterm subterm term : Prop :=
  match term with
  | lambda x type t => False
  | app t0 t1 => False
  | idApp _x => False
  | unit => False
  | none type => False
  | some t => False
  | nil type => False
  | cons t0 t1 => False
  | asLocal t type => t = subterm
  | asLocalFrom t0 type t1 => t0 = subterm
  | asLocalIn x' type0 t0 t1 type1 => t1 = subterm
  | asLocalInFrom x' type0 t0 t1 type1 t2 => t1 = subterm
  | signal t => False
  | var t => False
  | now t => False
  | set t0 t1 => False
  | peerApp peer => False
  | reactApp reactive => False
  | tnat n => False
  end.

Definition is_reducing_subterm_t subterm term : Prop :=
  match term with
  | lambda x type t => False
  | app t0 t1 => t0 = subterm /\ ~ value_t t0 \/ t1 = subterm /\ ~ value_t t1 /\ value_t t0
  | idApp _x => False
  | unit => False
  | none type => False
  | some t => t = subterm /\ ~ value_t t
  | nil type => False
  | cons t0 t1 => t0 = subterm /\ ~ value_t t0 \/ t1 = subterm /\ ~ value_t t1 /\ value_t t0
  | asLocal t type => t = subterm /\ ~ value_t t
  | asLocalFrom t0 type t1 => t0 = subterm /\ ~ value_t t0 /\ value_t t1 \/ t1 = subterm /\ ~ value_t t1
  | asLocalIn x' type0 t0 t1 type1 => t0 = subterm /\ ~ value_t t0
  | asLocalInFrom x' type0 t0 t1 type1 t2 => t0 = subterm /\ ~ value_t t0 /\ value_t t2 \/ t2 = subterm /\ ~ value_t t2
  | signal t => False
  | var t => t = subterm /\ ~ value_t t
  | now t => t = subterm /\ ~ value_t t
  | set t0 t1 => t0 = subterm /\ ~ value_t t0 \/ t1 = subterm /\ ~ value_t t1 /\ value_t t0
  | peerApp peer => False
  | reactApp reactive => False
  | tnat n => False
  end.

Definition is_reducing_subterm_s subterm term : Prop :=
  match term with
  | placed x type t s => t = subterm /\ ~ value_t t
  | pUnit => False
  end.

Definition is_subterm_t subterm term : Prop :=
  match term with
  | lambda x type t => t = subterm
  | app t0 t1 => t0 = subterm \/ t1 = subterm
  | idApp _x => False
  | unit => False
  | none type => False
  | some t => t = subterm
  | nil type => False
  | cons t0 t1 => t0 = subterm \/ t1 = subterm
  | asLocal t type => t = subterm
  | asLocalFrom t0 type t1 => t0 = subterm \/ t1 = subterm
  | asLocalIn x' type0 t0 t1 type1 => t0 = subterm \/ t1 = subterm
  | asLocalInFrom x' type0 t0 t1 type1 t2 => t0 = subterm \/ t1 = subterm \/ t2 = subterm
  | signal t => t = subterm
  | var t => t = subterm
  | now t => t = subterm
  | set t0 t1 => t0 = subterm \/ t1 = subterm
  | peerApp peer => False
  | reactApp reactive => False
  | tnat n => False
  end.

Definition is_subterm_s subterm term : Prop :=
  match term with
  | placed x type t s => t = subterm
  | pUnit => False
  end.


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
