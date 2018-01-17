Require Import ReTierSyntax.
Require Import Maps.
Require Coq.Lists.List.
Require Coq.Lists.ListSet.

(**
 ----------------------------------------------------------------------------
  Below we use the following notation taken from the informal specification.

  rho   : reactive system
  theta : peer instances
  P     : current peer
 ----------------------------------------------------------------------------
**)

Reserved Notation "program :: theta : P |> t ; rho == theta' ==> t' ; rho'"
  (at level 40,
   theta at next level, P at next level, t at next level,
   rho at next level, theta' at next level, t' at next level).

Reserved Notation "program :: s ; rho == theta ==> s' ; rho'"
  (at level 40,
  s at next level, rho at next level, theta at next level, s' at next level).


(** auxiliary functions for aggegation **)

Fixpoint Phi (ties: ties) (P0 P1: P) (peers: ListSet.set p) (value: t) (type: T): option t :=
  match ties (P0, P1), peers with
  | Multiple, Datatypes.cons peer peers => match Phi ties P0 P1 peers value type with
    | Datatypes.Some peers => Datatypes.Some (cons value peers)
    | Datatypes.None => Datatypes.None
    end
  | Multiple, Datatypes.nil => Datatypes.Some (nil type)
  | Optional, Datatypes.cons peer Datatypes.nil => Datatypes.Some (some value)
  | Optional, Datatypes.nil => Datatypes.Some (none type)
  | Optional, _ => Datatypes.None
  | Single, Datatypes.cons peer Datatypes.nil => Datatypes.Some value
  | Single, _ => Datatypes.None
  | None, _ => Datatypes.None
  end.


(* --------------------------------------------------------------------- *)


Fixpoint subst_t x value term: t :=
  match term with
  | lambda x' type term =>
    if id_dec x x'
      then lambda x' type term
      else lambda x' type (subst_t x value term)
  | app term0 term1 => app (subst_t x value term0) (subst_t x value term1)
  | idApp x' => if id_dec x x' then value else term
  | unit => unit
  | none type => none type
  | some term => some (subst_t x value term)
  | nil type => nil type
  | cons term0 term1 => cons (subst_t x value term0) (subst_t x value term1)
  | asLocal term type => asLocal term type
  | asLocalFrom term0 type term1 => asLocalFrom term0 type (subst_t x value term1)
  | asLocalIn x' term0 term1 type => asLocalIn x' (subst_t x value term0) term1 type
  | asLocalInFrom x' term0 term1 type term2 => asLocalInFrom x' (subst_t x value term0) term1 type (subst_t x value term2)
  | signal term => signal (subst_t x value term)
  | var term => var (subst_t x value term)
  | now term => now (subst_t x value term)
  | set term0 term1 => set (subst_t x value term0) (subst_t x value term1)
  | peerApp peer => peerApp peer
  | reactApp reactive => reactApp reactive
  | tnat n => tnat n
  end.

Notation "[ id :=_t value ] term" := (subst_t id value term) (at level 30).

Fixpoint subst_s_locality x value term locality: t :=
  match term with
  | lambda x' type term =>
    if id_dec x x'
      then lambda x' type (subst_s_locality x value term RemoteVar)
      else lambda x' type (subst_s_locality x value term locality)
  | app term0 term1 => app (subst_s_locality x value term0 locality) (subst_s_locality x value term1 locality)
  | idApp x' => match locality with
    | LocalOrRemoteVar => if id_dec x x' then value else term
    | RemoteVar => term
    end
  | unit => unit
  | none type => none type
  | some term => some (subst_s_locality x value term locality)
  | nil type => nil type
  | cons term0 term1 => cons (subst_s_locality x value term0 locality) (subst_s_locality x value term1 locality)
  | asLocal term type => asLocal (subst_s_locality x value term LocalOrRemoteVar) type
  | asLocalFrom term0 type term1 => asLocalFrom (subst_s_locality x value term0 LocalOrRemoteVar) type (subst_s_locality x value term1 locality)
  | asLocalIn x' term0 term1 type =>
    if id_dec x x'
      then asLocalIn x' (subst_s_locality x value term0 locality) (subst_s_locality x value term1 RemoteVar) type
      else asLocalIn x' (subst_s_locality x value term0 locality) (subst_s_locality x value term1 LocalOrRemoteVar) type
  | asLocalInFrom x' term0 term1 type term2 =>
    if id_dec x x'
      then asLocalInFrom x' (subst_s_locality x value term0 locality) (subst_s_locality x value term1 RemoteVar) type (subst_s_locality x value term2 locality)
      else asLocalInFrom x' (subst_s_locality x value term0 locality) (subst_s_locality x value term1 LocalOrRemoteVar) type (subst_s_locality x value term2 locality)
  | signal term => signal (subst_s_locality x value term locality)
  | var term => var (subst_s_locality x value term locality)
  | now term => now (subst_s_locality x value term locality)
  | set term0 term1 => set (subst_s_locality x value term0 locality) (subst_s_locality x value term1 locality)
  | peerApp peer => peerApp peer
  | reactApp reactive => reactApp reactive
  | tnat n => tnat n
  end.

Fixpoint subst_s x value term: s :=
  match term with
  | placed x' type term0 term1 =>
    if id_dec x x'
      then placed x' type (subst_s_locality x value term0 LocalOrRemoteVar) term1
      else placed x' type (subst_s_locality x value term0 LocalOrRemoteVar) (subst_s x value term1)
  | pUnit => pUnit
  end.

Notation "[ id :=_s value ] term" := (subst_s id value term) (at level 30).



Definition reactive_system := list t.

Definition reactive_system_lookup (r: r) (system: reactive_system): option t :=
  match r with Reactive n => List.nth_error system n end.

Definition reactive_system_add (t: t) (system: reactive_system): r * reactive_system :=
  (Reactive (length system), List.app system (Datatypes.cons t Datatypes.nil)).

Fixpoint reactive_system_update (r: r) (t: t) (system: reactive_system): reactive_system :=
  match r, system with
  | _, Datatypes.nil => Datatypes.nil
  | Reactive O, Datatypes.cons _ system => Datatypes.cons t system
  | Reactive (Datatypes.S n), Datatypes.cons t' system =>
    Datatypes.cons t' (reactive_system_update (Reactive n) t system)
  end.


(*
Definition context := t -> t.

Inductive is_context: context -> Prop :=
  | C_Hole: is_context (fun t => t)
  | C_App_Left: forall t0 context,
      is_context context ->
      is_context (fun t => app (context t) t0)
  | C_App_Right: forall v context,
      value v ->
      is_context context ->
      is_context (fun t => app v (context t)).
*)

(*
Inductive evaluation_congruence: t -> t -> t -> t -> Prop :=
  | C_App_Left: forall t0 t0' t1,
      evaluation_congruence t0 t0' (app t0 t1) (app t0' t1)
  | C_App_Right: forall v t1 t1',
      value v ->
      evaluation_congruence t1 t1' (app v t1) (app v t1')
  | C_Some: forall t t',
      evaluation_congruence t t' (some t) (some t').
*)

Inductive evaluation_t : program -> peer_instances -> P -> t -> reactive_system -> peer_instances -> t -> reactive_system -> Prop :=

(*
  | E_Context: forall program theta theta' P t t' rho rho' context,
      is_context context ->
      t <> context t ->
      program :: theta : P |> t; rho == theta' ==> t'; rho' ->
      program :: theta : P |> context t; rho == theta' ==> context t'; rho'
*)
(*
  | E_Congruence: forall program theta theta' P t0 t0' t1 t1' rho rho',
      evaluation_congruence t0 t0' t1 t1' ->
      program :: theta : P |> t0; rho == theta' ==> t0'; rho' ->
      program :: theta : P |> t1; rho == theta' ==> t1'; rho'
*)

  (* contextual congruence *)

  | EC_App_Left: forall program theta theta' P t0 t0' t1 rho rho',
      program :: theta : P |> t0; rho == theta' ==> t0'; rho' ->
      program :: theta : P |> app t0 t1; rho == theta' ==> app t0' t1; rho'

  | EC_App_Right: forall program theta theta' P v t1 t1' rho rho',
      value v ->
      program :: theta : P |> t1; rho == theta' ==> t1'; rho' ->
      program :: theta : P |> app v t1; rho == theta' ==> app v t1'; rho'

  | EC_Some: forall program theta theta' P t t' rho rho',
      program :: theta : P |> t; rho == theta' ==> t'; rho' ->
      program :: theta : P |> some t; rho == theta' ==> some t; rho'

  | EC_Cons_Left: forall program theta theta' P t0 t0' t1 rho rho',
      program :: theta : P |> t0; rho == theta' ==> t0'; rho' ->
      program :: theta : P |> cons t0 t1; rho == theta' ==> cons t0' t1; rho'

  | EC_Cons_Right: forall program theta theta' P v t1 t1' rho rho',
      value v ->
      program :: theta : P |> t1; rho == theta' ==> t1'; rho' ->
      program :: theta : P |> cons v t1; rho == theta' ==> cons v t1'; rho'

  | EC_AsLocalFrom: forall program theta theta' P S t0 t1 t1' rho rho',
      program :: theta : P |> t1; rho == theta' ==> t1'; rho' ->
        program :: theta : P |> asLocalFrom t0 (*:*) S (*from*) t1; rho
        == theta' ==> asLocalFrom t0 (*:*) S (*from*) t1'; rho'

  | EC_Comp: forall program theta theta' P S x t0 t0' t1 rho rho',
      program :: theta : P |> t0; rho == theta' ==> t0'; rho' ->
        program :: theta : P |> asLocalIn x (*=*) t0 (*in*) t1 (*:*) S; rho
        == theta' ==> asLocalIn x (*=*) t0' (*in*) t1 (*:*) S; rho'

  | EC_CompFrom_Right: forall program theta theta' P S x t0 t1 t2 t2' rho rho',
      program :: theta : P |> t2; rho == theta' ==> t2'; rho' ->
        program :: theta : P |> asLocalInFrom x (*=*) t0 (*in*) t1 (*:*) S (*from*) t2; rho
        == theta' ==> asLocalInFrom x (*=*) t0 (*in*) t1 (*:*) S (*from*) t2'; rho'

  | EC_CompFrom_Left: forall program theta theta' P S x v t0 t0' t1 rho rho',
      value v ->
      program :: theta : P |> t0; rho == theta' ==> t0'; rho' ->
        program :: theta : P |> asLocalInFrom x (*=*) t0 (*in*) t1 (*:*) S (*from*) v; rho
        == theta' ==> asLocalInFrom x (*=*) t0' (*in*) t1 (*:*) S (*from*) v; rho'

  | EC_Var: forall program theta theta' P t t' rho rho',
      program :: theta : P |> t; rho == theta' ==> t'; rho' ->
      program :: theta : P |> var t; rho == theta' ==> var t; rho'

  | EC_Now: forall program theta theta' P t t' rho rho',
      program :: theta : P |> t; rho == theta' ==> t'; rho' ->
      program :: theta : P |> now t; rho == theta' ==> now t; rho'

  | EC_Set_Left: forall program theta theta' P t0 t0' t1 rho rho',
      program :: theta : P |> t0; rho == theta' ==> t0'; rho' ->
      program :: theta : P |> set t0 (*:=*) t1; rho == theta' ==> set t0' (*:=*) t1; rho'

  | EC_Set_Right: forall program theta theta' P v t1 t1' rho rho',
      value v ->
      program :: theta : P |> t1; rho == theta' ==> t1'; rho' ->
      program :: theta : P |> set v (*:=*) t1; rho == theta' ==> set v (*:=*) t1'; rho'

  (* local computation *)

  | E_App: forall program theta P x v t T rho,
      value v ->
        program :: theta : P |> app (lambda x T t) v; rho
        == theta ==> [x :=_t v] t; rho

  (* remote access *)

  | E_AsLocal: forall program theta P0 P1 v v' T rho,
      value v ->
      Phi (peer_ties program) P0 P1 (peer_instances_of_type program P1) v T = Some v' ->
        program :: theta : P0 |> asLocal v (*:*) (T on P1); rho
        == theta ==> v'; rho

  | E_Comp: forall program theta P0 P1 x v t T rho,
      value v ->
        program :: theta : P0 |> asLocalIn x (*=*) v (*in*) t (*:*) (T on P1); rho
        == peer_instances_of_type program P1 ==> asLocal ([x :=_t v] t) (*:*) (T on P1); rho

  | E_Remote: forall program theta theta' P0 P1 t t' T rho rho',
      program :: peer_instances_of_type program P1 : P1 |> t; rho == theta' ==> t'; rho' ->
        program :: theta : P0 |> asLocal t (*:*) (T on P1); rho
        == theta' ==> asLocal t' (*:*) (T on P1); rho'

  | E_AsLocalFrom: forall program theta P0 P1 v p T rho,
      value v ->
        program :: theta : P0 |> asLocalFrom v (*:*) (T on P1) (*from*) (peerApp p); rho
        == theta ==> v; rho

  | E_CompFrom: forall program theta P0 P1 x v p t T rho,
      value v ->
        program :: theta : P0 |> asLocalInFrom x (*=*) v (*in*) t (*:*) (T on P1) (*from*) (peerApp p); rho
        == single_peer_instance p ==> asLocalFrom ([x :=_t v] t) (*:*) (T on P1) (*from*) (peerApp p); rho

  | E_RemoteFrom: forall program theta theta' P0 P1 t t' p T rho rho',
      program :: single_peer_instance p : P1 |> t; rho == theta' ==> t'; rho' ->
        program :: theta : P0 |> asLocalFrom t (*:*) (T on P1) (*from*) (peerApp p); rho
        == theta' ==> asLocalFrom t' (*:*) (T on P1) (*from*) (peerApp p); rho'

  (* reactive rules *)

  | E_ReactiveVar: forall program theta P v r rho rho',
      value v ->
      reactive_system_add v rho = (r, rho') ->
        program :: theta : P |> var v; rho
        == theta ==> reactApp r; rho'

  | E_Signal: forall program theta P t r rho rho',
      reactive_system_add t rho = (r, rho')->
        program :: theta : P |> signal t; rho
        == theta ==> reactApp r; rho'

  | E_Set: forall program theta P v r rho rho',
      reactive_system_update r v rho = rho'->
      value v ->
        program :: theta : P |> set (reactApp r) (*:=*) v; rho
        == theta ==> unit; rho'

  | E_Now: forall program theta P t r rho,
      reactive_system_lookup r rho = Some t ->
        program :: theta : P |> now (reactApp r); rho
        == theta ==> t; rho

where "program :: theta : P |> t ; rho == theta' ==> t' ; rho'" := (evaluation_t program theta P t rho theta' t' rho').


Inductive evaluation_s : program -> s -> reactive_system -> peer_instances -> s -> reactive_system -> Prop :=

  | E_Placed: forall program theta P x t t' s T rho rho',
      program :: peer_instances_of_type program P : P |> t; rho == theta ==> t'; rho' ->
        program :: placed x (T on P) t s; rho
        == theta ==> placed x (T on P) t' s; rho'

  | E_Placed_Val: forall program P x v s T rho,
      value v ->
        program :: placed x (T on P) v s; rho
        == peer_instances_all program ==> [x :=_s v] s; rho

where "program :: s ; rho == theta ==> s' ; rho'" := (evaluation_s program s rho theta s' rho').

