Require Import ReTierSyntax.
Require Import Maps.
Require Coq.Lists.ListSet.


(** auxiliary functions for aggegation **)


  Fixpoint Phi (ties: Ties) (p0 p1: P) (peers: Coq.Lists.ListSet.set p) (value: t) (type: T): option t :=
    match (ties (p0, p1), peers) with
    | (Some multiple, Datatypes.cons peer peers) => match Phi ties p0 p1 peers value type with
      | Some peers => Some (cons value peers)
      | None => None
      end
    | (Some multiple, Datatypes.nil) => Some (nil type)
    | (Some optional, Datatypes.cons peer Datatypes.nil) => Some (some value)
    | (Some optional, Datatypes.nil) => Some (none type)
    | (Some optional, _) => None
    | (Some single, Datatypes.cons peer Datatypes.nil) => Some value
    | (Some single, _) => None
    | (Some mNone, _) => None
    | (None, _) => None
    end.


(* --------------------------------------------------------------------- *)


Fixpoint subst_t (id: id) (value: t) (term: t): t :=
  match term with
  | lambda id' type term =>
    if beq_id id id'
      then lambda id' type term
      else lambda id' type (subst_t id value term)
  | app term0 term1 => app (subst_t id value term0) (subst_t id value term1)
  | idApp id' => if beq_id id id' then value else term
  | unit => unit
  | none type => none type
  | some term => some (subst_t id value term)
  | nil type => nil type
  | cons term0 term1 => cons (subst_t id value term0) (subst_t id value term1)
  | asLocal term type => asLocal (subst_t id value term) type
  | asLocalFrom term0 type term1 => asLocalFrom (subst_t id value term0) type (subst_t id value term1)
  | asLocalIn id' term0 term1 type =>
    if beq_id id id'
      then asLocalIn id' (subst_t id value term0) term1 type
      else asLocalIn id' (subst_t id value term0) (subst_t id value term1) type
  | asLocalInFrom id' term0 term1 type term2 =>
    if beq_id id id'
      then asLocalInFrom id' (subst_t id value term0) term1 type (subst_t id value term2)
      else asLocalInFrom id' (subst_t id value term0) (subst_t id value term1) type (subst_t id value term2)
  | signal term => signal (subst_t id value term)
  | var term => var (subst_t id value term)
  | now term => now (subst_t id value term)
  | set term0 term1 => set (subst_t id value term0) (subst_t id value term1)
  | peerApp peer => peerApp peer
  | reactApp reactive => reactApp reactive
  | tnat n => tnat n
  end.

Notation "[ id :=_t value ] term" := (subst_t id value term) (at level 40).

Fixpoint subst_s (id: id) (value: t) (term: s): s :=
  match term with
  | placed id' type term0 term1 =>
    if beq_id id id'
      then placed id' type (subst_t id value term0) term1
      else placed id' type (subst_t id value term0) (subst_s id value term1)
  | pUnit => pUnit
  end.

Notation "[ id :=_s value ] term" := (subst_s id value term) (at level 40).


Definition peerInsts := ListSet.set p.
Definition noPeerInsts := ListSet.empty_set p.

Definition eq_peerInstDec : forall x y : p, {x = y} + {x <> y}.
  decide equality. decide equality.
Defined.

Definition pISet_add (x: p) (s: peerInsts): peerInsts :=
  ListSet.set_add eq_peerInstDec x s.

Definition pISet_mem (x: p) (s: peerInsts): bool :=
  ListSet.set_mem eq_peerInstDec x s.



Inductive reactiveSystem : Type :=
  | ReactiveSystem: r -> ListSet.set r -> reactMap t -> reactiveSystem.

Definition emptyReactSys := ReactiveSystem (Reactive 0) (ListSet.empty_set r) (reactEmpty).




(** Context for local evaluation. **)
Inductive leContext: Type :=
  | LeContext: Ties -> peerTyping -> peerInsts -> P -> reactiveSystem-> leContext.

Definition emptyLeContext := LeContext noTies noPeers noPeerInsts (Peer "_") emptyReactSys.


Definition getPeerInstancesOfType (context: leContext) (PT: P): ListSet.set p :=
    match context with
    | LeContext _ typing insts _ _
      =>  let hasTypePT (pInst: p): bool :=
            match (typing pInst) with
            | None => false
            | Some PT2 => beq_peerType PT PT2
            end
          in Coq.Lists.List.filter hasTypePT insts
    end.

Definition getReactSys (context: leContext): reactiveSystem :=
  match context with
  | LeContext _ _ _ _ sys => sys
  end.




(* TODO: replace by lemma and prove it *)
Hypothesis term_eq_dec : forall x y:t, {x = y} + {x <> y}.
(* TODO: replace by lemma and prove it *)
Hypothesis react_eq_dec : forall x y:r, {x = y} + {x <> y}.


Definition reactDomainMem (x: r) (sys: reactiveSystem): bool :=
  match sys with
  | ReactiveSystem _ dom _ => ListSet.set_mem react_eq_dec x dom
  end.




(* no distinction here between allocation of signals and vars *)
Definition reactAlloc (t: t) (rho: reactiveSystem): r * reactiveSystem :=
  match rho with
  | ReactiveSystem nextReact dom map
    => match nextReact with
       | Reactive n => (nextReact,
                        ReactiveSystem (Reactive (n+1))
                                       (ListSet.set_add react_eq_dec nextReact dom)
                                       (reactUpdate nextReact t map))
      end
  end.

Definition updateVar (r: r) (v: t) (rho: reactiveSystem): reactiveSystem :=
  match rho with
  | ReactiveSystem next dom map => ReactiveSystem next dom
                                                  (reactUpdate r v map)
  end.

Definition currentValue (r: r) (rho: reactiveSystem): (option t) * reactiveSystem :=
  match rho with
  | ReactiveSystem _ _ map => (map r, rho)
  end.


(* ...just a little reminder
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
    | remoteApp        : r -> t

    (* Added to make testing easier. *)
    | tnat   : nat -> t.
*)
Reserved Notation "'[' x ':=' s ']' tm" (at level 40).

Fixpoint subst (x:id) (s tm: t): t :=
  match tm with
  | lambda y T body => if beq_id x y then lambda y T body else lambda y T (subst x s body)
  | app f arg => app (subst x s f) (subst x s arg)
  | idApp y   => if beq_id x y then s else (idApp y)
  | unit      => unit
  | none T    => none T
  | some t    => some (subst x s t)
  | nil T     => nil T
  | cons t1 t2 => cons (subst x s t1) (subst x s t2)
  | asLocal t (*:*) S => asLocal (subst x s t) (*:*) S
  | asLocalFrom t1 (*:*) S (*from*) t2
      => asLocalFrom (subst x s t1) (*:*) S (*from*) t2
  | asLocalIn y (*=*) t1 (*in*) t2 (*:*) S
      =>  if beq_id x y then asLocalIn y (*=*) (subst x s t1) (*in*) t2 (*:*) S
          else asLocalIn y (*=*) (subst x s t1) (*in*) (subst x s t2) (*:*) S
  | asLocalInFrom y (*=*) t1 (*in*) t2 (*:*) S (*from*) t3
      =>  if beq_id x y
          then asLocalInFrom y (*=*) (subst x s t1) (*in*) t2 (*:*) S (*from*) t3
          else asLocalInFrom y (*=*) (subst x s t1) (*in*) (subst x s t2) (*:*) S (*from*) t3
  | signal t => signal (subst x s t)
  | var t => var (subst x s t)
  | now t => now (subst x s t)
  | set t1 t2 => set (subst x s t1) (subst x s t2)
  | peerApp p => peerApp p
  | reactApp r => reactApp r
  | tnat n => tnat n    (*TODO: remove tnat *)
  end
where "'[' x ':=' s ']' tm" := (subst x s tm).



Inductive either (a b: Type) :=
  | Left:  a -> either a b
  | Right: b -> either a b.

(** Notation for local evaluation. **)
(*Reserved Notation "context '|>' t1 'L==>' t2" (at level 40).*)
Reserved Notation "context '||>' t1 'Ld==>' t2 ',' rho" (at level 50).


Inductive localStep : leContext -> t -> (either r t) -> reactiveSystem -> Prop :=
  (* E_Context *)
  | E_App: forall context x T t v,
        (* context ||> (app (lambda x T t) v) Ld==> Right _ _ ([x := v] t), getReactSys context *)
        (* substitution 'subst' replaced by 'subst_t' *)
        context ||> (app (lambda x T t) v) Ld==> Right _ _ ([x :=_t v] t), getReactSys context

  (* remote access *)
  | E_AsLocal: forall context peers ties P0 P1 v v' T _x _y _z,
        context = LeContext ties _x _y P0 _z ->
        peers = getPeerInstancesOfType context P1 ->
        Some v' = Phi ties P0 P1 peers v T ->
        context ||> (asLocal v (*:*) (T on P1)) Ld==> Right _ _ v', getReactSys context

  | E_Comp: forall context x v t T P1,
        context ||> (asLocalIn x (*=*) v (*in*) t (*:*) (T on P1))
          (* Ld==> Right _ _ (asLocal ([x := v] t) (*:*) (T on P1)), getReactSys context *)
          (* substitution 'subst' replaced by 'subst_t' *)
          Ld==> Right _ _ (asLocal ([x :=_t v] t) (*:*) (T on P1)), getReactSys context

  | E_Remote: forall context t t' T P1 context' ties typing peers P0 _x,
        context = LeContext ties typing peers P0 _x ->
        context' = LeContext ties typing peers P1 _x ->
        context' ||> t Ld==> Right _ _ t', getReactSys context  ->
        context ||> asLocal t (*:*) (T on P1) Ld==> Right _ _ (asLocal t' (*:*) (T on P1)), getReactSys context

  | E_AsLocalFrom: forall context v T P1 p,
        context ||> asLocalFrom v (*:*) (T on P1) (*from*) p Ld==> Right _ _ v, getReactSys context

  | E_CompFrom: forall context x v t S p,
        context ||> asLocalInFrom x (*=*) v (*in*) t (*:*) S (*from*) p
          (* Ld==> Right _ _ (asLocalFrom ([x := v] t) (*:*) S (*from*) p), getReactSys context *)
          (* substitution 'subst' replaced by 'subst_t' *)
          Ld==> Right _ _ (asLocalFrom ([x :=_t v] t) (*:*) S (*from*) p), getReactSys context

  | E_RemoteFrom: forall context t t' T P1 p context' ties typing peers P0 _x,
        context = LeContext ties typing peers P0 _x ->
        context' = LeContext ties typing peers P1 _x ->
        context' ||> t Ld==> Right _ _ t', getReactSys context  ->
        context ||> asLocalFrom t (*:*) (T on P1) (*from*) p
          Ld==> Right _ _ (asLocalFrom t' (*:*) (T on P1) (*from*) p), getReactSys context

  (* reactive rules *)
  | E_ReactiveVar: forall context v r rho',
        (r, rho') = reactAlloc v (getReactSys context) ->
        context ||> var v Ld==> Left _ _ r, rho'
  | E_Signal: forall context t r rho',
        (r, rho') = reactAlloc t (getReactSys context) ->
        context ||> signal t Ld==> Left _ _ r, rho'
  | E_Set: forall context v r rho',
        rho' = updateVar r v (getReactSys context) ->
        context ||> (set (reactApp r) (*:=*) v) Ld==> Right _ _ unit, rho'
  | E_Now: forall context t r rho',
        (Some t, rho') = currentValue r (getReactSys context) ->
        context ||> now (reactApp r) Ld==> Right _ _ t, rho'

where "context '||>' t1 'Ld==>' t2 ',' rho" := (localStep context t1 t2 (getReactSys context)).

Notation "context '|>' t1 'L==>' t2" := (context ||> t1 Ld==> t2, getReactSys context) (at level 40).


Hint Constructors localStep.
  