Require Import ReTierSyntax.
Require Import Maps.
Require Coq.Lists.ListSet.


Definition peerInsts := ListSet.set p.
Definition noPeerInsts := ListSet.empty_set p.

Definition eq_peerInstDec : forall x y : p, {x = y} + {x <> y}.
  decide equality. decide equality.
Defined.

Definition pISet_add (x: p) (s: peerInsts): peerInsts :=
  ListSet.set_add eq_peerInstDec x s.

Definition pISet_mem (x: p) (s: peerInsts): bool :=
  ListSet.set_mem eq_peerInstDec x s.


(**
 ----------------------------------------------------------------------------
  Below we use the following notation taken from the informal specification.

  rho   : reactive system
 ----------------------------------------------------------------------------
**)

Reserved Notation "peerTyping ; Ties ; peerInsts ; P |> t ; rho ==> t' ; rho'"
  (at level 40,
   Ties at next level, peerInsts at next level, P at next level,
   t at next level, rho at next level, t' at next level).



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


Fixpoint subst_t x value term: t :=
  match term with
  | lambda x' type term =>
    if beq_id x x'
      then lambda x' type term
      else lambda x' type (subst_t x value term)
  | app term0 term1 => app (subst_t x value term0) (subst_t x value term1)
  | idApp x' => if beq_id x x' then value else term
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
    if beq_id x x'
      then lambda x' type (subst_s_locality x value term RemoteVar)
      else lambda x' type (subst_s_locality x value term locality)
  | app term0 term1 => app (subst_s_locality x value term0 locality) (subst_s_locality x value term1 locality)
  | idApp x' => match locality with
    | LocalOrRemoteVar => if beq_id x x' then value else term
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
    if beq_id x x'
      then asLocalIn x' (subst_s_locality x value term0 locality) (subst_s_locality x value term1 RemoteVar) type
      else asLocalIn x' (subst_s_locality x value term0 locality) (subst_s_locality x value term1 LocalOrRemoteVar) type
  | asLocalInFrom x' term0 term1 type term2 =>
    if beq_id x x'
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
    if beq_id x x'
      then placed x' type (subst_s_locality x value term0 LocalOrRemoteVar) term1
      else placed x' type (subst_s_locality x value term0 LocalOrRemoteVar) (subst_s x value term1)
  | pUnit => pUnit
  end.

Notation "[ id :=_s value ] term" := (subst_s id value term) (at level 30).



Inductive reactiveSystem : Type :=
  | ReactiveSystem: r -> ListSet.set r -> reactMap t -> reactiveSystem.

Definition emptyReactSys := ReactiveSystem (Reactive 0) (ListSet.empty_set r) (reactEmpty).

Definition getPeerInstancesOfType (typing: peerTyping) (insts: peerInsts) (PT: P): ListSet.set p :=
  let hasTypePT (pInst: p): bool :=
    match (typing pInst) with
    | None => false
    | Some PT2 => beq_peerType PT PT2
    end
  in Coq.Lists.List.filter hasTypePT insts.

Lemma react_eq_dec : forall x y:r, {x = y} + {x <> y}.
Proof. repeat decide equality. Qed.

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


Inductive localStep : peerTyping -> Ties -> peerInsts -> P -> t -> reactiveSystem -> t -> reactiveSystem -> Prop :=

  (* TODO: E_Context *)

  | E_App: forall ties peerTyping peerInsts P x v t T rho,
      value v ->
        peerTyping; ties; peerInsts; P |> app (lambda x T t) v; rho
        ==> [x :=_t v] t; rho

  (* remote access *)

  | E_AsLocal: forall ties peerTyping peerInsts P0 P1 v v' T rho peers,
      value v ->
      getPeerInstancesOfType peerTyping peerInsts P1 = peers ->
      Phi ties P0 P1 peers v T = Some v' ->
        peerTyping; ties; peerInsts; P0 |> asLocal v (*:*) (T on P1); rho
        ==> v'; rho

  | E_Comp: forall ties peerTyping peerInsts P0 P1 x v t T rho,
      value v ->
        peerTyping; ties; peerInsts; P0 |> asLocalIn x (*=*) v (*in*) t (*:*) (T on P1); rho
        ==> asLocal ([x :=_t v] t) (*:*) (T on P1); rho

  | E_Remote: forall ties peerTyping peerInsts P0 P1 t t' T rho rho',
      peerTyping; ties; peerInsts; P1 |> t; rho ==> t'; rho' ->
        peerTyping; ties; peerInsts; P0 |> asLocal t (*:*) (T on P1); rho
        ==> asLocal t' (*:*) (T on P1); rho'

  | E_AsLocalFrom: forall ties peerTyping peerInsts P0 P1 v p T rho,
      value v ->
        peerTyping; ties; peerInsts; P0 |> asLocalFrom v (*:*) (T on P1) (*from*) p; rho
        ==> v; rho

  | E_CompFrom: forall ties peerTyping peerInsts P0 P1 x v p t T rho,
      value v ->
        peerTyping; ties; peerInsts; P0 |> asLocalInFrom x (*=*) v (*in*) t (*:*) (T on P1) (*from*) p; rho
        ==> asLocalFrom ([x :=_t v] t) (*:*) (T on P1) (*from*) p; rho

  | E_RemoteFrom: forall ties peerTyping peerInsts P0 P1 t t' p T rho rho',
      peerTyping; ties; peerInsts; P1 |> t; rho ==> t'; rho' ->
        peerTyping; ties; peerInsts; P0 |> asLocalFrom t (*:*) (T on P1) (*from*) p; rho
        ==> asLocalFrom t' (*:*) (T on P1) (*from*) p; rho'

  (* reactive rules *)

  | E_ReactiveVar: forall ties peerTyping peerInsts P v r rho rho',
      (r, rho') = reactAlloc v rho ->
      value v ->
        peerTyping; ties; peerInsts; P |> var v; rho
        ==> reactApp r; rho'

  | E_Signal: forall ties peerTyping peerInsts P t r rho rho',
      (r, rho') = reactAlloc t rho ->
        peerTyping; ties; peerInsts; P |> signal t; rho
        ==> reactApp r; rho'

  | E_Set: forall ties peerTyping peerInsts P v r rho rho',
      rho' = updateVar r v rho ->
      value v ->
        peerTyping; ties; peerInsts; P |> set (reactApp r) (*:=*) v; rho
        ==> unit; rho'

  | E_Now: forall ties peerTyping peerInsts P t r rho rho',
      (Some t, rho') = currentValue r rho ->
        peerTyping; ties; peerInsts; P |> now (reactApp r); rho
        ==> t; rho'

where "peerTyping ; Ties ; peerInsts ; P |> t ; rho ==> t' ; rho'" := (localStep peerTyping Ties peerInsts P t rho t' rho').

