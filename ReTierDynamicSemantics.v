Require Import ReTierSyntax.
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
