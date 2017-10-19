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


