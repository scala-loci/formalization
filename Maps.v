Require Import Coq.Strings.String.



(*
Definition total_map (A: Type) := id -> A.
Definition t_empty {A: Type} (default: A) : total_map A :=
  (fun _ => default).
Definition t_update {A: Type} (m: total_map A) (x: id) (v: A) : total_map A :=
  fun x' => if beq_id x' x then v else m x'.

Definition partial_map (A: Type) := total_map (option A).
*)


Definition total_map (K V: Type) := K -> V.

Definition t_empty {K V: Type} (default: V) : total_map K V :=
  (fun _ => default).

Definition t_update {K V: Type} (eqFct: K -> K -> bool) (m: total_map K V) (k: K) (v: V): total_map K V :=
  fun k' => if eqFct k' k then v else m k'.


(*
Definition genPair_update {K V: Type} (eqFct: K -> K -> bool) (m: total_map K V) (z: K*V): total_map K V :=
  match z with
  | (k,v) => genSep_update eqFct m k v
  end.
*)

Definition partial_map (K V: Type) := total_map K (option V).

Definition p_empty (K V: Type) : partial_map K V := (fun _ => None).

Definition p_update {K V: Type} (eqFct: K -> K -> bool) (m: partial_map K V) (k: K) (v: V): partial_map K V :=
  t_update eqFct m k (Some v).