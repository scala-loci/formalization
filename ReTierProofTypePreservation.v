Require Import ReTierSyntax.
Require Import ReTierStaticSemantics.
Require Import ReTierDynamicSemantics.
Require Import ReTierProofSubstitution.
Require Import ReTierProofAggregation.


Lemma tied_not_None: forall context P1 P2,
  areTied context P1 P2 = true -> getTieMult context (P1, P2) <> None.
Proof.
  intros context P1 P2. destruct context as [typing ties reacEnv placeEnv varEnv].
  unfold areTied. simpl. destruct (ties (P1, P2)).
  1-2: intros; congruence.
Qed.

Lemma tied_not_SomeMNone: forall context P1 P2,
  areTied context P1 P2 = true -> getTieMult context (P1, P2) <> (Some mNone).
Proof.
  intros context P1 P2. destruct context as [typing ties reacEnv placeEnv varEnv].
  unfold areTied. simpl. destruct (ties (P1, P2)).

  1-2: unfold not; intros.
  1: destruct m.
  1-5: congruence.
Qed.




(* reminder:
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

(* static context *)
Inductive context: Type :=
  | Context: peerTyping -> Ties -> reactEnv -> placeEnv -> varEnv -> P -> context.

(* dynamic context *)
Inductive leContext: Type :=
  | LeContext: Ties -> peerTyping -> peerInsts -> P -> reactiveSystem-> leContext.
*)
(*
Lemma preservation_nonReactive: forall t t' T statContext dynContext,
    statContext |- t \in T -> 
    dynContext |> t L==> Right _ _ t' ->
    exists T',
    statContext |- t' \in T'.
*)
(* stronger formulation *)
Lemma preservation_nonReactive: forall t t' T peerInsts typing ties reactEnv placeEnv varEnv P reactSys,
    Context typing ties reactEnv placeEnv varEnv P |- t \in T -> 
    LeContext ties typing peerInsts P reactSys |> t L==> Right _ _ t' ->
    exists T',
    Context typing ties reactEnv placeEnv varEnv P |- t' \in T'.
Proof.
  intros t t' T peerInsts typing ties reactEnv placeEnv varEnv P reactSys.
  destruct t as [ x Tx body (* lambda : id -> T -> t -> t *)
                | fct arg   (* app    : t -> t -> t *)
                | x         (* idApp  : id -> t *)
                |           (* unit   : t *)
                | Tn        (* none   : T -> t *)
                | ts        (* some   : t -> t *)
                | Tn        (* nil    : T -> t *)
                | tc tl     (* cons   : t -> t -> t *)
                | targ S    (* asLocal       : t -> S -> t  *)
                | targ S tfrom    (* asLocalFrom   : t -> S -> t -> t *)
                | x tassign tin S (* asLocalIn     : id -> t -> t -> S -> t *)
                | targ tassign tin S tfrom (* asLocalInFrom : id -> t -> t -> S -> t -> t *)
                | ts        (* signal : t -> t *)
                | tv        (* var    : t -> t *)
                | tn        (* now    : t -> t *)
                | ttarget tsource (* set    : t -> t -> t *)
                | p         (* peerApp  : p -> t *)
                | r         (* reactApp : r -> t *)
                (* TODO: remove ? *)
                | n         (* tnat   : nat -> t *)
  ].
  (* value cases,
     i.e. cases in which no evaluation step is possible, because t is value *)
    1,4-8,  (* cases  t = lambda x Tx body
                      | unit
                      | none Tn
                      | some ts
                      | nil Tn
                      | cons tc tl *)
    17-19,  (* cases  t = peerApp p
                      | reactApp r
                      | tnat n (* TODO: remove? *) *)
  (* Left reactive cases,
     i.e. cases in which no step is possible, because step would lead to Left _ _ t',
     but Right _ _ t' is given *)
    13-14,  (* cases  t = signal ts
                      | var tv *)
  (* variable case.
     Cannot take evaluation step on variable, but case cannot occur since substitution
     is applied before variable gets evaluated. *)
    3:      (* case   t = idApp x *)
      intros H_stat H_dyn; inversion H_dyn.
  
  Focus 2. (* t = asLocal targ S *)
    intros H_stat H_dyn. destruct S as [Targ P1].
    inversion H_stat. simpl in H2. rewrite H2 in H6, H7.
    exists T.


    (*destruct dynContext.*) inversion H_dyn. (* why does this create: asLocal t'0 ... ??? *)
(*
Focus 2.
apply T_AsLocal with (P0 := P).
1: reflexivity.
2,3: assumption.
*)

    symmetry in H13. inversion H13. (* adds hypothesis ties = ties0 *)
    rewrite H18, H21 in H16.
    (* for lemma instantiation:
        - p0 := P0
        - p1 := P1
        - peers := peers
        - value := targ
        - value_type := Targ
    *)
    apply aggregation with (p0 := P0) (p1 := P1) (peers := peers) (value := targ) (value_type := Targ).
    1-4: rewrite H2.
    3: simpl; symmetry.
    3-5: assumption.
    1: apply tied_not_None.
    2: apply tied_not_SomeMNone.
 
    1-2: assumption.
    Focus 1. eapply T_AsLocal.
    Focus 1. reflexivity.
    2,3: simpl; assumption.
    
    Abort.