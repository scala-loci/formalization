Require Import ReTierSyntax.
Require Import ReTierStaticSemantics.
Require Import ReTierDynamicSemantics.
Require Import ReTierProofContext.
Require Import ReTierProofSubstitution.
Require Import ReTierProofAggregation.




Lemma tied_not_None: forall program P1 P2,
  are_peers_tied program P1 P2 -> (peer_ties program) (P1, P2) <> None.
Proof.
  intros program P1 P2.
  unfold are_peers_tied. destruct ((peer_ties program) (P1, P2)).
  1-2: intros; congruence.
Qed.

Lemma tied_not_SomeMNone: forall program P1 P2,
  are_peers_tied program P1 P2 -> (peer_ties program) (P1, P2) <> (Some mNone).
Proof.
  intros program P1 P2.
  unfold are_peers_tied. simpl. destruct ((peer_ties program) (P1, P2)).

  1-2: unfold not; intros.
  1: destruct m.
  1-5: congruence.
Qed.




Lemma substitution_t_relaxed:
  forall program Psi Delta Gamma P x t T v U,
  program :: Psi; Delta; idUpdate x U Gamma; P |- t : T ->
  program :: Psi; Delta; Gamma; P |- v : U ->
  program :: Psi; Delta; Gamma; P |- [x :=_t v] t : T.
Admitted.



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


(*
Lemma transmittable_peer_invariant: forall t T typing ties reactEnv placeEnv varEnv P P',
  transmittable_value t ->
  transmittable_type T ->
  Context typing ties reactEnv placeEnv emptyVarEnv P |- t \in T ->
  Context typing ties reactEnv placeEnv varEnv P' |- t \in T.
Proof.
  intros t T typing ties reactEnv placeEnv varEnv P P' Htrans_t Htrans_T Hstat.
  generalize dependent T.
  (*
  inversion Htrans_t; subst; inversion Hstat; subst.
  - apply T_Unit.
  - apply T_None.
  - apply T_Some. 
  *)
  
  induction t as [  x Tx body IHbody (* lambda : id -> T -> t -> t *)
                  | fct IHfct arg IHarg   (* app    : t -> t -> t *)
                  | x         (* idApp  : id -> t *)
                  |           (* unit   : t *)
                  | Tn        (* none   : T -> t *)
                  | ts IHts        (* some   : t -> t *)
                  | Tn        (* nil    : T -> t *)
                  | tc IHtc tl IHtl     (* cons   : t -> t -> t *)
                  | targ IHtarg S    (* asLocal       : t -> S -> t  *)
                  | targ IHtarg S tfrom IHtfrom    (* asLocalFrom   : t -> S -> t -> t *)
                  | x tassign IHtassign tin IHtin S (* asLocalIn     : id -> t -> t -> S -> t *)
                  | targ tassign IHtassign tin IHtin S tfrom IHtfrom (* asLocalInFrom : id -> t -> t -> S -> t -> t *)
                  | ts IHts        (* signal : t -> t *)
                  | tv IHtv        (* var    : t -> t *)
                  | tn IHtn        (* now    : t -> t *)
                  | ttarget IHttarget tsource IHtsource (* set    : t -> t -> t *)
                  | p         (* peerApp  : p -> t *)
                  | r         (* reactApp : r -> t *)
                  (* TODO: remove ? *)
                  | n         (* tnat   : nat -> t *)
  ]; intros T Htrans_T Hstat; inversion Htrans_t; inversion Hstat; subst.
  - apply T_Unit.
  - apply T_None.
  - apply T_Some. apply IHts.
    + assumption.
    + inversion Htrans_T. assumption.
    + assumption.
  - apply T_Nil.
  - apply T_Cons.
    + apply IHtc.
      * assumption.
      * inversion Htrans_T. subst. assumption.
      * assumption.
    + apply IHtl.
      * assumption.
      * assumption.
      * assumption.
  - apply T_Peer. assumption.
  - apply T_Reactive. assumption.
  - apply T_Nat.
Qed.

Lemma transmittable_peer_invariant_gen: forall t T typing ties reactEnv placeEnv placeEnv' varEnv varEnv' P P',
  transmittable_value t ->
  transmittable_type T ->
  Context typing ties reactEnv placeEnv varEnv P |- t \in T ->
  Context typing ties reactEnv placeEnv' varEnv' P' |- t \in T.
Admitted.
(*Proof.
  intros t T typing ties reactEnv placeEnv varEnv P P' Htrans_t Htrans_T Hstat.
  generalize dependent T.
  (*
  inversion Htrans_t; subst; inversion Hstat; subst.
  - apply T_Unit.
  - apply T_None.
  - apply T_Some. 
  *)
  
  induction t as [  x Tx body IHbody (* lambda : id -> T -> t -> t *)
                  | fct IHfct arg IHarg   (* app    : t -> t -> t *)
                  | x         (* idApp  : id -> t *)
                  |           (* unit   : t *)
                  | Tn        (* none   : T -> t *)
                  | ts IHts        (* some   : t -> t *)
                  | Tn        (* nil    : T -> t *)
                  | tc IHtc tl IHtl     (* cons   : t -> t -> t *)
                  | targ IHtarg S    (* asLocal       : t -> S -> t  *)
                  | targ IHtarg S tfrom IHtfrom    (* asLocalFrom   : t -> S -> t -> t *)
                  | x tassign IHtassign tin IHtin S (* asLocalIn     : id -> t -> t -> S -> t *)
                  | targ tassign IHtassign tin IHtin S tfrom IHtfrom (* asLocalInFrom : id -> t -> t -> S -> t -> t *)
                  | ts IHts        (* signal : t -> t *)
                  | tv IHtv        (* var    : t -> t *)
                  | tn IHtn        (* now    : t -> t *)
                  | ttarget IHttarget tsource IHtsource (* set    : t -> t -> t *)
                  | p         (* peerApp  : p -> t *)
                  | r         (* reactApp : r -> t *)
                  (* TODO: remove ? *)
                  | n         (* tnat   : nat -> t *)
  ]; intros T Htrans_T Hstat; inversion Htrans_t; inversion Hstat; subst.
  - apply T_Unit.
  - apply T_None.
  - apply T_Some. apply IHts.
    + assumption.
    + inversion Htrans_T. assumption.
    + assumption.
  - apply T_Nil.
  - apply T_Cons.
    + apply IHtc.
      * assumption.
      * inversion Htrans_T. subst. assumption.
      * assumption.
    + apply IHtl.
      * assumption.
      * assumption.
      * assumption.
  - apply T_Peer. assumption.
  - apply T_Reactive. assumption.
  - apply T_Nat.
Qed.
*)

Lemma transmittable_value_type: forall v T typing ties reactEnv placeEnv varEnv P,
  transmittable_value v ->
  Context typing ties reactEnv placeEnv varEnv P |- v \in T ->
  transmittable_type T.
Proof.
(*
  intros v T typing ties reactEnv placeEnv varEnv P Htrans Hstat.
  generalize dependent v.
  induction T as [ T1 IHT1 T2 IHT2 (* Arrow  : T -> T -> T *)
                  |   (* Unit   : T *)
                  |   (* Option : T -> T *)
                  |   (* List   : T -> T *)
                  |   (* Remote : P -> T *)
                  |   (* Signal : T -> T *)
                  |   (* Var    : T -> T *)
                  |   (* Tnat   : T *) ].
  - intros v Htrans Hstat.
    (* inversion Htrans; subst; inversion Hstat; subst. *)
    inversion Htrans; subst.
    + inversion Hstat.
    + inversion Hstat.
    + inversion Hstat.
    + inversion Hstat.
    + inversion Hstat.
    + inversion Hstat.
    + (* TODO: fix problem *) admit.
    + inversion Hstat.
  - intros v Htrans Hstat.
    inversion Htrans; subst; try apply U_Unit; inversion Hstat.
  - intros v Htrans Hstat. inversion Htrans; subst.
    + inversion Hstat.
    + inversion Hstat; subst.
    + inversion Hstat. 
  
  induction v as [  (* lambda : id -> T -> t -> t *)
                  | (* app    : t -> t -> t *)
                  | (* idApp  : id -> t *)
                  |           (* unit   : t *)
                  | Tn        (* none   : T -> t *)
                  | ts IHts        (* some   : t -> t *)
                  | Tn        (* nil    : T -> t *)
                  | tc IHtc tl IHtl     (* cons   : t -> t -> t *)
                  | (* asLocal       : t -> S -> t  *)
                  | (* asLocalFrom   : t -> S -> t -> t *)
                  | (* asLocalIn     : id -> t -> t -> S -> t *)
                  | (* asLocalInFrom : id -> t -> t -> S -> t -> t *)
                  | ts IHts        (* signal : t -> t *)
                  | tv IHtv        (* var    : t -> t *)
                  | (* now    : t -> t *)
                  | (* set    : t -> t -> t *)
                  | p         (* peerApp  : p -> t *)
                  | (* reactApp : r -> t *)
                  (* TODO: remove ? *)
                  | n         (* tnat   : nat -> t *)
  ]; inversion Htrans. 
  - inversion Hstat. apply U_Unit.
  - inversion Hstat. apply U_Option. subst. appl
  ; inversion Hstat; subst. 
  - apply U_Unit.
  - apply U_Option. apply 

*)
Admitted.
*)

Lemma preservation_nonReactive: forall t t' T theta theta' program Psi Delta Gamma P rho rho',
  program :: Psi; Delta; Gamma; P |- t : T -> 
  program :: theta : P |> t; rho == theta' ==> t'; rho' ->
  program :: Psi; Delta; Gamma; P |- t' : T.
Proof.
intros t t' T theta theta' program Psi Delta Gamma P rho rho'.
intros H_stat H_dyn.
generalize dependent P.
generalize dependent T.
generalize dependent t'.
generalize dependent Gamma.
generalize dependent theta.
generalize dependent theta'.
induction t as [  x Tx body (* lambda : id -> T -> t -> t *)
                  | fct IHfct arg IHarg   (* app    : t -> t -> t *)
                  | x         (* idApp  : id -> t *)
                  |           (* unit   : t *)
                  | Tn        (* none   : T -> t *)
                  | ts IHts        (* some   : t -> t *)
                  | Tn        (* nil    : T -> t *)
                  | tc IHtc tl IHtl     (* cons   : t -> t -> t *)
                  | targ IHtarg S    (* asLocal       : t -> S -> t  *)
                  | targ IHtarg S tfrom IHtfrom    (* asLocalFrom   : t -> S -> t -> t *)
                  | x tassign IHtassign tin IHtin S (* asLocalIn     : id -> t -> t -> S -> t *)
                  | targ tassign IHtassign tin IHtin S tfrom IHtfrom (* asLocalInFrom : id -> t -> t -> S -> t -> t *)
                  | ts IHts        (* signal : t -> t *)
                  | tv IHtv        (* var    : t -> t *)
                  | tn IHtn        (* now    : t -> t *)
                  | ttarget IHttarget tsource IHtsource (* set    : t -> t -> t *)
                  | p         (* peerApp  : p -> t *)
                  | r         (* reactApp : r -> t *)
                  (* TODO: remove ? *)
                  | n         (* tnat   : nat -> t *)
  ].

- (* lambda *)
  intros theta' theta varEnv t' T P H_stat H_dyn.
  inversion H_dyn.
- (* app *)
  intros theta' theta varEnv t' T P H_stat H_dyn.
  inversion H_stat.
  inversion H_dyn; subst.
  + eapply T_App; try eassumption.
    eapply IHfct; eassumption.
  + eapply T_App; try eassumption.
    eapply IHarg; eassumption.
  + eapply substitution_t_relaxed; try eassumption. (* lemma has no proof yet... useless if not povable *)
    inversion H6.
    eassumption.
- (* idApp *)
  intros theta' theta varEnv t' T P H_stat H_dyn.
  inversion H_dyn.
- (* unit *)
  intros theta' theta varEnv t' T P H_stat H_dyn.
  inversion H_dyn.
- (* none *)
  intros theta' theta varEnv t' T P H_stat H_dyn.
  inversion H_dyn.
- (* some *)
  intros theta' theta varEnv t' T P H_stat H_dyn.
  inversion H_dyn.
  assumption.
- (* nil *)
  intros theta' theta varEnv t' T P H_stat H_dyn.
  inversion H_dyn.
- (* cons *)
  intros theta' theta varEnv t' T P H_stat H_dyn.
  inversion H_stat.
  inversion H_dyn; subst.
  + apply T_Cons; try assumption.
    eapply IHtc; eassumption.
  + apply T_Cons; try assumption.
    eapply IHtl; eassumption.


- (* asLocal *)
  intros theta' theta varEnv t' T P H_stat H_dyn.
  inversion H_stat.
  subst.

  apply tied_not_None in H8 as H3.
  apply tied_not_SomeMNone in H8 as H4.
  inversion H_dyn; subst.
  + eapply aggregation.
    * eassumption.
    * eassumption.
    * eassumption.
    * eassumption.
    * eassumption.
    * eapply transmittable_value_typing in H2; eassumption.
    * eapply transmittable_value_typing; eassumption.
  + eapply T_AsLocal.
    * assumption.
    * eapply IHtarg; eassumption.
    * assumption.
    * assumption.


- (* asLocalFrom *)
  intros theta' theta varEnv t' T P H_stat H_dyn.
  inversion H_stat.
  subst.
  inversion H_dyn; subst.
  + apply T_AsLocalFrom; try assumption.
    eapply IHtfrom; eassumption.
  + eapply transmittable_value_typing; eassumption.
  + inversion H_stat.
    subst.
    eapply T_AsLocalFrom.
    * assumption.
    * eapply IHtarg; try eassumption.
    * assumption.
    * assumption.
    
    
- (* asLocalIn *)
  intros theta' theta varEnv t' T P H_stat H_dyn.
  inversion H_stat.
  subst.
  inversion H_dyn; subst.
  + eapply T_Comp; try eassumption.
    eapply IHtassign; try eassumption.
  + eapply T_AsLocal.
    * assumption.
    * eapply substitution_t; try eassumption.
      eapply transmittable_value_typing; eassumption.
    * assumption.
    * auto.
  
  
- (* asLocalInFrom *)
Admitted.





(*
(* stronger formulation *)
Lemma preservation_nonReactive: forall t t' T peerInsts typing ties reactEnv placeEnv varEnv P reactSys,
    typing; ties; Psi; Delta; Gamma; P |- t \in T -> 
    LeContext ties typing peerInsts P reactSys |> t L==> Right _ _ t' ->
    exists T',
    typing; ties; Psi; Delta; Gamma; P |- t' \in T'.
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
*)
