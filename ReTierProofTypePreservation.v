Require Import ReTierSyntax.
Require Import ReTierStaticSemantics.
Require Import ReTierDynamicSemantics.
Require Import ReTierProofContext.
Require Import ReTierProofSubstitution.
Require Import ReTierProofReactiveSystem.
Require Import ReTierProofTransmission.
Require Import ReTierProofAggregation.
Require Import ReTierProofPeerTies.




(*
Lemma substitution_t_relaxed:
  forall program Psi Delta Gamma P x t T v U,
  program :: Psi; Delta; idUpdate x U Gamma; P |- t : T ->
  program :: Psi; Delta; Gamma; P |- v : U ->
  program :: Psi; Delta; Gamma; P |- [x :=_t v] t : T.
Admitted.
*)



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


Theorem preservation_t: forall t t' T theta theta' program Psi P rho rho',
  program :: Psi; emptyPlaceEnv; emptyVarEnv; P |- t : T ->
  program :: Psi; emptyPlaceEnv; emptyVarEnv |- rho ->
  List.incl theta (peer_instances_of_type program P) ->
  program :: theta : P |> t; rho == theta' ==> t'; rho' ->
  exists Psi',
    Psi' extends Psi /\
    program :: Psi'; emptyPlaceEnv; emptyVarEnv; P |- t' : T /\
    program :: Psi'; emptyPlaceEnv; emptyVarEnv |- rho'.
Proof.
intros until rho'.
intros H_typing H_reactive_typing H_instances H_eval.
remember emptyPlaceEnv as Delta.
remember emptyVarEnv as Gamma.
generalize dependent theta.
generalize dependent t'.
induction H_typing; intros; subst.
- (* idApp *)
  inversion H_eval.
  
- (* app *)
  inversion H_eval; subst.
  + apply IHH_typing1 in H8; try assumption || reflexivity.
    destruct H8 as [ Psi' ].
    destruct H, H0.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_App; try eassumption.
    eapply reactive_typing_weakening_t; eassumption.
  + apply IHH_typing2 in H9; try assumption || reflexivity.
    destruct H9 as [ Psi' ].
    destruct H, H0.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_App; try eassumption.
    eapply reactive_typing_weakening_t; eassumption.
  + inversion H_typing1.
    subst.
    exists Psi.
    split.
    * apply reactive_typing_extends_refl.
    * split; try assumption.
      eapply substitution_t; eassumption.
      
- (* lambda *)
  inversion H_eval.
  
- (* cons *)
  inversion H_eval; subst.
  + apply IHH_typing1 in H8; try assumption || reflexivity.
    destruct H8 as [ Psi' ].
    destruct H, H0.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_Cons; try eassumption.
    eapply reactive_typing_weakening_t; eassumption.
  + apply IHH_typing2 in H9; try assumption || reflexivity.
    destruct H9 as [ Psi' ].
    destruct H, H0.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_Cons; try eassumption.
    eapply reactive_typing_weakening_t; eassumption.
    
- (* nil *)
  inversion H_eval.
  
- (* some *)
  inversion H_eval; subst.
  edestruct IHH_typing as (Psi' & (H_ext & H_typing_t' & H_typing_rho')); eauto.  
  eexists; split; eauto; split.
  + apply T_Some. assumption.
  + assumption.
  
- (* none *)
  inversion H_eval.
  
- (* unit *)
  inversion H_eval.
  
- (* peerApp *)
  inversion H_eval.
  
- (* asLocal *)
  inversion H_eval; subst.
  + exists Psi; split.
    * apply reactive_typing_extends_refl.
    * { split.
        - eapply aggregation; eauto. apply List.incl_refl.
        - assumption.
      }
  + edestruct IHH_typing as (Psi' & H_extends & H_typing_t' & H_typing_rho');
      eauto. 
    * apply List.incl_refl.
    * eexists; split; try split; eauto.
      apply T_AsLocal; auto.
  
- (* asLocalFrom *)
  inversion H_eval; subst.
  + edestruct IHH_typing2 as (Psi' & H_extends & H_typing_t1' & H_typing_rho');
      clear IHH_typing2; eauto.
    eexists; split; try split; eauto.
    apply T_AsLocalFrom; auto.
    eapply reactive_typing_weakening_t; eauto.
  + exists Psi; split; try split.
    * apply reactive_typing_extends_refl.
    * inversion H_typing2; subst.
      apply zeta_type_invariance; auto.
    * assumption.
  + edestruct IHH_typing1 as (Psi' & H_extends & H_typing_t'0 & H_typing_rho');
      clear IHH_typing1; eauto.
    * inversion H_typing2; subst. assumption.
    * eexists; split; try split; eauto.
      apply T_AsLocalFrom; auto.
      eapply reactive_typing_weakening_t; eauto.
  
- (* asLocalIn *)
  inversion H_eval; subst.
  + edestruct IHH_typing1 as [Psi' (H_extends & H_typing_t0' & H_typing_rho')]; 
      eauto.
    eexists; split; try split; eauto.
    apply T_Comp; auto.
    eapply reactive_typing_weakening_t; eauto.
  + exists Psi; split.
    * apply reactive_typing_extends_refl.
    * split; try assumption.
      apply T_AsLocal; auto.
      eapply substitution_t; try eassumption.
      apply zeta_type_invariance; auto.
      apply mutualTiesSymmetric.
      assumption.
       
  
- (* asLocalInFrom *)
  inversion H_eval; subst.
  + edestruct IHH_typing3 as [Psi' (H_ext & H_typing_t2' & H_typing_rho')]; eauto.
    eexists; repeat split; eauto.
    * apply T_ComFrom; auto; eapply reactive_typing_weakening_t; eauto.
    * inversion H_typing_rho'.
      assumption.
    * inversion H_typing_rho'.
      assumption.
  + edestruct IHH_typing1 as [Psi' (H_ext & H_typing_t' & H_typing_rho')]; eauto.
    eexists; repeat split; eauto.
    * apply T_ComFrom; auto;
        eapply context_invariance_t; eauto;
          eapply reactive_typing_weakening_t; eauto.
    * inversion H_typing_rho'; assumption.
    * inversion H_typing_rho'; assumption.
  + exists Psi; repeat split.
    * apply reactive_typing_extends_refl.
    * apply T_AsLocalFrom; auto.
      eapply substitution_t; eauto.
      apply zeta_type_invariance; auto.
      apply mutualTiesSymmetric; assumption.
    * inversion H_reactive_typing; assumption.
    * inversion H_reactive_typing; assumption.
      
  
  
- (* reactApp *)
  inversion H_eval.   (* TODO: Which rule allows formation of H_eval?
                       * Does this case ever occurr?
                       *)
  
- (* signal *)
  inversion H_eval.
  subst.
  pose proof reactive_typing_add.
  specialize H with program Psi emptyPlaceEnv emptyVarEnv rho P t T (Signal T).
  apply H in H_reactive_typing as H0; try assumption || (right; reflexivity).
  destruct H0 as [ Psi' ], H0 as [ rho0 ], H0 as [ r' ].
  destruct H0, H1, H2, H4.
  rewrite H3 in H1.
  inversion H1.
  subst.
  exists Psi'.
  do 2 (split; try assumption).
  eapply T_Reactive; try eassumption.
  left. reflexivity.
  
- (* var *)
  inversion H_eval; subst.
  + apply IHH_typing in H3; try assumption || reflexivity.
    destruct H3 as [ Psi' ].
    destruct H, H0.
    exists Psi'.
    do 2 (split; try assumption).
    apply T_ReactiveVar.
    assumption.
  + pose proof reactive_typing_add.
    specialize H with program Psi emptyPlaceEnv emptyVarEnv rho P t T (Var T).
    apply H in H_reactive_typing as H1; try assumption || (left; reflexivity).
    destruct H1 as [ Psi' ], H1 as [ rho0 ], H1 as [ r' ].
    destruct H1, H2, H3, H5.
    rewrite H4 in H2.
    inversion H2.
    subst.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_Reactive; try eassumption.
    right. reflexivity.

- (* now *)
  inversion H_eval as [| | | | | | | | | |
                        tmp0 tmp1 tmp2 tmp3 tmp4 t'' tmp6 tmp7 H_eval_t
                        | | | | | | | | | | | | | ]; subst.
  + edestruct IHH_typing as [Psi' (H_ext & H_typing_t'0 & H_typing_rho')]; eauto.
    eexists; split; repeat split; eauto.
    * eapply T_Now; eassumption.
    * inversion H_typing_rho'; assumption.
    * inversion H_typing_rho'; assumption.
  + exists Psi; repeat split.
    * apply reactive_typing_extends_refl.
    * inversion H_reactive_typing as [H_eq_domain H_fa].
      { specialize (H_fa r) as (t_lr & T_lr & T' & P_lr & H_lookup_tlr &
                                H_lookup_Tlr & H_structure_Tlr & H_typing_tlr).
        - apply reactive_system_lookup_domain.
          congruence.
        - rewrite H_lookup_tlr in H0.   (* TODO: rename H0 *)
          inversion H0; subst.
          
          (* TODO: simplify rest ... we construct a lot of duplicate hypothesis *)
          inversion H_typing; subst.
          (* inversion H_reactive_typing as [H_eq_rho']. *)
          inversion H_reactive_typing as
            [H_eq_rho'_Psi (t & T0' & T1' & P'
                            & H_lookup_t & H_lookup_T0'_P' & H_T0 & H_ex)].
          + apply reactive_system_lookup_domain with (r := r).
            congruence.
          + rewrite H_lookup_tlr in H_lookup_t.
            inversion H_lookup_t as [H_eq_t'_t].
            clear H_lookup_t.
            rewrite H_lookup_Tlr in H_lookup_T0'_P'.
            inversion H_lookup_T0'_P' as [(H_eq_Tlr_T0' & H_eq_Plr_P')].
            clear H_lookup_T0'_P'.
            rewrite H2 in H_lookup_Tlr.
            inversion H_lookup_Tlr as [(H_eq_T0_Tlr & H_eq_P_Plr)].
            clear H_lookup_Tlr.
            subst.
            (* TODO: assign a fixed name to H during construction *)
            destruct H_T0; destruct H; congruence.
      }
    * inversion H_reactive_typing.
      assumption.
    * inversion H_reactive_typing.
      assumption.
  
- inversion H_eval; subst.
  + apply IHH_typing1 in H8; try assumption || reflexivity.
    destruct H8 as [ Psi' ].
    destruct H, H0.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_Set; try eassumption.
    eapply reactive_typing_weakening_t; eassumption.
  + apply IHH_typing2 in H9; try assumption || reflexivity.
    destruct H9 as [ Psi' ].
    destruct H, H0.
    exists Psi'.
    do 2 (split; try assumption).
    eapply T_Set; try eassumption.
    eapply reactive_typing_weakening_t; eassumption.
  + inversion H_typing1.
    subst.
    pose proof reactive_typing_update.
    specialize H with program Psi emptyPlaceEnv emptyVarEnv rho r P t2 T.
    apply H in H_reactive_typing as H1; try assumption.
    exists Psi.
    split.
    * apply reactive_typing_extends_refl.
    * split; try assumption.
      apply T_Unit.
- inversion H_eval.
Qed.


Lemma preservation_nonReactive: forall t t' T theta theta' program Psi Delta Gamma P rho rho',
  program :: Psi; Delta; Gamma; P |- t : T ->
  program :: theta : P |> t; rho == theta' ==> t'; rho' ->
  List.incl theta (peer_instances_of_type program P) ->
  program :: Psi; Delta; Gamma; P |- t' : T.
Proof.
intros t t' T theta theta' program Psi Delta Gamma P rho rho'.
intros H_stat H_dyn H_inst.
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
                  | x T tassign IHtassign tin IHtin S (* asLocalIn     : id -> T -> t -> t -> S -> t *)
                  | targ T tassign IHtassign tin IHtin S tfrom IHtfrom (* asLocalInFrom : id -> T -> t -> t -> S -> t -> t *)
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
  intros theta' theta varEnv t' T P H_stat H_dyn H_inst.
  inversion H_dyn.
- (* app *)
  intros theta' theta varEnv t' T P H_stat H_dyn H_inst.
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
  intros theta' theta varEnv t' T P H_stat H_dyn H_inst.
  inversion H_dyn.
- (* unit *)
  intros theta' theta varEnv t' T P H_stat H_dyn H_inst.
  inversion H_dyn.
- (* none *)
  intros theta' theta varEnv t' T P H_stat H_dyn H_inst.
  inversion H_dyn.
- (* some *)
  intros theta' theta varEnv t' T P H_stat H_dyn H_inst.
  inversion H_dyn.
(*  assumption.
*)
admit.
- (* nil *)
  intros theta' theta varEnv t' T P H_stat H_dyn H_inst.
  inversion H_dyn.
- (* cons *)
  intros theta' theta varEnv t' T P H_stat H_dyn H_inst.
  inversion H_stat.
  inversion H_dyn; subst.
  + apply T_Cons; try assumption.
    eapply IHtc; eassumption.
  + apply T_Cons; try assumption.
    eapply IHtl; eassumption.


- (* asLocal *)
  intros theta' theta varEnv t' T P H_stat H_dyn H_inst.
  inversion H_stat.
  subst.

  inversion H_dyn; subst.
  + eapply aggregation; try eassumption.
    apply List.incl_refl.
  + eapply T_AsLocal.
    * assumption.
    * eapply IHtarg; try eassumption.
      apply List.incl_refl.
    * assumption.
    * assumption.


- (* asLocalFrom *)
  intros theta' theta varEnv t' T P H_stat H_dyn H_inst.
  inversion H_stat.
  subst.
  inversion H_dyn; subst.
  + apply T_AsLocalFrom; try assumption.
    eapply IHtfrom; eassumption.
  + inversion H11.
    eapply transmission; eassumption.
  + inversion H_stat.
    subst.
    eapply T_AsLocalFrom.
    * assumption.
    * inversion H11.
      eapply IHtarg; eassumption.
    * assumption.
    * assumption.
    
    
- (* asLocalIn *)
  intros theta' theta varEnv t' T1 P H_stat H_dyn H_inst.
  inversion H_stat.
  subst.
  inversion H_dyn; subst.
  + eapply T_Comp; try eassumption.
    eapply IHtassign; try eassumption.
  + eapply T_AsLocal; try assumption.
    eapply substitution_t; try eassumption.
    eapply transmission; try eassumption.
    unfold peers_tied in H14.
    destruct H14.
    unfold peers_tied.
    split; assumption.
  
  
- (* asLocalInFrom *)
  intros theta' theta Gamma tin' T0 P H_stat H_dyn H_inst.
  inversion H_stat. subst.
  inversion H_dyn. subst.
  + apply T_ComFrom; auto.  (* TODO: fix spelling mistake *)
    eapply IHtfrom; eauto.
  + apply T_ComFrom; auto; subst.
    eapply IHtassign; eauto.
  + subst.
    apply T_AsLocalFrom; auto.
    eapply substitution_t.
    * eassumption.
    * eapply transmission; eauto.
      apply mutualTiesSymmetric. assumption.
      
      
- (* signal *) 
  intros theta' theta Gamma ts' T P H_stat H_dyn H_inst.
  inversion H_stat; subst. inversion H_dyn; subst.
  (*inversion H_react; subst.*)
  eapply T_Reactive.
  + admit.
    (* TODO: fix rules for static semantics *)
    (* Goal not true with current rules. 
    
       H_dyn:   program :: theta' : P |> signal ts; rho == theta' ==> reactApp r; rho'
       goal:    reactive_type r Psi = Some (Signal T0 on P)
       
       r is new reactive index 
       => r not contained in Psi
       => contradiction with goal
     *)
  + left. reflexivity.


- (* var *)
  (* TODO: fix rules for static semantics *)
  (* Same problem as in signal case above => Goal not true with current rules. *)
  admit.


- (* now *)
  admit.  (* see tmpTypePreservation-v2.v a proof.
              (alternative lemma with stronger hypothesis.
           *)


- (* set *)
  intros theta' theta Gamma t' T P H_stat H_dyn H_inst.
  inversion H_stat; subst.
  inversion H_dyn; subst.
  + eapply T_Set; eauto.
  + eapply T_Set; eauto.
  + apply T_Unit.


- (* peerApp *)
  intros theta' theta Gamma t' T P H_stat H_dyn H_inst.
  inversion H_dyn.


- (* reactApp *)
  intros theta' theta Gamma t' T P H_stat H_dyn H_inst.
  inversion H_dyn.


- (* tnat *)
  intros theta' theta Gamma t' T P H_stat H_dyn H_inst.
  inversion H_dyn.

(*Qed.*)
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
