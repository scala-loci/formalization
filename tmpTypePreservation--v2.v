Require Import ReTierSyntax.
Require Import ReTierStaticSemantics.
Require Import ReTierDynamicSemantics.
Require Import ReTierProofContext.
Require Import ReTierProofSubstitution.
Require Import ReTierProofReactiveSystem.
Require Import ReTierProofTransmission.
Require Import ReTierProofAggregation.
Require Import ReTierProofPeerTies.




Lemma reactApp_typing_impl_type_lookup_weak: forall program Psi Delta Gamma P r T,
                    program :: Psi; Delta; Gamma; P |- reactApp r : T ->
                    reactive_type r Psi = Some (T on P).
Proof.
  intros program Psi Delta Gamma P r T H_typing.
  inversion H_typing; subst.
  assumption.
Qed.
  
                    




Lemma preservation_reactive_system_well_typed: forall t t' T theta theta' program Psi Delta Gamma P rho rho',
  program :: Psi; Delta; Gamma; P |- t : T ->
  program :: theta : P |> t; rho == theta' ==> t'; rho' ->
  List.incl theta (peer_instances_of_type program P) ->
  program :: Psi ; Delta ; Gamma |- rho ->    (* additional hypothesis *)
  program :: Psi; Delta; Gamma; P |- t' : T.
Proof.
intros t t' T theta theta' program Psi Delta Gamma P rho rho'.
intros H_stat H_dyn H_inst H_react.
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

(* following admitted cases have already been proven in the original formulation
   of this lemma with a weeker hypothesis (see ReTierProofTypePreservation.v)
*)
- (* lambda *)
  admit.
- (* app *)
  admit.
- (* idApp *)
  admit.
- (* unit *)
  admit.
- (* none *)
  admit.
- (* some *)
  admit.
- (* nil *)
  admit.
- (* cons *)
  admit.
- (* asLocal *)
  admit.
- (* asLocalFrom *)
  admit.
- (* asLocalIn *)
  admit.
- (* asLocalInFrom *)
  admit.
      
(* ===================================================================== *)

(* The Following admitted cases cannot be proven with the current static
   semantics rules. See explanation below ReTierProofTypePreservation.v
   The stronger hypothesis does not solve this problem.
*)
  
- (* signal *) 
  admit.
- (* var *)
  admit.

  
(* ======================================================= *)

(* We were not able to prove the following case in the lemma's original
   formulation with a week hypothesis (see ReTierProofTypePreservation.v).
*)

- (* now *)
  intros theta' theta Gamma H_react tn' T P H_stat H_dyn H_inst.
  (* TODO: assign fixed names to hypotheses e.g. H6. *)
  
  inversion H_stat; subst.
  + destruct H6; subst.
    * { inversion H_dyn; subst.
        - assumption.
        - inversion H_react as [H_dom H_store].
          specialize (H_store r).
          assert (Hlt_r_dom: reactive_index r < reactive_domain rho').
          {
            apply reactive_system_lookup_domain.
            destruct reactive_system_lookup.
            - discriminate.
            - discriminate.
          }
          apply H_store in Hlt_r_dom. rename Hlt_r_dom into H_store'. clear H_store.
          destruct H_store' as [tn'r H_store].
          destruct H_store as [Tr H_store].
          destruct H_store as [Tn'r H_store].
          destruct H_store as [Pr H_store].
          destruct H_store as [H_lookup_r_tn'r H_store].
          destruct H_store as [H_type_r_TrOnPr H_store].
          destruct H_store as [H_pattern_Tr H_type_tn'r_Tn'r].
          rewrite H4 in H_lookup_r_tn'r.
          inversion H_lookup_r_tn'r as [H_eq_tn'_tn'r]. clear H_lookup_r_tn'r.
          symmetry in H_eq_tn'_tn'r; subst.
          apply reactApp_typing_impl_type_lookup_weak in H0 as H_type_r.
          rewrite H_type_r in H_type_r_TrOnPr. inversion H_type_r_TrOnPr. 
          clear H_type_r_TrOnPr H_type_r.
          subst.
          destruct H_pattern_Tr as [H_eq_sig_var | H_eq_sigT_sigTn'r].
          * inversion H_eq_sig_var.
          * inversion H_eq_sigT_sigTn'r as [H_eq_T_Tn'r].
            symmetry in H_eq_T_Tn'r. subst.
            assumption.
      }
    * (* the following code until ( *** ) is COPY & PASTE of previous case ( * )
         TODO: remove copied & pasted code
      *)
      { inversion H_dyn; subst.
        - assumption.
        - inversion H_react as [H_dom H_store].
          specialize (H_store r).
          assert (Hlt_r_dom: reactive_index r < reactive_domain rho').
          {
            apply reactive_system_lookup_domain.
            destruct reactive_system_lookup.
            - discriminate.
            - discriminate.
          }
          apply H_store in Hlt_r_dom. rename Hlt_r_dom into H_store'. clear H_store.
          destruct H_store' as [tn'r H_store].
          destruct H_store as [Tr H_store].
          destruct H_store as [Tn'r H_store].
          destruct H_store as [Pr H_store].
          destruct H_store as [H_lookup_r_tn'r H_store].
          destruct H_store as [H_type_r_TrOnPr H_store].
          destruct H_store as [H_pattern_Tr H_type_tn'r_Tn'r].
          rewrite H4 in H_lookup_r_tn'r.
          inversion H_lookup_r_tn'r as [H_eq_tn'_tn'r]. clear H_lookup_r_tn'r.
          symmetry in H_eq_tn'_tn'r; subst.
          apply reactApp_typing_impl_type_lookup_weak in H0 as H_type_r.
          rewrite H_type_r in H_type_r_TrOnPr. inversion H_type_r_TrOnPr. 
          clear H_type_r_TrOnPr H_type_r.
          subst.
      (*
        *** 
        COPY & PASTE until heare
        TODO: remove copied & pasted code
      *)
          destruct H_pattern_Tr as [H_eq_varT_varTn'r | H_eq_var_sig].
        (* cases like above in switched order *)
          * inversion H_eq_varT_varTn'r as [H_eq_T_Tn'r].
            symmetry in H_eq_T_Tn'r. subst.
            assumption.
          * inversion H_eq_var_sig.
      }
      
(* ===================================================================== *)

(* following admitted cases have already been proven in the original formulation
   of this lemma with a weeker hypothesis (see ReTierProofTypePreservation.v)
*)

- (* set *)
  admit.
- (* peerApp *)
  admit.
- (* reactApp *)
  admit.
- (* tnat *)
  admit.

Qed.