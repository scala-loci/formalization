Require Import ReTierSyntax.
Require Import ReTierStaticSemantics.
Require Import ReTierDynamicSemantics.
Require Import ReTierProofReactiveSystem.


(* Definition 1 from the informal specification *)
Definition config_complete program :=
  forall P0 P1,
  ((peer_ties program) (P0, P1) = Single ->
   length (peer_instances_of_type program P1) = 1) /\
  ((peer_ties program) (P0, P1) = Optional ->
   length (peer_instances_of_type program P1) <= 1).


Lemma some_phi: forall program t T P0 P1,
  config_complete program ->
  peers_tied program P0 P1 ->
  exists t', Phi (peer_ties program) P0 P1 (peer_instances_of_type program P1) t T = Some t'.
Proof.
intros until P1.
intros H_complete H_tied.
destruct program as [ ties peers ].
unfold peers_tied in H_tied.
destruct H_tied as [ H_P0_tied H_P1_tied ].
simpl in H_P0_tied.
clear H_P1_tied.
unfold config_complete, peer_ties in H_complete.
destruct (ties (P0, P1)) eqn: H_tie.
- clear H_complete.
  induction (peer_instances_of_type (Program ties peers) P1) as [| p peers' IH_peers ].
  + simpl.
    rewrite H_tie.
    esplit.
    reflexivity.
  + simpl.
    rewrite H_tie.
    destruct IH_peers.
    simpl in H.
    rewrite H.
    esplit.
    reflexivity.
- apply H_complete in H_tie as H_peers_length.
  destruct (peer_instances_of_type (Program ties peers) P1) as [| p peers' ].
  + simpl.
    rewrite H_tie.
    esplit.
    reflexivity.
  + destruct peers'.
    * simpl.
      rewrite H_tie.
      esplit.
      reflexivity.
    * simpl in H_peers_length.
      apply le_S_n in H_peers_length.
      inversion H_peers_length.
- apply H_complete in H_tie as H_peers_length.
  destruct (peer_instances_of_type (Program ties peers) P1) as [| p peers' ].
  + inversion H_peers_length.
  + destruct peers'.
    * simpl.
      rewrite H_tie.
      esplit.
      reflexivity.
    * simpl in H_peers_length.
      congruence.
- congruence.
Qed.


Theorem progress_t: forall t T theta program Psi P rho,
  config_complete program ->
  program :: Psi; emptyPlaceEnv; emptyVarEnv; P |- t : T ->
  program :: Psi; emptyPlaceEnv; emptyVarEnv |- rho ->
  value t \/ exists t' theta' rho', program :: theta : P |> t; rho == theta' ==> t'; rho'.
Proof.
intros until rho.
intros H_complete H_typing H_reactive_typing.
remember emptyPlaceEnv as Delta.
remember emptyVarEnv as Gamma.
generalize dependent theta.
induction H_typing; intros; subst.
- (* idApp *)
  right.
  inversion H as [H_contradiction | (_ & H_contradiction)];
    inversion H_contradiction.
  
- (* app *)
  right. eapply IHH_typing1 in H_complete as IHH_typing1'; auto. clear IHH_typing1.
  destruct IHH_typing1' as [H_value_t1 | H_eval_t1].
  + eapply IHH_typing2 in H_complete as IHH_typing2'; auto. clear IHH_typing2.
    destruct IHH_typing2' as [H_value_t2 | H_eval_t2].
    * { destruct H_value_t1; inversion H_typing1; subst.
        - repeat eexists. apply E_App. assumption.
        - destruct H6 as [H_typing_r_signal | H_typing_r_var].
          + inversion H_typing_r_signal.
          + inversion H_typing_r_var.
      }
    * destruct H_eval_t2 as (t' & theta' & rho' & H_eval_t2).
      repeat eexists; eapply EC_App_Right; eauto.
  + destruct H_eval_t1 as (t' & theta' & rho' & H_eval_t1).
    repeat eexists; eapply EC_App_Left; eassumption.
  
- (* lambda *)
    left. apply v_lambda.
- (* cons *)
  eapply IHH_typing1 in H_complete as IHH_typing1'; eauto. clear IHH_typing1.
  destruct IHH_typing1' as [H_value_t0 | H_eval_t0].
  + eapply IHH_typing2 in H_complete as IHH_typing2'; eauto. clear IHH_typing2.
    destruct IHH_typing2' as [H_value_t1 | H_eval_t1].
    * left. apply v_cons; assumption.
    * right. destruct H_eval_t1 as (t' & theta' & rho' & H_eval_t1).
      repeat eexists; apply EC_Cons_Right; eauto.
  + destruct H_eval_t0 as (t' & theta' & rho' & H_eval_t0).
    right; repeat eexists; apply EC_Cons_Left; eassumption.
  
- (* nil *)
  left. apply v_nil.
- (* some *)
  eapply IHH_typing in H_complete as IHH_typing'; auto. clear IHH_typing.
  destruct IHH_typing' as [H_value_t | (t' & theta' & rho' & H_eval_t)]. 
  + left; apply v_some; assumption.
  + right; repeat eexists; eapply EC_Some; eassumption.
  
- (* none *)
   left. apply v_none.
   
- (* unit *)
  left. apply v_unit.
  
- (* peerApp *)
  left. apply v_peerApp.
  
- (* asLocal *)
  edestruct IHH_typing; try assumption || reflexivity.
  + pose proof some_phi.
    eapply H3 in H0; try assumption.
    destruct H0 as [ t' ].
    right. repeat esplit.
    eapply E_AsLocal; eassumption.
  + destruct H2 as [ t' ], H2 as [ theta' ], H2 as [ rho' ].
    right. repeat esplit.
    apply E_Remote. eassumption.
    
- (* asLocalFrom *)
  right.
  eapply IHH_typing2 in H_complete as IHH_typing2'; auto; clear IHH_typing2.
  destruct IHH_typing2' as [H_value_t1 | H_eval_t1].
  + inversion H_value_t1; subst; inversion H_typing2; subst.
    * { eapply IHH_typing1 in H_complete as [H_value_t0 | H_eval_t0]; auto.
        - repeat eexists; apply E_AsLocalFrom; auto.
        - destruct H_eval_t0 as (t' & theta' & rho' & H_eval_t0). 
          repeat eexists; apply E_RemoteFrom; eauto.
      }
    * destruct H8 as [H_contradiction | H_contradiction];
        inversion H_contradiction.
  + destruct H_eval_t1 as (t' & theta' & rho' & H_eval_t1).
    repeat eexists; apply EC_AsLocalFrom; eauto.
  
- (* asLocalIn *)
  right.
  eapply IHH_typing1 in H_complete as IHH_typing1'; auto; clear IHH_typing1.
  destruct IHH_typing1' as [H_value_t0 | (t' & theta' & rho' & H_eval_t0)].
  + repeat eexists; apply E_Comp; auto.
  + repeat eexists; apply EC_Comp; eauto.
  
- (* asLocalInFrom *)
  right.
  assert (H_complete' := H_complete).
  eapply IHH_typing3 in H_complete as [H_value_t2 | (t2' & theta' & rho' & H_eval_t2)];
    auto. clear IHH_typing3.
  + inversion H_value_t2; subst; inversion H_typing3; subst.
    * { eapply IHH_typing1 in H_complete' as [H_value_t0 | (t0' & theta' & rho' & H_eval_t1)];
          auto.
        - repeat eexists; apply E_CompFrom; auto.
        - repeat eexists; apply EC_CompFrom_Left; eauto.
      }
    * destruct H9 as [H_contradiction | H_contradiction]; inversion H_contradiction.
  + repeat eexists; apply EC_CompFrom_Right; eauto. 
  
- (* reactApp *)
  left. apply v_reactApp.
  
- (* signal *)
  right.
  repeat eexists; apply E_Signal; reflexivity.
  
- (* var *)
  right.
  eapply IHH_typing in H_complete as [H_value_t | (t' & theta' & rho' & H_eval_t)];
    auto.
  + repeat eexists; apply E_ReactiveVar; try assumption || reflexivity.
  + repeat eexists; apply EC_Var; eauto.
  
- (* now *)
  right.
  eapply IHH_typing in H_complete as [H_value_t | (t' & theta' & rho' & H_eval_t)];
    auto; clear IHH_typing.
  + destruct H; subst; inversion H_value_t; subst; inversion H_typing; subst.
    * { inversion H_reactive_typing.
        edestruct H1 as (t & T0 & T' & P' & H_lookup & H_rest).
        - rewrite H. apply reactive_env_type_domain.
          rewrite H0. discriminate.
        - repeat eexists. apply E_Now. eapply H_lookup. 
      }
    * { (* TODO: remove duplicate *)
        inversion H_reactive_typing.
        edestruct H1 as (t & T0 & T' & P' & H_lookup & H_rest).
        - rewrite H. apply reactive_env_type_domain.
          rewrite H0. discriminate.
        - repeat eexists. apply E_Now. eapply H_lookup. 
      }
  + repeat eexists; apply EC_Now; eauto.  
  
- (* set *)
  right.
  edestruct IHH_typing1 as [H_value_t1 | (t1' & theta1' & rho1' & H_eval_t1)]; auto.
  + edestruct IHH_typing2 as [H_value_t2 | (t2' & theta2' & rho2' & H_eval_t2)];
      auto.
    * inversion H_value_t1; subst; inversion H_typing1; subst.
      repeat eexists; apply E_Set; auto.
    * repeat eexists; apply EC_Set_Right; eauto. 
  + repeat eexists; apply EC_Set_Left; eauto.
  
- (* tnat *)
  left. apply v_tnat.
Qed.


Lemma progress: forall program Psi Delta Gamma P theta rho t T,
  program :: Psi; Delta; Gamma; P |- t : T ->
  (value t \/ exists t' theta' rho', program :: theta : P |> t; rho == theta' ==> t'; rho').
Proof.
  intros program Psi Delta Gamma P theta rho t T H_typing.
  generalize dependent T.
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
                  | x Tx tassign IHtassign tin IHtin S (* asLocalIn     : id -> T -> t -> t -> S -> t *)
                  | targ Targ tassign IHtassign tin IHtin S tfrom IHtfrom (* asLocalInFrom : id -> T -> t -> t -> S -> t -> t *)
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
    left. apply v_lambda.
  
  
  - (* app *)
    intros T H_type_app.
    right.
    inversion H_type_app as   [| tmp0 tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 tmp7
                              Targ H_type_fct H_type_arg
                              tmp11 tmp12 tmp13 tmp14 tmp15 tmp16 tmp17
                              | | | | | | | | | | | | | | | | | ];
      subst.
    apply IHarg in H_type_arg as H_eval_arg. clear IHarg.
    assert (A_eval_fct:
              (exists (t' : t) (theta' : peer_instances) (rho' : reactive_system),
                  program :: theta : P |> fct; rho == theta' ==> t'; rho') ->
              (exists (t' : t) (theta' : peer_instances) (rho' : reactive_system),
                  program :: theta : P |> app fct arg; rho == theta' ==> t'; rho')).
    { intros H_eval_fct.
      inversion H_eval_fct as [fct' H_eval_fct']; clear H_eval_fct.
      inversion H_eval_fct' as [theta' H_eval_fct'']; clear H_eval_fct'.
      inversion H_eval_fct'' as [rho' H_eval_fct]; clear H_eval_fct''.
      repeat eexists. apply EC_App_Left. eassumption.
    }
    destruct H_eval_arg as [H_value_arg | H_eval_arg].
    

                  
    + apply IHfct in H_type_fct as H_eval_fct. clear IHfct.
      destruct H_eval_fct as [H_value_fct | H_eval_fct].
      * { 
          inversion H_value_fct; subst;
            inversion H_type_fct as [| | | | | | | | | | | | |
                                      tmp0 tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 tmp7 tmp8
                                      H_false
                                     | | | | | ];
              subst.
          - repeat eexists.
            apply E_App. assumption.
          - destruct H_false as [H_false | H_false]; inversion H_false.
        }
      * apply A_eval_fct; assumption.
    + apply IHfct in H_type_fct as [H_value_fct | H_eval_fct].
      * inversion H_eval_arg as [arg' H_eval_arg']; clear H_eval_arg.
        inversion H_eval_arg' as [theta' H_eval_arg'']; clear H_eval_arg'.
        inversion H_eval_arg'' as [rho' H_eval_arg]; clear H_eval_arg''.
        repeat eexists. apply EC_App_Right; eassumption.
      * apply A_eval_fct; assumption.
  
  
  - (* idApp *)
    admit.
  
  - (* unit *)
    intros T H. left. apply v_unit.
    
  - (* none *)
    intros T H. left. apply v_none.
    
  - (* some *)
    intros T H_type_some.
    inversion H_type_some as  [| | | | |
                                tmp0 tmp1 tmp2 tmp3 tmp4 tmp5
                                Ts H_type_ts
                               | | | | | | | | | | | | | ];
      subst.
    apply IHts in H_type_ts as [H_value_ts |H_eval_ts].
    + left. apply v_some. assumption.
    + right.
      inversion H_eval_ts as [ts' H_eval_ts']; clear H_eval_ts.
      inversion H_eval_ts' as [theta' H_eval_ts'']; clear H_eval_ts'.
      inversion H_eval_ts'' as [rho' H_eval_ts]; clear H_eval_ts''.
      repeat eexists.
      eapply EC_Some.
      eassumption.
    
    
  - (* nil *)
    intros T H. left. apply v_nil.
  - (* cons *)
    intros T H_type_cons.
    inversion H_type_cons as  [| | |
                                tmp0 tmp1 tmp2 tmp3 tmp4 tmp5 tmp6
                                Tc H_type_tc H_type_tl
                               | | | | | | | | | | | | | | | ];
      subst.
    apply IHtc in H_type_tc as [H_value_tc | H_eval_tc].
    + apply IHtl in H_type_tl as [H_value_tl | H_eval_tl].
      * left. apply v_cons; assumption.
      * right.
        inversion H_eval_tl as [tl' H_eval_tl']; clear H_eval_tl.
        inversion H_eval_tl' as [theta' H_eval_tl'']; clear H_eval_tl'.
        inversion H_eval_tl'' as [rho' H_eval_tl]; clear H_eval_tl''.
        repeat eexists; eapply EC_Cons_Right; eassumption.
    + right.
      inversion H_eval_tc as [tc' H_eval_tc']; clear H_eval_tc.
      inversion H_eval_tc' as [theta' H_eval_tc'']; clear H_eval_tc'.
      inversion H_eval_tc'' as [rho' H_eval_tc]; clear H_eval_tc''.    
      repeat eexists; eapply EC_Cons_Left; eassumption.
    
    
  - (* asLocal *)
    admit.
    
  - (* asLocalFrom *)
    admit.

  - (* asLocalIn *)
    admit.

  - (* asLocalInFrom *)
    admit.
    
    
  - (* signal *)
    intros T H; right.
    repeat eexists; apply E_Signal. reflexivity.
    
    
  - (* var *)
    intros T H_type_var; right. (*; repeat eexists.*)
    inversion H_type_var as [| | | | | | | | | | | | | | |
                              tmp0 tmp1 tmp2 tmp3 tmp4 tmp5
                              Tv H_type_tv
                             | | | ];
      subst.
    apply IHtv in H_type_tv as [H_value_tv | H_eval_tv].
    + repeat eexists; apply E_ReactiveVar.
      * assumption.
      * reflexivity.
    + inversion H_eval_tv as [tv' H_eval_tv']; clear H_eval_tv.
      inversion H_eval_tv' as [theta' H_eval_tv'']; clear H_eval_tv'.
      inversion H_eval_tv'' as [rho' H_eval_tv]; clear H_eval_tv''.
      repeat eexists; apply EC_Var.
      eassumption.
    
  
  - (* now *)
    admit.

  - (* set *)
    intros T H_type_set; right.
    inversion H_type_set as [| | | | | | | | | | | | | | | | |
                              tmp0 tmp1 tmp2 tmp3 tmp4 tmp5 tmp6
                              Tsource H_type_ttarget H_type_tsource
                             | ];
      subst.
    assert (H_type_ttarget': program :: Psi; Delta; Gamma; P |- ttarget : Var Tsource).
    { assumption. }     (* necessary to avoid losing H_type_ttarget
                           TODO: is there a better way? *)
    apply IHttarget in H_type_ttarget' as [H_value_ttarget | H_eval_ttarget];
      clear IHttarget.
    + assert (H_type_tsource': program :: Psi; Delta; Gamma; P |- tsource : Tsource).
      { assumption. }   (* necessary to avoid losing H_type_tsource
                           TODO: is there a better way? *)
      apply IHtsource in H_type_tsource' as [H_value_tsource | H_eval_tsource];
      clear IHtsource.
      * inversion H_type_ttarget as [| | | | | | | | | | | | |
                                      tmp0 tmp1 tmp2 tmp3 tmp4 
                                      r tmp6
                                      Tsource' H_type_r_Tsource  tmp9
                                    | | | | | ];
          subst; inversion H_value_ttarget; subst.
        repeat eexists; apply E_Set; auto.
      * inversion H_eval_tsource as [tsource' H_eval_tsource']; clear H_eval_tsource.
        inversion H_eval_tsource' as [theta' H_eval_tsource'']; clear H_eval_tsource'.
        inversion H_eval_tsource'' as [rho' H_eval_tsource]; clear H_eval_tsource''.
        repeat eexists; apply EC_Set_Right; eauto.
    + inversion H_eval_ttarget as [ttarget' H_eval_ttarget']; clear H_eval_ttarget.
      inversion H_eval_ttarget' as [theta' H_eval_ttarget'']; clear H_eval_ttarget'.
      inversion H_eval_ttarget'' as [rho' H_eval_ttarget]; clear H_eval_ttarget''.
      repeat eexists; apply EC_Set_Left; eauto.
        


  - (* peerApp *)
    intros T H. left. apply v_peerApp.


  - (* reactApp *)
    intros T H. left. apply v_reactApp.


  - (* tnat *)
    intros T H. left. apply v_tnat.
Admitted.

        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        