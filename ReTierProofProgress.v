Require Import ReTierSyntax.
Require Import ReTierDynamicSemantics.
Require Import ReTierStaticSemantics.


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
    admit.
    
  - (* var *)
    admit.

  - (* now *)
    admit.

  - (* set *)
    admit.


  - (* peerApp *)
    intros T H. left. apply v_peerApp.


  - (* reactApp *)
    intros T H. left. apply v_reactApp.


  - (* tnat *)
    intros T H. left. apply v_tnat.
Admitted.

        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        