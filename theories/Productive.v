Require Import
        Coq.Arith.Arith
        Coq.micromega.Psatz
        Coq.Sets.Ensembles
        Coq.Logic.Classical
        Coq.Program.Tactics.

Require Import
        Common
        Maps
        FunImp
        HoareCommon
        Fixpoints.

Section existential_Execution.

  (* Formalizing existential executions.
   *)

  Structure funExSpec : Type :=
    { (* Number of traces involved in the relational specifications *)
      k : nat;
      (* Relational precondition on k initial states *)
      preEx : Vector.t (list nat) (S k) -> Prop;
      (* Relational postcondition on k initial states and k return values *)
      postEx : Vector.t (list nat) (S k) -> Vector.t nat (S k) -> Prop }.

  Class ExEnv : Type :=
    { AllEnv :> Env;
      funExSpecs : total_map funExSpec }.

  Local Arguments Singleton [_] _.

  Inductive ceval_Ex (Sigma : ExEnv) : com -> state -> Ensemble state -> Prop :=
    | ceval_Ex_Skip : forall st,
        ceval_Ex Sigma SKIP st (Singleton st)
    | ceval_Havoc_Ass  : forall st x a,
        ceval_Ex Sigma (CHavoc x) st (Singleton (x !-> a ; st))
    | ceval_Ex_Ass  : forall st x a,
        ceval_Ex Sigma (x ::= a) st (Singleton (x !-> (aeval st a) ; st))
    | ceval_Ex_Seq : forall c1 c2 st Q Q',
        ceval_Ex Sigma c1 st Q ->
        (forall st', Q st' -> ceval_Ex Sigma c2 st' Q') ->
         ceval_Ex Sigma (c1 ;; c2) st Q'
    | ceval_Ex_IfTrue : forall st Q b c1 c2,
        beval st b = true ->
        ceval_Ex Sigma c1 st Q ->
        ceval_Ex Sigma (TEST b THEN c1 ELSE c2 FI) st Q
    | ceval_Ex_IfFalse : forall st b c1 c2 Q,
        beval st b = false ->
        ceval_Ex Sigma c2 st Q ->
        ceval_Ex Sigma (TEST b THEN c1 ELSE c2 FI) st Q
    | ceval_Ex_WhileFalse : forall b st c,
        beval st b = false ->
        ceval_Ex Sigma (WHILE b DO c END) st (Singleton st)
    | ceval_Ex_WhileTrue : forall st b c Q Q',
        beval st b = true ->
        ceval_Ex Sigma c st Q ->
        (forall st', Q st' ->
                     ceval_Ex Sigma (WHILE b DO c END) st' Q') ->
        ceval_Ex Sigma (WHILE b DO c END) st Q'
    | ceval_Ex_CallDef :
        forall st Q args x f fd,
          funDefs f = Some fd ->
          ceval_Ex Sigma (funBody fd) (build_total_map (funArgs fd) (aseval st args) 0) Q
          -> ceval_Ex Sigma (x :::= f $ args) st
                        (fun st' => exists st'', Q st'' /\ st' = (x !-> aeval st'' (funRet fd); st))
    | ceval_Ex_CallSpec : forall st args x f i inits returns,
        funDefs f = None ->
        (funExSpecs f).(preEx) inits ->
        (funExSpecs f).(postEx) inits returns ->
        Vector.nth inits i = aseval st args ->
        (*(funSpecs f).(pre) (aseval st args) ->
        (f unSpecs f).(post) (Vector.nth returns i) (aseval st args) -> *)
        ceval_Ex Sigma (x :::= f $ args) st
                   (fun st' => exists inits returns, (funExSpecs f).(postEx) inits returns
                                                     /\ (funExSpecs f).(preEx) inits
                                                     /\ Vector.nth inits i = aseval st args
                               /\ st' = (x !-> Vector.nth returns i; st))
  | ceval_Ex_Weaken : forall st c Q Q',
        ceval_Ex Sigma c st Q ->
        Included state Q Q' ->
        ceval_Ex Sigma c st Q'.

  (* Existential executions is a *stronger* property than evaluation-- it forces
     a command to evaluate to a final state regardless of how
     nondeterministic choices are made. *)
  Theorem productive_sufficient (Sigma : ExEnv)
    (Complete_Env : forall f, exists fd,  @funDefs (@AllEnv Sigma) f = Some fd) :
    forall (c : com) (st : state) (Q : Ensemble state),
      ceval_Ex Sigma c st Q ->
      exists st' (exe : (AllEnv) |- st =[c]=> st'), Q st'.
  Proof.
    induction 1.
    - assert (AllEnv |- st =[ SKIP ]=> st) by econstructor.
      eexists _, H; econstructor.
    - assert (AllEnv |- st =[ CHavoc x ]=> _) by econstructor.
      eexists _, H; econstructor.
    - eassert (AllEnv |- st =[ x ::= a ]=> _) by (econstructor; eauto).
      eexists _, H; econstructor.
    - destruct IHceval_Ex as [st' [exe Q_st'] ].
      specialize (H0 _ Q_st'); destruct (H1 _ Q_st') as [st'' [exe' Q'_st']].
      assert (AllEnv |- st =[ c1;; c2 ]=> st'') by (econstructor; eauto).
      eauto.
    - destruct IHceval_Ex as [st' [exe Q_st'] ].
      assert (AllEnv |- st =[ TEST b THEN c1 ELSE c2 FI ]=> st') by (econstructor; eauto).
      eexists _, H1 ; eauto.
    - destruct IHceval_Ex as [st' [exe Q_st'] ].
      assert (AllEnv |- st =[ TEST b THEN c1 ELSE c2 FI ]=> st') by (econstructor; eauto).
      eexists _, H1; eauto.
    - assert (AllEnv |- st =[ WHILE b DO c END ]=> st) by (econstructor; eauto).
      eexists _, H0; eauto; econstructor.
    - destruct IHceval_Ex as [st' [exe Q_st'] ].
      specialize (H1 _ Q_st'); destruct (H2 _ Q_st') as [st'' [exe' Q'_st']].
      assert (AllEnv |- st =[ WHILE b DO c END ]=> st'') by (econstructor; eauto).
      eauto.
    - destruct IHceval_Ex as [st' [exe Q_st'] ].
      eassert (AllEnv |- st =[ x :::= f $ args ]=> _) by (eapply (@E_CallDef AllEnv); eauto).
      eexists _, H1; eauto.
    - destruct (Complete_Env f) as [fd' H3]; rewrite H3 in H; discriminate.
    - destruct IHceval_Ex as [st' [exe Q_st'] ]; eexists _, exe; eauto.
      eapply H0; apply Q_st'.
  Qed.


  (* An existential environment is consistent if all of its existential specifications
     imply their universal counterparts.  *)
  Definition Consistent_Env (Sigma : ExEnv) : Prop :=
    forall f,
      (forall inits i, (funExSpecs f).(preEx) inits -> (funSpecs f).(pre) (Vector.nth inits i))
      /\ (forall inits returns i,
             (funExSpecs f).(postEx) inits returns ->
             (funSpecs f).(post) (Vector.nth returns i) (Vector.nth inits i)).

  Section Relationalceval_Ex.

  Variables m : nat.
  Definition Estate := Vector.t state m.
  Definition Eprogs := Vector.t com m.

  Inductive Relceval_Ex
            (Sigma : ExEnv)
    : Estate -> Eprogs -> Ensemble Estate -> Prop :=
  | RelP_Finish : forall Est Ec,
      (forall i, Vector.nth Ec i = CSkip)
      -> Relceval_Ex Sigma Est Ec (Singleton Est)

    | RelP_SkipIntro : forall Est Q Ec Ec' i,
      (forall i', i <> i' -> Vector.nth Ec i' = Vector.nth Ec' i') ->
      Vector.nth Ec' i = CSeq (Vector.nth Ec i) CSkip ->
      Relceval_Ex Sigma Est Ec' Q ->
      Relceval_Ex Sigma Est Ec Q

  | RelP_Step :
      forall Est Q (R : Ensemble state) Ec Ec' i c1 c2,
        (forall i', i <> i' -> Vector.nth Ec i' = Vector.nth Ec' i') ->
        Vector.nth Ec i = CSeq c1 c2 ->
        Vector.nth Ec' i = c2 ->
        ceval_Ex Sigma c1 (Vector.nth Est i) R ->
        (forall st,
            R st ->
            Relceval_Ex Sigma (Vector.replace Est i st) Ec' Q) ->
        Relceval_Ex Sigma Est Ec Q

  | RelP_Weaken :
      forall Est Ec Q Q',
        Relceval_Ex Sigma Est Ec Q ->
        Included _ Q Q' ->
        Relceval_Ex Sigma Est Ec Q'.

  Hint Resolve bassn_eval_true bassn_eval_false : hoare.
  Hint Constructors ceval.

  Theorem Relceval_Ex_sufficient (Sigma : ExEnv)
          (Complete_Env : forall f, exists fd,  @funDefs (@AllEnv Sigma) f = Some fd)
  : forall (Est : Estate)
           (Ec : Eprogs)
           (Q : Ensemble Estate),
      Relceval_Ex Sigma Est Ec Q ->
      exists Est'
             (exe : forall i, AllEnv |- (Vector.nth Est i) =[Vector.nth Ec i]=> (Vector.nth Est' i)),
        Q Est'.
  Proof.
    induction 1.
    - exists Est.
      assert (forall i, AllEnv |- (Vector.nth Est i) =[Vector.nth Ec i]=> (Vector.nth Est i))
        as exe
          by (intros; rewrite H; eauto).
      eexists exe; econstructor.
    - destruct IHRelceval_Ex as [Est' [exe QEst] ].
      assert (forall (i' : Fin.t m), AllEnv |- Vector.nth Est i' =[ Vector.nth Ec i' ]=> Vector.nth Est' i')
        as exe'.
      { intros; destruct (Fin.eq_dec i i'); subst.
        + specialize (exe i'); rewrite H0 in exe.
          inversion exe; subst.
          inversion H7; subst; eauto.
        + rewrite H; eauto.
      }
      eauto.
    - eapply productive_sufficient in H2; eauto; destruct H2 as [st' [exe' R_st'] ].
      destruct (H4 _ R_st') as [Est' [exes' Q_exes'] ].
      eexists Est'.
      assert (forall (i' : Fin.t m), AllEnv |- Vector.nth Est i' =[ Vector.nth Ec i' ]=> Vector.nth Est' i'); eauto.
      { intros; destruct (Fin.eq_dec i i'); subst.
        + rewrite H0.
          econstructor; eauto.
          specialize (exes' i'); rewrite vector_nth_replace in exes'; eauto.
        + rewrite H; eauto.
          specialize (exes' i'); rewrite vector_nth_replace' in exes'; eauto.
      }
    - destruct IHRelceval_Ex as [Est' [exes' Q_exes'] ].
      eexists Est', exes'.
      eapply H0; eauto.
  Qed.

  End Relationalceval_Ex.

  (* A productive function definition is one that produces at least
     one behavior allowed by its specifiction. *)
  Definition productive_funDef (Sigma : ExEnv)
             (fs : funExSpec)
             (fd : funDef) : Prop :=
    forall inits,
      fs.(preEx) inits ->
      Relceval_Ex _ Sigma (Vector.map (fun args => build_total_map (fd.(funArgs)) args 0) inits)
                    (Vector.const fd.(funBody) _)
                    (fun finals => fs.(postEx) inits (Vector.map (fun st => aeval st fd.(funRet)) finals)).

  (* An environment is productive if all of its function definitions are
     productive with respect to their specs.  *)
  Definition ex_compatible_env (Sigma : ExEnv) : Prop :=
    forall f fd,
      funDefs f = Some fd ->
      productive_funDef Sigma (funExSpecs f) fd.

  Lemma productive_empty
    : forall Sigs Sigma ESigma,
      ex_compatible_env {| AllEnv := {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |};
                        funExSpecs := ESigma |} .
  Proof.
    unfold ex_compatible_env; simpl; intros; discriminate.
  Qed.

  Lemma Relceval_Ex_ceval_Ex
    : forall
      (k : nat)
      (Sigma : ExEnv)
      (Complete_Env : forall f, exists fd,  @funDefs (@AllEnv Sigma) f = Some fd)
      (Q : Ensemble (Estate k))
      (inits : Vector.t state k)
      (c : Vector.t com k),
      Relceval_Ex k Sigma inits c Q ->
      forall i,
      ceval_Ex Sigma (Vector.nth c i) (Vector.nth inits i)
                 (fun st => exists finals, Q finals /\ st = Vector.nth finals i).
  Proof.
    intros; induction H.
    - rewrite H; econstructor.
      + econstructor.
      + unfold Included, Ensembles.In; intros.
        inversion H0; subst.
        eexists; split; eauto.
        constructor.
    - destruct (Fin.eq_dec i i0); subst.
      + rewrite H0 in IHRelceval_Ex.
        revert IHRelceval_Ex; clear.
        generalize
          (Vector.nth Est i0)
          (fun st : state => exists finals : Estate k0, Q finals /\ st = Vector.nth finals i0).
        remember (CSeq (Vector.nth Ec i0) SKIP).
        intros s P H; revert Heqc; induction H; intros; try discriminate.
        * injection Heqc; intros; subst.
          econstructor; eauto.
          unfold Included, Ensembles.In; intros.
          eapply H0 in H2; revert H2; clear; intro; remember CSkip; induction H2; try discriminate.
          econstructor.
          eapply H. eapply IHceval_Ex; eauto.
        * econstructor; eauto.
      + rewrite H; eauto.
    - destruct (Fin.eq_dec i i0); subst.
      + rewrite H0.
        econstructor; intros.
        eauto; intros.
        eapply H4 in H1.
        rewrite vector_nth_replace in H1; eauto.
      + rewrite H; eauto.
        eapply productive_sufficient in H2; eauto; destruct H2 as [? [? ?] ].
        erewrite <- (vector_nth_replace' _ _ Est); eauto.
    - econstructor; eauto.
      unfold Included, Ensembles.In; intros.
      destruct H1 as [? [? ?] ].
      eexists; split; eauto.
      eapply H0; eauto.
  Qed.

  (* Key refinement theorem Theorem: executing a program in a
     compatible environment must result in a final state included in
     an existential execution. *)
  Theorem productive_strong (Sigma : ExEnv)
          (Complete_Env : forall f, exists fd,  @funDefs (@AllEnv Sigma) f = Some fd) :
    forall (c : com) (st : state) (Q : Ensemble state),
      ex_compatible_env Sigma ->
      ceval_Ex {| AllEnv := {|
                               funSigs := funSigs;
                               funSpecs := funSpecs;
                               funDefs := empty |};
                    funExSpecs := funExSpecs |}
                 c st Q ->
      ceval_Ex Sigma c st Q.
  Proof.
    induction 2; intros; try (solve [econstructor; eauto]).
    - simpl in *; rewrite apply_empty in H0; discriminate.
    - destruct (@funDefs (@AllEnv Sigma) f) eqn: ?.
      + pose proof (H _ _ Heqo inits H1).
        destruct f0.
        eapply ceval_Ex_Weaken.
        * econstructor; eauto.
          eapply Relceval_Ex_ceval_Ex with (i := i) in H4.
          rewrite Vector.const_nth in H4; simpl in *.
          erewrite VectorSpec.nth_map, H3 in H4; try reflexivity.
          apply H4.
          eauto.
        * unfold Included, Ensembles.In; intros.
          destruct H5 as [st'' [ [? ?] ?] ]; intuition; simpl in *.
          eexists _, _.
          repeat split.
          -- apply H7.
          -- try eassumption.
          -- subst; eauto.
          -- subst.
             erewrite Vector.nth_map; try reflexivity.
      + eapply (@ceval_Ex_CallSpec Sigma); eauto.
  Qed.

  Theorem Relceval_Ex_strong (Sigma : ExEnv)
          (Complete_Env : forall f, exists fd,  @funDefs (@AllEnv Sigma) f = Some fd)
          (m : nat)
      : forall (Est : Estate m)
               (Ec : Eprogs m)
               (Q : Ensemble (Estate m)),
      ex_compatible_env Sigma ->
      Relceval_Ex m {| AllEnv := {|
                                  funSigs := funSigs;
                                  funSpecs := funSpecs;
                                  funDefs := empty |};
                       funExSpecs := funExSpecs |} Est Ec Q ->
      Relceval_Ex m Sigma Est Ec Q.
  Proof.
    induction 2; intros; try (solve [econstructor; eauto]).
    eapply RelP_Step; eauto using productive_strong.
  Qed.

  Theorem productive_refine (Sigma : ExEnv)
          (Complete_Env : forall f, exists fd,  @funDefs (@AllEnv Sigma) f = Some fd) :
    forall (c : com) (st : state) (Q : Ensemble state),
      ex_compatible_env Sigma ->
      ceval_Ex {| AllEnv := {|
                               funSigs := funSigs;
                               funSpecs := funSpecs;
                               funDefs := empty |};
                    funExSpecs := funExSpecs |}
                 c st Q ->
      exists st' (exe : (AllEnv) |- st =[c]=> st'), Q st'.
  Proof.
    intros.
    eapply productive_sufficient; eauto.
    eapply productive_strong; eauto.
  Qed.


  Local Hint Constructors ceval.
  Local Hint Constructors AppearsIn.

  Lemma productive_Weaken :
    forall Sigma c st Q f fd,
      ~ AppearsIn f c
      -> (forall (f' : String.string) (fd' : funDef),
             funDefs f' = Some fd' -> ~ AppearsIn f (funBody fd'))
      -> ceval_Ex Sigma c st Q
      -> ceval_Ex {| AllEnv := {| funSigs := funSigs;
                                    funSpecs := funSpecs;
                                    funDefs := f |-> fd; funDefs |};
                       funExSpecs := funExSpecs |} c st Q.
  Proof.
    induction 3; simpl; try solve [econstructor; eauto].
    - econstructor; eauto.
      simpl; unfold update, t_update; find_if_inside; eauto.
      destruct H; subst; eauto.
    - econstructor; eauto.
      eapply ceval_Ex_CallSpec; eauto.
      + simpl; unfold update, t_update; find_if_inside; eauto.
        destruct H; subst; eauto.
      + unfold Included, In; eauto.
  Qed.

End existential_Execution.
