Require Import
        Coq.Arith.Arith
        Coq.micromega.Psatz
        Coq.Sets.Ensembles
        Coq.Logic.Classical
        Coq.Program.Tactics.

Require Import Maps Imp HoareCommon.

Section productive_Execution.

  (* Formalizing when it is productive to use function definitions.
     Productive here means that the function definition doesn't rule
     out some behavior allowed by the spec, i.e. the composite program
     still "produces" that behavior.

     Note: I (Ben) am not in love with this terminology, anyone who reads
     this should feel free to suggest another. Living? NotDead? UnDead?
     *)

  Structure funExSpec : Type :=
  { preEx : list nat -> list nat -> Prop;
    postEx : nat -> list nat -> list nat -> Prop }.

  Class ExEnv : Type :=
    { AllEnv :> Env;
      funExSpecs : total_map funExSpec }.

  (* A productive initial state is one that ensures the program
  *always* produces the specified final state *)

  Local Arguments Singleton [_] _.

  Inductive Productive (Sigma : ExEnv) : com -> state -> Ensemble state -> Prop :=
    | Productive_Skip : forall st,
        Productive Sigma SKIP st (Singleton st)
    | Productive_Ass  : forall st x a,
        Productive Sigma (x ::= a) st (Singleton (x !-> (aeval st a) ; st))
    | Productive_Seq : forall c1 c2 st Q Q',
        Productive Sigma c1 st Q ->
        (forall st', Q st' -> Productive Sigma c2 st' Q') ->
         Productive Sigma (c1 ;; c2) st Q'
    | Productive_IfTrue : forall st Q b c1 c2,
        beval st b = true ->
        Productive Sigma c1 st Q ->
        Productive Sigma (TEST b THEN c1 ELSE c2 FI) st Q
    | Productive_IfFalse : forall st b c1 c2 Q,
        beval st b = false ->
        Productive Sigma c2 st Q ->
        Productive Sigma (TEST b THEN c1 ELSE c2 FI) st Q
    | Productive_WhileFalse : forall b st c,
        beval st b = false ->
        Productive Sigma (WHILE b DO c END) st (Singleton st)
    | Productive_WhileTrue : forall st b c Q Q',
        beval st b = true ->
        Productive Sigma c st Q ->
        (forall st', Q st' ->
                     Productive Sigma (WHILE b DO c END) st' Q') ->
        Productive Sigma (WHILE b DO c END) st Q'
    | Productive_CallDef :
        forall st Q args x f fd,
          funDefs f = Some fd ->
          Productive Sigma (funBody fd) (build_total_map (funArgs fd) (aseval st args) 0) Q
          -> Productive Sigma (x :::= f $ args) st
                        (fun st' => exists st'', Q st'' /\ st' = (x !-> aeval st'' (funRet fd); st))
    | Productive_CallSpec : forall st args x f n params,
        funDefs f = None ->
        (funExSpecs f).(preEx) params (aseval st args) ->
        (funExSpecs f).(postEx) n params (aseval st args) ->
        (funSpecs f).(pre) (aseval st args) ->
        (funSpecs f).(post) n (aseval st args) ->
        Productive Sigma (x :::= f $ args) st
                   (fun st' => exists n, (funExSpecs f).(postEx) n params (aseval st args)
                                         /\ st' = (x !-> n; st))
  | Productive_Weaken : forall st c Q Q',
        Productive Sigma c st Q ->
        Included state Q Q' ->
        Productive Sigma c st Q'.

  (*Inductive ProductiveBnd (Sigma : ExEnv) : nat -> com -> state -> Ensemble state -> Prop :=
    | ProductiveBnd_Skip : forall n st,
        ProductiveBnd Sigma n SKIP st (Singleton st)
    | ProductiveBnd_Ass  : forall n st x a,
        ProductiveBnd Sigma n (x ::= a) st (Singleton (x !-> (aeval st a) ; st))
    | ProductiveBnd_Seq : forall n c1 c2 st Q Q',
        ProductiveBnd Sigma n c1 st Q ->
        (forall st', Q st' -> ProductiveBnd Sigma n c2 st' Q') ->
         ProductiveBnd Sigma n (c1 ;; c2) st Q'
    | ProductiveBnd_IfTrue : forall n st Q b c1 c2,
        beval st b = true ->
        ProductiveBnd Sigma n c1 st Q ->
        ProductiveBnd Sigma n (TEST b THEN c1 ELSE c2 FI) st Q
    | ProductiveBnd_IfFalse : forall n st b c1 c2 Q,
        beval st b = false ->
        ProductiveBnd Sigma n c2 st Q ->
        ProductiveBnd Sigma n (TEST b THEN c1 ELSE c2 FI) st Q
    | ProductiveBnd_WhileFalse : forall n b st c,
        beval st b = false ->
        ProductiveBnd Sigma n (WHILE b DO c END) st (Singleton st)
    | ProductiveBnd_WhileTrue : forall n st b c Q Q',
        beval st b = true ->
        ProductiveBnd Sigma n c st Q ->
        (forall st', Q st' ->
                     ProductiveBnd Sigma n (WHILE b DO c END) st' Q') ->
        ProductiveBnd Sigma (S n) (WHILE b DO c END) st Q'
    | ProductiveBnd_CallDef :
        forall n st Q args x f fd,
          funDefs f = Some fd ->
          ProductiveBnd Sigma n (funBody fd) (build_total_map (funArgs fd) (aseval st args) 0) Q
          -> ProductiveBnd Sigma n (x :::= f $ args) st
                        (fun st' => exists st'', Q st'' /\ st' = (x !-> aeval st'' (funRet fd); st))
    | ProductiveBnd_CallSpec : forall m st args x f n params,
        funDefs f = None ->
        (funExSpecs f).(preEx) params (aseval st args) ->
        (funExSpecs f).(postEx) n params (aseval st args) ->
        (funSpecs f).(pre) (aseval st args) ->
        (funSpecs f).(post) n (aseval st args) ->
        ProductiveBnd Sigma m (x :::= f $ args) st
                   (fun st' => exists n, (funExSpecs f).(postEx) n params (aseval st args)
                                         /\ st' = (x !-> n; st))
  | ProductiveBnd_Weaken : forall n st c Q Q',
        ProductiveBnd Sigma n c st Q ->
        Included state Q Q' ->
        ProductiveBnd Sigma n c st Q'.

  Require Import Coq.Logic.ChoiceFacts.

  Lemma ProductiveBnd_Eqv (Sigma : ExEnv) :
    forall (c : com)
           (st : state)
           (Q : Assertion),
      Productive Sigma c st Q ->
      exists n, ProductiveBnd Sigma n c st Q.
  Proof.
    induction 1; intros; try solve [eexists _; econstructor; eauto].
    - destruct IHProductive.
      eapply GuardedFunctionalChoice_on in H0. *)

  (* Productivity is a *stronger* property than evaluation-- it forces
     a command to evaluate to a final state regardless of how
     nondeterministic choices are made. *)
  Theorem productive_com_produces (Sigma : ExEnv) :
    forall (c : com) (st : state) (Q : Ensemble state),
      Productive Sigma c st Q ->
      exists st' (exe : (AllEnv) |- st =[c]=> st'), Q st'.
  Proof.
    induction 1.
    - assert (AllEnv |- st =[ SKIP ]=> st) by econstructor.
      eexists _, H; econstructor.
    - eassert (AllEnv |- st =[ x ::= a ]=> _) by (econstructor; eauto).
      eexists _, H; econstructor.
    - destruct IHProductive as [st' [exe Q_st'] ].
      specialize (H0 _ Q_st'); destruct (H1 _ Q_st') as [st'' [exe' Q'_st']].
      assert (AllEnv |- st =[ c1;; c2 ]=> st'') by (econstructor; eauto).
      eauto.
    - destruct IHProductive as [st' [exe Q_st'] ].
      assert (AllEnv |- st =[ TEST b THEN c1 ELSE c2 FI ]=> st') by (econstructor; eauto).
      eexists _, H1 ; eauto.
    - destruct IHProductive as [st' [exe Q_st'] ].
      assert (AllEnv |- st =[ TEST b THEN c1 ELSE c2 FI ]=> st') by (econstructor; eauto).
      eexists _, H1; eauto.
    - assert (AllEnv |- st =[ WHILE b DO c END ]=> st) by (econstructor; eauto).
      eexists _, H0; eauto; econstructor.
    - destruct IHProductive as [st' [exe Q_st'] ].
      specialize (H1 _ Q_st'); destruct (H2 _ Q_st') as [st'' [exe' Q'_st']].
      assert (AllEnv |- st =[ WHILE b DO c END ]=> st'') by (econstructor; eauto).
      eauto.
    - destruct IHProductive as [st' [exe Q_st'] ].
      eassert (AllEnv |- st =[ x :::= f $ args ]=> _) by (eapply (@E_CallDef AllEnv); eauto).
      eexists _, H1; eauto.
    - eassert (AllEnv |- st =[ x :::= f $ args ]=> _) by (eapply (@E_CallSpec AllEnv); eauto).
      eexists _, H4; eauto.
    - destruct IHProductive as [st' [exe Q_st'] ]; eexists _, exe; eauto.
      eapply H0; apply Q_st'.
  Qed.

  Inductive MustEval (Sigma : ExEnv) : state -> com -> state -> Prop :=
    | MustEval_Skip : forall st,
        MustEval Sigma st SKIP st
    | MustEval_Ass  : forall st x a,
        MustEval Sigma st (x ::= a) (x !-> (aeval st a) ; st)
    | MustEval_Seq : forall c1 c2 st st' st'',
        MustEval Sigma st c1 st' ->
        MustEval Sigma st' c2 st'' ->
         MustEval Sigma st (c1 ;; c2)  st''
    | MustEval_IfTrue : forall st st' b c1 c2,
        beval st b = true ->
        MustEval Sigma st c1 st' ->
        MustEval Sigma st (TEST b THEN c1 ELSE c2 FI) st'
    | MustEval_IfFalse : forall st b c1 c2 st',
        beval st b = false ->
        MustEval Sigma st c2 st' ->
        MustEval Sigma st (TEST b THEN c1 ELSE c2 FI) st'
    | MustEval_WhileFalse : forall b st c,
        beval st b = false ->
        MustEval Sigma st (WHILE b DO c END) st
    | MustEval_WhileTrue : forall st b c st' st'',
        beval st b = true ->
        MustEval Sigma st c st' ->
        MustEval Sigma st' (WHILE b DO c END) st'' ->
        MustEval Sigma st (WHILE b DO c END) st''
    | MustEval_CallDef :
        forall st args x f fd st',
          funDefs f = Some fd ->
          MustEval Sigma (build_total_map (funArgs fd) (aseval st args) 0) (funBody fd) st'
          -> MustEval Sigma st (x :::= f $ args)
                     (x !-> aeval st' (funRet fd) ; st)
    | MustEval_CallSpec : forall st args x f n params,
        funDefs f = None ->
        (funExSpecs f).(preEx) params (aseval st args) ->
        (funExSpecs f).(postEx) n params (aseval st args) ->
        MustEval Sigma st (x :::= f $ args) (x !-> n; st).

  (* An existential environment is consistent if all of its existential specifications
     imply their universal counterparts.  *)
  Definition Consistent_Env (Sigma : ExEnv) : Prop :=
    forall f,
      (forall (params args : list nat), preEx (funExSpecs f) params args -> pre (funSpecs f) args)
      /\ (forall (ret : nat) (params args : list nat),
             postEx (funExSpecs f) ret params args -> post (funSpecs f) ret args).

  (* MustEval is also a stronger property than Eval *)
  Theorem MustEval_com_MustEval
          (Sigma : ExEnv)
          (SigmaOK : Consistent_Env Sigma)
    : forall (c : com) (st st' : state),
      MustEval Sigma st c st' ->
      AllEnv |- st =[c]=> st'.
  Proof.
    induction 1; try solve [econstructor; eauto].
    eapply E_CallSpec; eauto.
    eapply SigmaOK; eauto.
    eapply SigmaOK; eauto.
  Qed.

  Theorem productive_com_MustEval (Sigma : ExEnv) :
    forall (c : com) (st : state) (Q : Ensemble state),
      Productive Sigma c st Q ->
      exists st' (exe : MustEval Sigma st c st'), Q st'.
  Proof.
    induction 1.
    - assert (MustEval Sigma st SKIP st) by econstructor.
      eexists _, H; econstructor.
    - eassert (MustEval Sigma st (x ::= a) _) by (econstructor; eauto).
      eexists _, H; econstructor.
    - destruct IHProductive as [st' [exe Q_st'] ].
      specialize (H0 _ Q_st'); destruct (H1 _ Q_st') as [st'' [exe' Q'_st']].
      assert (MustEval Sigma st (c1;; c2) st'') by (econstructor; eauto).
      eauto.
    - destruct IHProductive as [st' [exe Q_st'] ].
      assert (MustEval Sigma st (TEST b THEN c1 ELSE c2 FI) st') by (econstructor; eauto).
      eexists _, H1 ; eauto.
    - destruct IHProductive as [st' [exe Q_st'] ].
      assert (MustEval Sigma st (TEST b THEN c1 ELSE c2 FI) st') by (econstructor; eauto).
      eexists _, H1; eauto.
    - assert (MustEval Sigma st (WHILE b DO c END) st) by (econstructor; eauto).
      eexists _, H0; eauto; econstructor.
    - destruct IHProductive as [st' [exe Q_st'] ].
      specialize (H1 _ Q_st'); destruct (H2 _ Q_st') as [st'' [exe' Q'_st']].
      assert (MustEval Sigma st (WHILE b DO c END) st'') by (econstructor; eauto).
      eauto.
    - destruct IHProductive as [st' [exe Q_st'] ].
      eassert (MustEval Sigma st (x :::= f $ args) _) by (eapply (@MustEval_CallDef Sigma); eauto).
      eexists _, H1; eauto.
    - eassert (MustEval Sigma st (x :::= f $ args) _) by (eapply (@MustEval_CallSpec Sigma); eauto).
      eexists _, H4; eauto.
    - destruct IHProductive as [st' [exe Q_st'] ]; eexists _, exe; eauto.
      eapply H0; apply Q_st'.
  Qed.

  (* A productive function definition is one that produces at least
     one behavior allowed by its specifiction. *)
  Definition productive_funDef (Sigma : ExEnv)
             (fs : funExSpec)
             (fd : funDef) : Prop :=
    forall (params args : list nat),
      (preEx fs) params args ->
      exists Q (exe : Productive Sigma (funBody fd) (build_total_map (funArgs fd) args 0) Q),
        forall st', Q st' -> (postEx fs) (aeval st' (funRet fd)) params args.

  (* An environment is productive if all of its function definitions are
     productive with respect to their specs.  *)
  Definition productive_Env (Sigma : ExEnv) : Prop :=
    forall f fd,
      funDefs f = Some fd ->
      productive_funDef Sigma (funExSpecs f) fd.



  Lemma productive_empty
    : forall Sigs Sigma ESigma,
      productive_Env {| AllEnv := {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |};
                        funExSpecs := ESigma |} .
  Proof.
    unfold productive_Env; simpl; intros; discriminate.
  Qed.

  (* Key Productivity Theorem: executing a program in a productive
     environment and productive initial state will produce some value that a
     'pure' specification environment (i.e. one without any function
     definitions) would have. *)
  Theorem productive_Env_produces (Sigma : ExEnv) :
    forall (c : com) (st : state) (Q : Ensemble state),
      productive_Env Sigma ->
      Productive {| AllEnv := {|
                               funSigs := funSigs;
                               funSpecs := funSpecs;
                               funDefs := empty |};
                    funExSpecs := funExSpecs |}
                 c st Q ->
      Productive Sigma c st Q.
  Proof.
    induction 2; intros; try (solve [econstructor; eauto]).
    - simpl in *; rewrite apply_empty in H0; discriminate.
    - destruct (@funDefs (@AllEnv Sigma) f) eqn: ?.
      + destruct (H _ _ Heqo _ _ H1) as [Q [exe Q_exe] ].
        eapply Productive_Weaken.
        econstructor; eauto.
        unfold Included, In; intros.
        destruct H5 as [? [? ?] ].
        eexists (aeval x1 (funRet f0)); split; eauto.
      + eapply (@Productive_CallSpec Sigma); eauto.
  Qed.

  Local Hint Constructors ceval.
  Local Hint Constructors AppearsIn.
  Lemma productive_Weaken :
    forall Sigma c st Q f fd,
      ~ AppearsIn f c
      -> (forall (f' : String.string) (fd' : funDef),
             funDefs f' = Some fd' -> ~ AppearsIn f (funBody fd'))
      -> Productive Sigma c st Q
      -> Productive {| AllEnv := {| funSigs := funSigs;
                                    funSpecs := funSpecs;
                                    funDefs := f |-> fd; funDefs |};
                       funExSpecs := funExSpecs |} c st Q.
  Proof.
    induction 3; simpl; try solve [econstructor; eauto].
    - econstructor; eauto.
      simpl; unfold update, t_update; find_if_inside; eauto.
      destruct H; subst; eauto.
    - econstructor; eauto.
      eapply Productive_CallSpec; eauto.
      + simpl; unfold update, t_update; find_if_inside; eauto.
        destruct H; subst; eauto.
      + unfold Included, In; eauto.
  Qed.

  Lemma productive_Env_Extend
    : forall (Sigma : ExEnv)
             (f : funName)
             (fd : funDef),
      productive_Env Sigma ->
      funDefs f = None ->
      (forall f' fd', funDefs f' = Some fd' ->
                      ~ AppearsIn f (funBody fd'))
      -> ~ AppearsIn f (funBody fd)
      -> productive_funDef Sigma (funExSpecs f) fd
      -> productive_Env {| AllEnv := {| funSigs := funSigs;
                                        funSpecs := funSpecs;
                                        funDefs := f |-> fd; funDefs |};
                           funExSpecs := funExSpecs
                           |}.
  Proof.
    unfold productive_Env; simpl; intros.
    unfold update, t_update in H4; find_if_inside; subst.
    - injections.
      unfold productive_funDef in *; intros.
      eapply H3 in H4; destruct H4 as [Q [? ?] ].
      eexists Q, (productive_Weaken _ _ _ _ _ _ H2 H1 x); eauto.
    - pose proof (H _ _ H4).
      unfold productive_funDef; intros.
      eapply H5 in H6.
      destruct H6 as [Q [? ?] ].
      eexists Q, (productive_Weaken _ _ _ _ _ _ (H1 _ _ H4) H1 x); eauto.
  Qed.

End productive_Execution.

Section EHoare.

  Reserved Notation "Sigma |- {[ P ]}  c  {[ Q ]}#"
           (at level 40, c at next level).

  Inductive ehoare_proof (Sigma : total_map funExSpec)
    : Assertion -> com -> Assertion -> Prop :=
  | EH_Skip : forall P,
      Sigma |- {[P]} SKIP {[P]}#
  | EH_Asgn : forall Q V a,
      Sigma |- {[Q[V |-> a]]} V ::= a {[Q]}#
  | EH_Seq  : forall P c Q d R,
      Sigma |- {[P]} c {[Q]}# ->
      Sigma |- {[Q]} d {[R]}# ->
      Sigma |- {[P]} c;;d {[R]}#
  | EH_If : forall P Q b c1 c2,
      Sigma |- {[fun st => P st /\ bassn b st]} c1 {[Q]}# ->
      Sigma |- {[fun st => P st /\ ~(bassn b st)]} c2 {[Q]}# ->
      Sigma |- {[P]} TEST b THEN c1 ELSE c2 FI {[Q]}#
  | EH_While : forall P M b c,
      (forall n : nat,
          Sigma |- {[fun st => P st /\ bassn b st /\ M n st]} c {[fun st => P st /\ exists n', M n' st /\ n' < n]}#) ->
      Sigma |- {[fun st => P st /\ exists n, M n st]} WHILE b DO c END {[fun st => P st /\ ~ (bassn b st)]}#
  | EH_Consequence  : forall (P Q P' Q' : Assertion) c,
      Sigma |- {[P']} c {[Q']}# ->
      (forall st, P st -> P' st) ->
      (forall st, Q' st -> Q st) ->
      Sigma |- {[P]} c {[Q]}#

  | EH_Spec : forall Q y f xs params,
      Sigma |- {[fun st =>
            (Sigma f).(preEx) params (aseval st xs) /\
            (exists v, (Sigma f).(postEx) v params (aseval st xs)) /\
            forall v, (Sigma f).(postEx) v params (aseval st xs) ->
                      Q[y |-> v] st]} y :::= f $ xs {[Q]}#

  where "Sigma |- {[ P ]}  c  {[ Q ]}#" := (ehoare_proof Sigma P c Q) : hoare_spec_scope.

  Definition ehoare_triple
             (ESigma : ExEnv)
             (P : Assertion)
             (c : com)
             (Q : Assertion) : Prop :=
    forall st,
      P st ->
      exists st' (exe : MustEval ESigma st c st'), Q st'.

  (*Theorem produces_productive_com (Sigma : ExEnv)
          (SigmaOK : Consistent_Env Sigma)
    : forall (c : com) (P Q : Assertion),
      ehoare_triple funSigs funSpecs funExSpecs P c Q ->
      forall st, P st ->
                 Productive
                   {| AllEnv := {| funSigs := funSigs; funSpecs := funSpecs; funDefs := empty |}; funExSpecs := funExSpecs |}
                   c st Q.
  Proof.
    induction c; unfold ehoare_triple; intros.
    - edestruct (H empty) as [st' [exe ?] ]; eauto using productive_empty;
        inversion exe; subst.
      econstructor.
      econstructor.
      unfold Included, In; intros; inversion H2; subst; eauto.
    - eapply H in H0; eauto using productive_empty; clear H.
      destruct H0 as [st' [exe ?] ].
      econstructor.
      econstructor.
      unfold Included, In; intros; inversion H0; subst; eauto.
      inversion exe; subst; eauto.
    - (*econstructor.
      eapply (H (f |-> {|funBody := _|}; empty)) in H0.
      destruct H0 as [st' [exe ?] ].
      inversion exe.
      simpl in H4; rewrite update_eq in H4; discriminate.
      simpl in H6; rewrite update_eq in H6; injections; simpl in *.
      eapply Productive_CallSpec.
      reflexivity. *)
      admit.
    - eapply (H _ (productive_empty _ _ _)) in H0.
      destruct H0 as [st' [exe ?] ].
      inversion exe; subst.


      econstructor.
      eapply IHc1; eauto.

      intros ? ? ? ? ?.



    - destruct IHProductive as [st' [exe Q_st'] ].
      assert (AllEnv |- st =[ TEST b THEN c1 ELSE c2 FI ]=> st') by (econstructor; eauto).
      eexists _, H1 ; eauto.
    - destruct IHProductive as [st' [exe Q_st'] ].
      assert (AllEnv |- st =[ TEST b THEN c1 ELSE c2 FI ]=> st') by (econstructor; eauto).
      eexists _, H1; eauto.
    - assert (AllEnv |- st =[ WHILE b DO c END ]=> st) by (econstructor; eauto).
      eexists _, H0; eauto; econstructor.
    - destruct IHProductive as [st' [exe Q_st'] ].
      specialize (H1 _ Q_st'); destruct (H2 _ Q_st') as [st'' [exe' Q'_st']].
      assert (AllEnv |- st =[ WHILE b DO c END ]=> st'') by (econstructor; eauto).
      eauto.
    - destruct IHProductive as [st' [exe Q_st'] ].
      eassert (AllEnv |- st =[ x :::= f $ args ]=> _) by (eapply (@E_CallDef AllEnv); eauto).
      eexists _, H1; eauto.
    - eassert (AllEnv |- st =[ x :::= f $ args ]=> _) by (eapply (@E_CallSpec AllEnv); eauto).
      eexists _, H4; eauto.
    - destruct IHProductive as [st' [exe Q_st'] ]; eexists _, exe; eauto.
      eapply H0; apply Q_st'.
  Qed.
 *)

  Notation "ESigma |= {[ P ]}  c  {[ Q ]}#" :=
    (ehoare_triple ESigma P c Q) (at level 90, c at next level)
    : hoare_spec_scope.

  Hint Resolve bassn_eval_true bassn_eval_false : hoare.
  Hint Constructors ehoare_proof : hoare.
  Hint Constructors ceval.

  Local Hint Constructors ceval.
  Local Hint Constructors AppearsIn.

  Hint Constructors Productive : hoare.

  Theorem ehoare_proof_produces {Sigma : ExEnv}
    : forall (P Q : Assertion) c
      (consistent_Sigma : Consistent_Env Sigma),
      productive_Env Sigma ->
      funExSpecs |- {[P]} c {[Q]}# ->
      forall st,
        P st ->
        Productive {| AllEnv := {| funSigs := @funSigs AllEnv;
                                   funSpecs := @funSpecs AllEnv;
                                   funDefs := empty |};
                      funExSpecs := funExSpecs |} c st Q.
  Proof.
    induction 3; intros; eauto.
    - eapply Productive_Weaken; try solve [econstructor; eauto].
      unfold Included, In; intros; inversion H1; subst; eauto.
    - eapply Productive_Weaken; try solve [econstructor].
      unfold Included, In; intros; inversion H1; subst; eauto.
    - eapply Productive_Weaken; try solve [econstructor; eauto].
      firstorder.
    - destruct (beval st b) eqn:?.
      + eapply Productive_Weaken; try solve [econstructor; eauto].
        firstorder.
      + eapply Productive_Weaken.
        * eapply Productive_IfFalse; firstorder eauto.
          eapply IHehoare_proof2; firstorder eauto with hoare.
          eapply bassn_eval_false; eauto.
        * firstorder.
    - destruct H2 as [P_st [n M' ] ].
      revert dependent st.
      induction n as [n IH] using (well_founded_ind lt_wf). intros.
      destruct (beval st b) eqn:?.
      + econstructor; eauto; intros.
        destruct H2 as [P_st' [n' [M_n' lt_n'] ] ]; eauto.
      + eapply Productive_Weaken; eauto using Productive_WhileFalse.
        unfold Included, In; intros.
        inversion H2; subst; intuition.
        eapply bassn_eval_false; eauto.
    - eapply Productive_Weaken; eauto.
    - destruct H0 as [? [ [n ?] ?] ] .
      eapply Productive_Weaken; eauto.
      + eapply Productive_CallSpec; firstorder eauto.
      + unfold Included, In; intros.
        destruct H3 as [n' [? ?] ]; subst.
        eapply H2; eauto.
  Qed.

  Theorem ehoare_proof_link {Sigma : ExEnv}
    : forall (P Q : Assertion) c,
      productive_Env Sigma ->
      Consistent_Env Sigma ->
      funExSpecs |- {[P]} c {[Q]}# ->
      Sigma |= {[P]} c {[Q]}#.
  Proof.
    unfold ehoare_triple; intros.
    eapply productive_com_MustEval.
    eapply productive_Env_produces; eauto.
    eapply ehoare_proof_produces; eauto.
  Qed.

  (*Lemma ehoare_while (Sigma : Env)  : forall P M b c,
      (forall n : nat,
          Sigma |= {[fun st => P st /\ bassn b st /\ M n st]} c {[fun st => P st /\ exists n', M n' st /\ n' < n]}#) ->
      Sigma |= {[fun st => P st /\ exists n, M n st]} WHILE b DO c END {[fun st => P st /\ ~ (bassn b st)]}#.
  Proof.
    unfold ehoare_triple.
    intros P M b c Hc st [HP H]. destruct H as [n HM]. revert dependent st.
    induction n as [n IH] using (well_founded_ind lt_wf). intros.
    destruct (beval st b) eqn:?.
    - edestruct Hc; eauto. destruct_conjs.
      edestruct IH; eauto. destruct_conjs.
      eauto.
    - repeat econstructor; eauto. firstorder with hoare.
  Qed. *)

   Lemma Empty_PreCondition :
    forall Sigma c Q,
        Sigma |- {[fun _ : state => False]} c {[Q]}#.
  Proof.
    induction c.
    - intros; econstructor; intuition eauto; econstructor.
    - intros; econstructor; intuition eauto; econstructor.
    - intros; econstructor.
      eapply EH_Spec.
      intros; intuition eauto.
      eauto.
    - econstructor; eauto.
    - econstructor; eauto.
      + econstructor; intuition eauto.
      + econstructor; intuition eauto.
    - intros; econstructor.
      econstructor.
      econstructor.
      eapply IHc.
      instantiate (1 := fun _ _ => False).
      intros ? [? [? ?] ].
      apply H.
      intros.
      split; try eapply H.
      intuition.
      intuition.
      simpl; intuition eauto.
      simpl; intuition eauto.
      Grab Existential Variables.
      econstructor.
  Qed.

  Definition ewp (ESigma : ExEnv) (c:com) (Q:Assertion) : Assertion :=
    fun st => exists st' (exe : MustEval ESigma st c st'), Q st'.

  Lemma ewp_is_precondition {Sigma : ExEnv}
        (SigmaOK : Consistent_Env Sigma)
        (SigmaOK' : productive_Env Sigma)
    : forall c Q,
      Sigma |= {[ewp Sigma c Q]} c {[Q]}#.
  Proof.
    firstorder eauto.
  Qed.

  Lemma ewp_is_weakest (Sigma : ExEnv)
    : forall c Q P,
      Sigma |= {[P]} c {[Q]}# -> P ->> ewp Sigma c Q.
  Proof.
    firstorder.
  Qed.

  Fixpoint gammaE'
           (Q : Assertion)
           (c : com)
           (b : bexp)
           (WP : Assertion -> Assertion)
           (n : nat) : Assertion :=
    match n with
    | 0 => fun st => ~ bassn b st /\ Q st
    | S n' => fun st => bassn b st /\ WP (gammaE' Q c b WP n') st
    end.

  Fixpoint ewp_gen'
           (funSpecs : total_map funExSpec)
           (c : com)
           (Q : Assertion) {struct c} : Assertion :=
    match c with
    | CSkip => Q
    | CAss x a => Q [x |-> a]
    | CCall x f args =>
      fun st => (exists os,
                      (funSpecs f).(preEx) os (aseval st args) /\
                      (exists v, (funSpecs f).(postEx) v os (aseval st args)) /\
                      (forall v, (funSpecs f).(postEx) v os (aseval st args)
                                 -> Q[x |-> v] st))
    | CSeq c1 c2 => ewp_gen' funSpecs c1 (ewp_gen' funSpecs c2 Q)
    | CIf b c1 c2 => fun st => (bassn b st -> ewp_gen' funSpecs c1 Q st)
                               /\ (~ bassn b st -> ewp_gen' funSpecs c2 Q st)
    | CWhile b c => fun st => exists n, gammaE' Q c b
                           (fun Q st => (bassn b st -> ewp_gen' funSpecs c Q st)
                                        /\ (~ bassn b st -> Q st)) n st
    end.

  Fixpoint unroll_loop' (n : nat)
           (b : bexp)
           (c : com)
    : com :=
    match n with
      0 => CSkip
    | S n'  => CIf b (c ;; (unroll_loop' n' b c)) CSkip
    end.

  Lemma unroll_loop_eqv_while Sigma :
    forall b c st st',
      MustEval Sigma st (CWhile b c) st' ->
      ~ bassn b st' /\ exists n, MustEval Sigma st (unroll_loop' n b c) st'.
  Proof.
    intros.
    remember (CWhile b c); revert b c Heqc0; induction H; intros; subst;
      try solve [inversion Heqc0]; injections; split.
    - eapply bassn_eval_false; eauto.
    - exists 0; simpl; econstructor.
    - destruct (IHMustEval2 _ _ (eq_refl _)) as [? [n' ?] ]; eauto.
    - destruct (IHMustEval2 _ _ (eq_refl _)) as [? [n' ?] ].
      eexists (S n'); simpl; eauto.
      econstructor; eauto.
      econstructor; eauto.
  Qed.

  Lemma ewp_gen'_is_monotone
    Sigma
    : forall (c : com) (a : state) (S S' : state -> Prop),
      (forall a0 : state, S a0 -> S' a0) -> ewp_gen' Sigma c S a -> ewp_gen' Sigma c S' a.
  Proof.
    induction c; simpl; intros; eauto.
    - unfold assn_sub; eauto.
    - unfold assn_sub in *; eauto.
      destruct H0 as [os [? [ [v ?] ?] ] ].
      eexists os; intuition eauto.
    - intuition; eauto.
    - destruct H0 as [n ?].
      eexists n.
      generalize dependent a.
      induction n; simpl in *; intuition eauto.
  Qed.

  Hint Resolve ewp_is_precondition ewp_is_weakest : hoare.
  Hint Unfold ehoare_triple ewp.

  Lemma ewp_gen'_is_ewp ESigma
        (ESigmaOK : productive_Env ESigma)
    : forall c (Q : Assertion) sigma,

      ewp {| AllEnv := {| funSigs := @funSigs AllEnv;
                                   funSpecs := @funSpecs AllEnv;
                                   funDefs := empty |};
                      funExSpecs := funExSpecs |}
          c Q sigma
      -> ewp_gen' (@funExSpecs ESigma) c Q sigma.
  Proof.
    induction c; simpl; intros.
    - destruct H as [? [H ?] ].
      inversion H; subst; firstorder eauto.
    - destruct H as [? [H ?] ].
      inversion H; subst; firstorder eauto.
    - destruct H as [? [H ?] ].
       inversion H; subst.
       + simpl in H6; rewrite apply_empty in H6; discriminate.
       + eexists params; intuition eauto.         (*remember (CCall x f args).
      induction H; try discriminate; injections.
      + clear IHProductive. admit.
      + eexists params; firstorder eauto.
      + eapply IHProductive in Heqc; clear IHProductive.
        destruct Heqc as [params [? [? ?] ] ]; eexists _; firstorder eauto.
        eapply H0; eapply H3; eauto. *)
      admit.
    - destruct H as [? [H ?] ].
      inversion H; subst.
      eapply IHc1.
      eexists _, _; eauto.
    - destruct H as [? [H ?] ].
      inversion H; subst.
      + split; intros.
        * eapply IHc1; eauto.
        * eapply bassn_eval_false in H1; congruence.
      + split; intros.
        * eapply bassn_eval_false in H6; congruence.
        * eauto.
    - destruct H as [? [H ?] ].
      eapply unroll_loop_eqv_while in H; destruct H as [? [n ?] ].
      revert IHc Q sigma x H H1 H0.
      induction n; simpl; intros.
      + eexists 0; simpl; inversion H1; subst; eauto.
      + inversion H1; subst; clear H1; eauto.
        * inversion H8; subst; clear H8.
          eapply bassn_eval_true in H7.
          destruct (IHn IHc _ _ _ H H6 H0) as [n' ?].
          eexists (S n'); simpl.
          intuition eauto.
        * inversion H8; subst; intuition eauto.
          inversion H8; subst; simpl; eexists 0; simpl; eauto.
          Grab Existential Variables.
          eauto.
  Admitted.

  Theorem hoare_proof_ewp' Sigma : forall c Q,
      Sigma |- {[ewp_gen' Sigma c Q]} c {[Q]}#.
  Proof.
    (* Need to pull prophecy vars out somehow... *)
    induction c; simpl; intros; try solve [econstructor].
    - admit. (* econstructor.
      2: { intros.
           destruct H.
           exact H.
      eapply EH_Spec.
      intros ? [os [? [ [v' ?] ?] ] ].

     firstorder eauto. *)
    - econstructor; eauto.
    - econstructor; eauto.
      + econstructor; firstorder eauto.
      + econstructor; firstorder eauto.
    - econstructor.
      econstructor.
      2: { intros.
           simpl; split.
           exact H.
           eauto.
      }
      intro; revert IHc.
      2: { simpl; intros.
           destruct H as [ [n ?] ?].
           destruct n; simpl in H; intuition eauto.
      }
      simpl.
      destruct n; simpl; intros.
      + econstructor.
        eapply Empty_PreCondition.
        intuition.
        intros; eapply H.
      + econstructor.
      2: intros; destruct H as [_ ?]; eapply H.
      2: { intros; split;
           [ eexists n; apply H | ].
           eexists n; eauto. }
      econstructor.
      eapply IHc.
      2: eauto.
      intros; intuition.
  Admitted.

  Theorem ehoare_proof_complete Sigma
          (Sigma_OK : Consistent_Env Sigma)
          (Sigma_OK' : productive_Env Sigma)
    : forall P c Q,
      {| AllEnv := {| funSigs := @funSigs AllEnv;
                                   funSpecs := @funSpecs AllEnv;
                                   funDefs := empty |};
                      funExSpecs := funExSpecs |} |= {[P]} c {[Q]}# ->
      funExSpecs |- {[P]} c {[Q]}#.
  Proof.
    intros; econstructor.
    - eapply hoare_proof_ewp'.
    - intros.
      eapply ewp_gen'_is_ewp; eauto.
    - eauto.
  Qed.

  (* The Productive predicate and the existential hoare rules should
  be equivalent. This proof will let us prove the soundness of vc
  generation with respect to the hoare rules. *)
  Theorem produces_ehoare_proof {Sigma : ExEnv}
    : forall c (P Q : Assertion),
      productive_Env Sigma ->
      Consistent_Env Sigma ->
      (forall st,
        P st ->
        Productive {| AllEnv := {| funSigs := @funSigs AllEnv;
                                   funSpecs := @funSpecs AllEnv;
                                   funDefs := empty |};
                      funExSpecs := funExSpecs |}
                      c st Q) ->
        funExSpecs |- {[P]} c {[Q]}#.
  Proof.
    intros; econstructor.
    - eapply hoare_proof_ewp'.
    - intros.
      eapply H1 in H2.
      eapply ewp_gen'_is_ewp; eauto.
      unfold ewp; intros.
  Abort.
(*      eapply (productive_com_produces); eauto.
      eapply productive_Env_produces; eauto.
    - eauto.
  Qed. *)

  Definition FClosed {A : Type} (F : (A -> Prop) -> A -> Prop)
             (S : A -> Prop) : Prop :=
    forall a, F S a -> S a.

  Definition LFP {A : Type} (F : (A -> Prop) -> A -> Prop) : A -> Prop :=
    fun a => forall S, FClosed F S -> S a.

  Definition Monotonic_F {A : Type} (F : (A -> Prop) -> A -> Prop) : Prop :=
    forall (S S' : A -> Prop),
      (forall a, S a -> S' a) -> forall a, F S a -> F S' a.

  Lemma LFP_is_FClosed {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F)
             (a : A),
      F (LFP F) a -> LFP F a.
  Proof.
    unfold LFP, FClosed; intros.
    eapply H0.
    eapply F_Monotone.
    2: eapply H.
    firstorder eauto.
  Qed.

  Lemma LFP_is_FConsistent {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F)
             (a : A),
      LFP F a -> F (LFP F) a.
  Proof.
    unfold LFP, FClosed; intros.
    eapply H; intros.
    eapply F_Monotone.
    2: eapply H0.
    simpl; intros.
    unfold LFP, FClosed; intros.
    eapply H2.
    eapply F_Monotone.
    2: eapply H1.
    intros.
    eapply H2.
    unfold LFP in H3.
    eapply H3.
    unfold FClosed.
    intros.
    eapply F_Monotone.
    2: eapply H4.
    simpl; eauto.
  Qed.

  Lemma LFP_is_FixedPoint {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F)
             (a : A),
      F (LFP F) a <-> LFP F a.
  Proof.
    split; intros.
    - eapply LFP_is_FClosed; eauto.
    - eapply LFP_is_FConsistent; eauto.
  Qed.

  Lemma Ind {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop) (Ind : A -> Prop),
      FClosed F Ind -> forall a, LFP F a -> Ind a.
  Proof.
    unfold LFP, FClosed; intros; eapply H0; eauto.
  Qed.

  Definition gammaE
           (Q : Assertion)
           (c : com)
           (b : bexp)
           (WP : Assertion -> Assertion)
    : Assertion :=
    @LFP state (fun (G : _ -> _) (st : state) => (~ bassn b st /\ Q st)
                                                 \/ (bassn b st /\ WP G st)).

  (* (* Inductive gammaE'' *)
  (*           (Q : Assertion) *)
  (*           (c : com) *)
  (*           (b : bexp) *)
  (*           (WP : Assertion -> Assertion) *)
  (*   : Assertion := *)
  (* | Base : forall st, *)
  (*     ~ bassn b st -> Q st -> gammaE'' Q c b WP st *)
  (* | Step : forall st, *)
  (*     bassn b st -> *)
  (*     WP (gammaE'' Q c b WP) st *)
  (*     -> gammaE'' Q c b WP st. *) *)

  Fixpoint ewp_gen
           (funSpecs : total_map funExSpec)
           (c : com)
           (Q : Assertion) {struct c} : Assertion :=
    match c with
    | CSkip => Q
    | CAss x a => Q [x |-> a]
    | CCall x f args =>
      fun st => (exists os,
                      (funSpecs f).(preEx) os (aseval st args) /\
                      (exists v, (funSpecs f).(postEx) v os (aseval st args)) /\
                      (forall v, (funSpecs f).(postEx) v os (aseval st args)
                                 -> Q[x |-> v] st))
    | CSeq c1 c2 => ewp_gen funSpecs c1 (ewp_gen funSpecs c2 Q)
    | CIf b c1 c2 => fun st => (bassn b st -> ewp_gen funSpecs c1 Q st)
                               /\ (~ bassn b st -> ewp_gen funSpecs c2 Q st)
    | CWhile b c => gammaE Q c b
                           (fun Q st => (bassn b st -> ewp_gen funSpecs c Q st)
                                        /\ (~ bassn b st -> Q st))
    end.

  Lemma ewp_gen_is_monotone
    Sigma
    : forall (c : com) (a : state) (S S' : state -> Prop),
      (forall a0 : state, S a0 -> S' a0) -> ewp_gen Sigma c S a -> ewp_gen Sigma c S' a.
  Proof.
    induction c; simpl; intros; eauto.
    - unfold assn_sub; eauto.
    - unfold assn_sub in *; eauto.
      destruct H0 as [os [? [ [v ?] ?] ] ].
      eexists os; intuition eauto.
    - intuition; eauto.
    - unfold gammaE, LFP, FClosed in *; intros.
      eapply H0; intuition eauto.
  Qed.

  Definition LoopVariant
             ESigma
             (c : com)
             (b : bexp)
             (Inv : Assertion)
             (Q1 Q2 : Assertion)
    : Prop :=
    forall st1 st2,
      Inv st1 ->
      Inv st2 ->
      bassn b st1 ->
      bassn b st2 ->
      Productive ESigma c st1 Q1 ->
      Productive ESigma c st2 Q2.
  (*(gammaE Q1 c b
                       (fun Q st => (bassn b st -> ewp_gen funSpecs c Q st)
                                    /\ (~ bassn b st -> Q st)))
             (gammaE Q2 c b
                     (fun Q st => (bassn b st -> ewp_gen funSpecs c Q st)
                                  /\ (~ bassn b st -> Q st))) *)

  Lemma well_founded_gammaE :
    forall (ESigma : ExEnv)
           (c : com)
           (b : bexp)
           (Q Inv : Assertion)
           (st : state),
      Productive ESigma (CWhile b c) st Q ->
      well_founded (LoopVariant ESigma c b Inv).
  Proof.
    intros.
    remember (CWhile b c); induction H; try discriminate.
    econstructor.
    unfold well_founded, LoopVariant; intros.
    constructor; intros.



  Lemma ewp_gen_is_ewp
        Sigs Sigma ESigma'
        (ESigma :=
           {| AllEnv := {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |};
              funExSpecs := ESigma' |})
    : forall c Q sigma,
      Productive ESigma c sigma Q
      -> ewp_gen (@funExSpecs ESigma) c Q sigma.
  Proof.
    induction c; simpl; intros.
    - eapply productive_com_produces in H.
      destruct H as [? [H ?] ]; inversion H; subst; eauto.
    - eapply productive_com_produces in H.
      destruct H as [? [H ?] ]; inversion H; subst; eauto.
    - remember (CCall x f args).
      induction H; try discriminate; injections.
      + eexists params; firstorder eauto.
      + eapply IHProductive in Heqc; clear IHProductive.
        destruct Heqc as [params [? [? ?] ] ]; eexists _; firstorder eauto.
        eapply H0; eapply H3; eauto.
    - remember (CSeq c1 c2).
      induction H; try discriminate; injections.
      + clear IHProductive.
        eapply IHc1.
        econstructor; eauto.
        intros ? ?; unfold In in *.
        eauto.
      + eapply ewp_gen_is_monotone; [ | intros; eauto].
        intros.
        eapply ewp_gen_is_monotone; eauto.
    - remember (CIf b c1 c2).
      induction H; try discriminate; injections.
      + split; intros.
        * eapply IHc1; eauto.
        * eapply bassn_eval_false in H1; congruence.
      + split; intros.
        * eapply bassn_eval_false in H; congruence.
        * eauto.
      + eapply IHProductive in Heqc; clear IHProductive.
        intuition; eapply ewp_gen_is_monotone; eauto.
    - remember (CWhile b c).
      induction H; try discriminate; injections.
     + eapply LFP_is_FClosed; intuition eauto.
       * unfold Monotonic_F; intros; intuition eauto.
         right; intuition auto.
         eapply ewp_gen_is_monotone; eauto.
       * left; intuition.
         eapply bassn_eval_false; eauto.
     + eapply LFP_is_FClosed; intuition eauto.
       * unfold Monotonic_F; intros; intuition eauto.
         right; intuition auto.
         eapply ewp_gen_is_monotone; eauto.
       * right; eapply bassn_eval_true in H; intuition.
         eapply IHc.
         econstructor; eauto.
         unfold Included, In; intros; eapply H2; eauto.
     + eapply IHProductive in Heqc0; clear IHProductive.
       eapply Ind; eauto.
       unfold FClosed; intros.
       eapply LFP_is_FClosed; intuition eauto.
       * unfold Monotonic_F; intros; intuition eauto.
         right; intuition auto.
         eapply ewp_gen_is_monotone; eauto.
       * unfold Monotonic_F; intros; intuition eauto.
         right; intuition auto.
         eapply ewp_gen_is_monotone; eauto.
       * firstorder eauto.
  Qed.

  Theorem hoare_proof_ewp (Sigma : ExEnv) : forall c Q,
      ehoare_proof funExSpecs (ewp_gen funExSpecs c Q) c Q.
  Proof.
    (* Need to pull prophecy vars out somehow... *)
    induction c; simpl; intros; try solve [econstructor].
    - admit. (* econstructor.
      2: { intros.
           destruct H.
           exact H.
      eapply EH_Spec.
      intros ? [os [? [ [v' ?] ?] ] ].

     firstorder eauto. *)
    - econstructor; eauto.
    - econstructor; eauto.
      + econstructor; firstorder eauto.
      + econstructor; firstorder eauto.
    - econstructor.
      + econstructor.
        instantiate (2 := gammaE Q c b
                                   (fun Q st => (bassn b st -> ewp_gen funExSpecs c Q st)
                                                /\ (~ bassn b st -> Q st))).
          instantiate (2 := gammaE' Q c b
                                   (fun Q st => (bassn b st -> ewp_gen funExSpecs c Q st)
                                                /\ (~ bassn b st -> Q st))).
          simpl.
          induction n; simpl.
          * econstructor.
            eapply Empty_PreCondition.
            intuition.
            intros; eapply H.
          * econstructor.
            eapply IHn.
            -- simpl; intros; intuition.
               admit.
            -- simpl; intros.
               intuition.
               destruct H1; intuition eauto.
      + simpl; intros. split; eauto. admit.
      + intros ? [? ?].
        eapply LFP_is_FConsistent in H; intuition.
        unfold Monotonic_F; intros; intuition eauto.
        right; intuition.
        eapply ewp_gen_is_monotone; eauto.
  Admitted.

  (* The Productive predicate and the existential hoare rules should
  be equivalent. This proof will let us prove the soundness of vc
  generation with respect to the hoare rules. *)
  Theorem produces_ehoare_proof {Sigma : ExEnv}
    : forall c (P Q : Assertion),
      productive_Env Sigma ->
      Consistent_Env Sigma ->
      (forall st,
        P st ->
        Productive {| AllEnv := {| funSigs := @funSigs AllEnv;
                                   funSpecs := @funSpecs AllEnv;
                                   funDefs := empty |};
                      funExSpecs := funExSpecs |}
                      c st Q) ->
        funExSpecs |- {[P]} c {[Q]}#.
  Proof.
    intros; econstructor.
    - eapply hoare_proof_ewp.
    - intros.
      eapply H1 in H2.
      eapply ewp_gen_is_ewp; eauto.
    - eauto.
  Qed.

  Print Assumptions produces_ehoare_proof.

  Inductive ehoare_proof' (Sigma : ExEnv)
    : Assertion -> com -> Assertion -> Prop :=
  | EH_Skip' : forall P,
      Sigma |- {[P]} SKIP {[P]}#
  | EH_Asgn' : forall Q V a,
      Sigma |- {[Q[V |-> a]]} V ::= a {[Q]}#
  | EH_Seq'  : forall P c Q d R,
      Sigma |- {[P]} c {[Q]}# ->
      Sigma |- {[Q]} d {[R]}# ->
      Sigma |- {[P]} c;;d {[R]}#
  | EH_If' : forall P Q b c1 c2,
      Sigma |- {[fun st => P st /\ bassn b st]} c1 {[Q]}# ->
      Sigma |- {[fun st => P st /\ ~(bassn b st)]} c2 {[Q]}# ->
      Sigma |- {[P]} TEST b THEN c1 ELSE c2 FI {[Q]}#
  | EH_While' : forall R P b c,
      well_founded R ->
      Sigma |- {[fun st => P st /\ bassn b st]} c {[fun st => P st
                                                              /\ R st st]}# ->
               Sigma |- {[fun st => P st]} WHILE b DO c END {[fun st => P st
                                                                        /\ ~ (bassn b st)                                                               ]}#
  | EH_Consequence'  : forall (P Q P' Q' : Assertion) c,
      Sigma |- {[P']} c {[Q']}# ->
      (forall st, P st -> P' st) ->
      (forall st, Q' st -> Q st) ->
      Sigma |- {[P]} c {[Q]}#

  | EH_Spec' : forall Q y f xs params,
      Sigma |- {[fun st =>
            (funExSpecs f).(preEx) params (aseval st xs) /\
            (exists v, (funExSpecs  f).(postEx) v params (aseval st xs)) /\
            forall v, (funExSpecs  f).(postEx) v params (aseval st xs) ->
                      Q[y |-> v] st]} y :::= f $ xs {[Q]}#

  where "Sigma |- {[ P ]}  c  {[ Q ]}#" := (ehoare_proof' Sigma P c Q) : hoare_spec_scope'.

  Theorem ehoare_proof'_sound {Sigma : ExEnv}
    : forall (P Q : Assertion) c
      (consistent_Sigma : Consistent_Env Sigma),
      productive_Env Sigma ->
      ehoare_proof' Sigma P c Q ->
      forall st,
        P st ->
        Productive {| AllEnv := {| funSigs := @funSigs AllEnv;
                                   funSpecs := @funSpecs AllEnv;
                                   funDefs := empty |};
                      funExSpecs := funExSpecs |} c st Q.
  Proof.
    induction 3; intros; eauto.
    - eapply Productive_Weaken; try solve [econstructor; eauto].
      unfold Included, In; intros; inversion H1; subst; eauto.
    - eapply Productive_Weaken; try solve [econstructor].
      unfold Included, In; intros; inversion H1; subst; eauto.
    - eapply Productive_Weaken; try solve [econstructor; eauto].
      firstorder.
    - destruct (beval st b) eqn:?.
      + eapply Productive_Weaken; try solve [econstructor; eauto].
        firstorder.
      + eapply Productive_Weaken.
        * eapply Productive_IfFalse; firstorder eauto.
          eapply IHehoare_proof'2; firstorder eauto with hoare.
          eapply bassn_eval_false; eauto.
        * firstorder.
    - destruct (beval st b) eqn: ?.
      2: { eapply Productive_Weaken.
           eapply Productive_WhileFalse; eauto.
           unfold Included, In; intros.
           inversion H2; subst; intuition eauto.
           eapply bassn_eval_false; eauto. }
      econstructor; eauto.
      eapply IHehoare_proof'.

      eapply bassn_eval_true in Heqb0.
      specialize (IHehoare_proof' _ (conj H1 Heqb0)).
      econstructor; simpl; eauto; intros.
      eapply
      pattern st.

      econstructor; eauto.
      intros.
      pattern st'.
      eapply well_founded_ind; eauto; intros.
      eapply H5.

      econstructor; eauto; simpl; intros.

      admit.
    - eapply Productive_Weaken; eauto.
    - destruct H0 as [? [ [n ?] ?] ] .
      eapply Productive_Weaken; eauto.
      + eapply Productive_CallSpec; firstorder eauto.
      + unfold Included, In; intros.
        destruct H3 as [n' [? ?] ]; subst.
        eapply H2; eauto.
  Admitted.

  Theorem hoare_proof_ewp (Sigma : ExEnv) : forall c Q,
      ehoare_proof' Sigma (ewp_gen funExSpecs c Q) c Q.
  Proof.
    (* Need to pull prophecy vars out somehow... *)
    induction c; simpl; intros; try solve [econstructor].
    - admit. (* econstructor.
      2: { intros.
           destruct H.
           exact H.
      eapply EH_Spec.
      intros ? [os [? [ [v' ?] ?] ] ].

     firstorder eauto. *)
    - econstructor; eauto.
    - econstructor; eauto.
      + econstructor; firstorder eauto.
      + econstructor; firstorder eauto.
    - econstructor.
      econstructor.
      (*pose  (fun st st' => Included _
                                    (gammaE Q c b
                                            (fun (Q : Assertion) (st : state) => (bassn b st -> ewp_gen funExSpecs c Q st) /\ (~ bassn b st -> Q st)) st')
                                    (gammaE Q c b
                                            (fun (Q : Assertion) (st : state) => (bassn b st -> ewp_gen funExSpecs c Q st) /\ (~ bassn b st -> Q st))) st).

      admit. *)
      2: intros; eapply H.
      + econstructor; eauto; intros.
        intuition.
        eapply LFP_is_FConsistent in H0; intuition.
        unfold Monotonic_F; intros; intuition eauto.
        right; intuition.
        eapply ewp_gen_is_monotone; eauto.
      + intros; intuition.
        intuition.
        eapply LFP_is_FConsistent in H0; intuition.
        unfold Monotonic_F; intros; intuition eauto.
        right; intuition.
        eapply ewp_gen_is_monotone; eauto.
  Admitted.


  (* Fixpoint LFPn' {A : Type} (F : (A -> Prop) -> A -> Prop) *)
  (*          (n : nat) *)
  (*   : A -> Prop := *)
  (*   match n with *)
  (*   | 0 => fun _ => False *)
  (*   | S n' => F (LFPn' F n') *)
  (*   end. *)

  (* Definition LFPn {A : Type} (F : (A -> Prop) -> A -> Prop) : A -> Prop := *)
  (*   fun a => exists n, LFPn' F n a. *)

  (* Lemma LFPn_is_FConsistent {A : Type} *)
  (*   : forall (F : (A -> Prop) -> A -> Prop) *)
  (*            (F_Monotone : Monotonic_F F) *)
  (*            (a : A), *)
  (*     LFPn F a -> F (LFPn F) a. *)
  (* Proof. *)
  (*   unfold LFP, FClosed; intros. *)
  (*   destruct H as [n ?]. *)
  (*   induction n. *)
  (*   - simpl in H; intuition. *)
  (*   - eapply F_Monotone; intros. *)
  (*     2: simpl in H; eauto. *)
  (*     unfold LFPn. *)
  (*     eauto. *)
  (* Qed. *)

  (*Lemma LFPn_is_FClosed {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F)
             (a : A),
      F (LFPn F) a -> LFPn F a.
  Proof.
    unfold LFPn; intros.
    assert (forall (a' : {a | LFPn F a}), exists n, LFPn' F n (proj1_sig a')).
    intros.
    destruct a' as [? [? ?] ].
    ee
    eexists; simpl; eassumption.
    eapply choice in H0.
    destruct H0.



    assert (exists m, forall a, F

    assert (exists n, LFPn' F (S n) a).
    simpl.

    assert (F (F (fun a : A => exists n : nat, LFPn' F n a)) a).
    { eapply F_Monotone.
      intros.
      2: eapply H.
      simpl in H0.
      destruct H0.
      admit.
    }
    firstorder eauto.

  Lemma LFPn_is_FConsistent {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F)
             (a : A),
      LFPn F a -> F (LFPn F) a.
  Proof.
    intros ? ? ? [n ?].
    revert a H.
    unfold LFPn.
    generalize (fun k : A -> Prop => k).
    induction n; simpl; intros.
    - admit.
    - eapply F_Monotone.
      2: eapply IHn; eauto.
      simpl; intros.
      destruct H0.
      eexists (S x).

      simpl.
      apply H0.
  Admitted.



  Lemma LFPn_is_FClosed {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F)
             (a : A),
      F (LFPn F) a -> LFPn F a.
  Proof.
    unfold LFPn; intros.
    assert (exists n, LFPn' F (S n) a).
    simpl.

    assert (F (F (fun a : A => exists n : nat, LFPn' F n a)) a).
    { eapply F_Monotone.
      intros.
      2: eapply H.
      simpl in H0.
      destruct H0.
      admit.
    }
    firstorder eauto. *)

  (*Lemma LFPn_is_FClosed {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F)
             (a : A)
             (n : nat),
      F (LFPn' F n) a -> LFPn' F (S n) a .
  Proof.
    simpl; intros; firstorder eauto.
    induction n; simpl in *; eauto.


    unfold LFPn; intros.
    assert (exists n, LFPn' F (S n) a).
    simpl.

  Lemma LFPn_is_FClosed {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F)
             (a : A),
      F (LFPn F) a -> LFPn F a.
  Proof.
    unfold LFPn; intros.
    assert (exists n, LFPn' F (S n) a).
    simpl.

    assert (F (F (fun a : A => exists n : nat, LFPn' F n a)) a).
    { eapply F_Monotone.
      intros.
      2: eapply H.
      simpl in H0.
      destruct H0.
      admit.
    }
    firstorder eauto. *)
  (*Admitted.

  Lemma LFPn_is_FixedPoint {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F)
             (a : A),
      F (LFPn F) a <-> LFPn F a.
  Proof.
    split; intros.
    - eapply LFPn_is_FClosed; eauto.
    - eapply LFPn_is_FConsistent; eauto.
  Qed. *)

  (*Lemma LFPn_eq_LFP {A}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F) a,
      LFP F a <-> LFPn F a.
  Proof.
    split; intros.
    - eapply Ind; eauto.
      unfold FClosed; intros. *)



  (*Theorem ehoare_proof_complete' Sigma
          (Sigma_OK : Consistent_Env Sigma)
          (Sigma_OK' : productive_Env Sigma)
    : forall P c Q,
      ehoare_triple funSigs funSpecs funExSpecs P c Q ->
      funExSpecs |- {[P]} c {[Q]}#.
  Proof.
    intros; econstructor.
    - eapply hoare_proof_ewp'.
    - intros.
      eapply ewp_gen'_is_ewp; eauto.
      unfold ewp.
      intros.
      destruct Sigma0 as [? ? ?]; simpl in *.
      unfold ehoare_triple in H.
      eapply H.
      eapply productive_Env_produces; eauto.
      unfold ehoare_triple in H.
      specialize (H _ H0); destruct H as [st' [exe ?] ].

      admit.
    - eauto.
      eapply (ewp_is_weakest _ _ _ _ H) in H0.
      eapply ewp_gen_is_ewp; eauto.
      unfold Consistent_Env; eauto.
    - eauto.
  Qed.


  (*
  Lemma LFPn_is_FConsistent {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F)
             (a : A),
      LFPn F a -> F (LFPn F) a.
  Proof.
    unfold LFP, FClosed; intros.
    destruct H as [n ?].
    induction n.
    - simpl in H; intuition.
      eapply F_Monotone; intros.
      2: eauto.
      simpl in H0; intuition.
    - eapply F_Monotone; intros.
    2: simpl in H; eauto.
      eauto.
  Qed. *)

  (*Lemma LFPn_is_FClosed {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F)
             (a : A)
             (n : nat),
      F (LFPn' F n) a -> LFPn' F (S n) a .
  Proof.
    simpl; intros; firstorder eauto.
    induction n; simpl in *; eauto.


    unfold LFPn; intros.
    assert (exists n, LFPn' F (S n) a).
    simpl.

  Lemma LFPn_is_FClosed {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F)
             (a : A),
      F (LFPn F) a -> LFPn F a.
  Proof.
    unfold LFPn; intros.
    assert (exists n, LFPn' F (S n) a).
    simpl.

    assert (F (F (fun a : A => exists n : nat, LFPn' F n a)) a).
    { eapply F_Monotone.
      intros.
      2: eapply H.
      simpl in H0.
      destruct H0.
      admit.
    }
    firstorder eauto. *)
  (*Admitted.

  Lemma LFPn_is_FixedPoint {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F)
             (a : A),
      F (LFPn F) a <-> LFPn F a.
  Proof.
    split; intros.
    - eapply LFPn_is_FClosed; eauto.
    - eapply LFPn_is_FConsistent; eauto.
  Qed. *)

  (*Lemma LFPn_eq_LFP {A}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F) a,
      LFP F a <-> LFPn F a.
  Proof.
    split; intros.
    - eapply Ind; eauto.
      unfold FClosed; intros.

    (Q : Assertion)
      (c : com)
      (b : bexp)
      (WP : Assertion -> Assertion)
      (st : state),
      (exists n, gammaE' Q c b WP n st) <->
      gammaE Q c b WP st. *)
  Abort.

  (*Lemma gammaE_eq_gammaE''
      : forall
      Sigma
      (Q : Assertion)
      (c : com)
      (b : bexp)
      (st : state),
      gammaE Q c b
             (fun (Q : Assertion) (st : state) => (bassn b st -> ewp_gen Sigma c Q st) /\ (~ bassn b st -> Q st)) st ->
      (exists n, gammaE' Q c b (fun (Q : Assertion) (st : state) => (bassn b st -> ewp_gen Sigma c Q st) /\ (~ bassn b st -> Q st)) n st).
  Proof.
    intros.
    pattern st; eapply Ind; eauto.
    unfold FClosed; intros; intuition.
    - eexists 0; simpl; eauto.
    - simpl in *.
      eexists (S _).
      simpl; split; eauto.
      unfold gammaE'.
  Admitted. *)

  Lemma gammaE_eq_gammaE'
    : forall
      (Q : Assertion)
      (c : com)
      (b : bexp)
      (WP : Assertion -> Assertion)
      (st : state),
      gammaE Q c b
             WP st ->

      gammaE Q c b WP st ->
      (exists n, gammaE' Q c b WP n st).
  Proof.
    intros.
    pattern st; eapply Ind; eauto.
    unfold FClosed; intros; intuition.
    - eexists 0; simpl; eauto.
    - eexists (S _).
      simpl; split; eauto.
      unfold gammaE'.
  Admitted.




  (* The Productive predicate and the existential hoare rules should
  be equivalent. This proof will let us prove the soundness of vc
  generation with respect to the hoare rules. *)
  Theorem produces_ehoare_proof {Sigma : ExEnv}
    : forall c (P Q : Assertion),
      productive_Env Sigma ->
      (forall st,
        P st ->
        Productive {| AllEnv := {| funSigs := @funSigs AllEnv;
                                   funSpecs := @funSpecs AllEnv;
                                   funDefs := empty |};
                      funExSpecs := funExSpecs |}
                      c st Q) ->
        funExSpecs |- {[P]} c {[Q]}#.
  Proof.
    intros; econstructor.
    - eapply hoare_proof_ewp.
    - intros.
      eapply ewp_gen_is_ewp. eauto.
      eapply H0 in H1.
      eapply productive_Env_produces; eauto.
    - eauto.
  Qed.

  Theorem ehoare_proof_link_complete {Sigma : ExEnv}
    : forall (P Q : Assertion) c,
      productive_Env Sigma ->
      Consistent_Env Sigma ->
      ehoare_triple (@funSigs AllEnv) (@funSpecs AllEnv) funExSpecs P c Q ->
      funExSpecs |- {[P]} c {[Q]}#.
  Proof.
    intros.
    eapply produces_ehoare_proof; eauto.
    intros.
    destruct Sigma as [ [? ? ?] ?].
    eapply H1 in H2; eauto.

    eapply productive_com_produces.
    eapply productive_Env_produces; eauto.
    eapply ehoare_proof_produces; eauto.
  Qed.

  (* Restrict Universal Specs to required behavior. *)
  (*Lemma ewp_gen_is_ewp Sigs Sigma ESigma
        (Sigma_OK : Consistent_Env
                      {| AllEnv := {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |};
                         funExSpecs := ESigma |})
    : forall c Q sigma',
      ewp {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} c Q sigma'
      -> ewp_gen ESigma c Q sigma'.
  Proof.
    induction c; simpl; intros ? ? [st' [H ?] ]; eauto.
    - inversion H; subst; eauto.
    - inversion H; subst; eauto.
    - inversion H; subst; eauto; simpl in *; try discriminate.
      unfold Consistent_Env in Sigma_OK.
      admit.
    - inversion H; subst; eauto.
      eapply IHc1.
      eexists _, H3; eauto.
    - inversion H; subst; intuition eauto.
      eapply bassn_eval_false in H6; intuition eauto.
    - unfold gammaE.
      eapply unroll_loop_eqv_while in H; destruct H as [Not_b [n H]].
      revert Q sigma' st' b c Not_b IHc H H0; induction n; simpl; intros.
      + inversion H; subst.
        eapply LFP_is_FClosed; intuition eauto.
        unfold Monotonic_F; intros; intuition eauto.
        right; intuition auto.
        eapply ewp_gen_is_monotone; eauto.
      + eapply LFP_is_FClosed; intuition eauto.
        * unfold Monotonic_F; intros; intuition eauto.
          right; intuition auto.
          eapply ewp_gen_is_monotone; eauto.
        * inversion H; subst.
          -- right; eapply bassn_eval_true in H6; intuition.
             inversion H7; subst.
             eapply IHc; unfold ewp.
             eexists _, H4.
             eapply IHn; eauto.
          -- inversion H7; subst. intuition.
  Admitted. *)

  (*Theorem ehoare_proof_complete' Sigma
          (Sigma_OK : Consistent_Env Sigma)
          (productive_Sigma : productive_Env Sigma)
    : forall P c Q,
      AllEnv |= {[P]} c {[Q]}# ->
      funExSpecs |- {[P]} c {[Q]}#.
  Proof.
    intros; econstructor.
    - eapply hoare_proof_ewp'.
    - intros.
      eapply ewp_gen'_is_ewp; eauto.
      unfold ewp; intros.
      unfold ehoare_triple in *.
      eapply H in H0.
      destruct H0 as [st' [exe ?] ].
      eexists _, _; eauto.
    - eauto.
  Admitted.

  Lemma unroll_loop_eqv_while' Sigma :
    forall b c st Q,
      Productive Sigma (CWhile b c) st Q ->
      (forall st', Q st' -> ~ bassn b st')
      /\ exists n, Productive Sigma (unroll_loop' n b c) st Q.
  Proof.
    intros.
    remember (CWhile b c); revert b c Heqc0; induction H; intros;
      try solve [inversion Heqc0]; split.
    - injections; intros; inversion H2; subst.
      eapply bassn_eval_false; eauto.
    - exists 0; simpl; eauto; econstructor.
    - injections; clear IHProductive.
      admit.
    (*destruct (IHceval2 _ _ (eq_refl _)) as [? [n' ?] ]; eauto. *)
    - destruct (IHceval2 _ _ (eq_refl _)) as [? [n' ?] ].
      eexists (S n'); simpl; eauto.
  Qed. *)

  Definition LiftFunExSpecs (ESigma : total_map funExSpec)
    : total_map funSpec :=
    fun id => ({| pre := fun args => exists o, @preEx (ESigma id) o args;
                  post := fun v args => exists o, @postEx (ESigma id) v o args |}).

  Fixpoint Productive_ind'
           (Sigma : ExEnv) (P : forall (c : com) (st : state) (Q : Ensemble state),
                             Productive Sigma c st Q -> Prop)
           (f : forall st : state, P SKIP%imp st (Singleton state st) (Productive_Skip Sigma st))
           (f0 : forall (st : state) (x : String.string) (a : aexp),
               P (x ::= a)%imp st (Singleton (String.string -> nat) (x !-> aeval st a; st))
                 (Productive_Ass Sigma st x a))
           (f1 : forall (c1 c2 : com) (st : state) (Q Q' : Ensemble state)
                        (H : Productive Sigma c1 st Q)
                        (IH : P c1 st Q H)
                        (H' : forall st' : state, Q st' -> Productive Sigma c2 st' Q'),
               (forall (st' : state) (Q_st' : Q st'), P c2 st' Q' (H' _ Q_st')) ->
               P (c1;; c2)%imp st Q' (Productive_Seq Sigma c1 c2 st Q Q' H H'))
           (f2 : forall (st : state) (Q : Ensemble state) (b : bexp) (c1 c2 : com)
                        (H : beval st b = true)
                        (H' : Productive Sigma c1 st Q)
                        (IH : P c1 st Q H'),
               P (TEST b THEN c1 ELSE c2 FI)%imp st Q (Productive_IfTrue Sigma st Q b c1 c2 H H'))
           (f3 : forall (st : state) (b : bexp) (c1 c2 : com) (Q : Ensemble state)
                        (H : beval st b = false)
                        (H' : Productive Sigma c2 st Q)
                        (IH : P c2 st Q H'),
               P (TEST b THEN c1 ELSE c2 FI)%imp st Q (Productive_IfFalse Sigma st b c1 c2 Q H H'))
           (f4 : forall (b : bexp) (st : state) (c : com)
                        (H : beval st b = false),
               P (WHILE b DO c END)%imp st (Singleton state st) (Productive_WhileFalse Sigma b st c H))
           (f5 : forall (st : state) (b : bexp) (c : com) (Q Q' : Ensemble state)
                        (H : beval st b = true)
                        (H' : Productive Sigma c st Q)
                        (IH : P c st Q H')
                        (H'' : forall st' : state, Q st' -> Productive Sigma (WHILE b DO c END) st' Q')
                        (IH2 : forall (st' : state) (Q_st' : Q st'), P (WHILE b DO c END)%imp st' Q' (H'' _ Q_st')),
               P (WHILE b DO c END)%imp st Q' (Productive_WhileTrue Sigma st b c Q Q' H H' H''))
           (f6 : forall (st : state) (Q : Ensemble state) (args : list aexp) (x f6 : String.string) (fd : funDef)
                        (H : funDefs f6 = Some fd)
                        (H' : Productive Sigma (funBody fd) (build_total_map (funArgs fd) (aseval st args) 0) Q)
                        (IH : P (funBody fd) (build_total_map (funArgs fd) (aseval st args) 0) Q H'),
               P (x :::= f6 $ args)%imp st
                 (fun st' : state => exists st'' : state, Q st'' /\ st' = (x !-> aeval st'' (funRet fd); st))
                 (Productive_CallDef Sigma st Q args x f6 fd H H'))
           (f7 : forall (st : state) (args : list aexp) (x f7 : String.string) (n : nat) params
                        (H : funDefs f7 = None)
                        (H' : preEx (funExSpecs f7) params (aseval st args))
                        (H'' : postEx (funExSpecs f7) n params (aseval st args))
                        H3 H4,
               P (x :::= f7 $ args)%imp st
                 (fun st' : state => exists n0 : nat, postEx (funExSpecs f7) n0 params (aseval st args) /\ st' = (x !-> n0; st))
                 (Productive_CallSpec Sigma st args x f7 n params H H' H'' H3 H4))
           (f8 : forall (st : state) (c : com) (Q Q' : Ensemble state)
                        (H : Productive Sigma c st Q)
                        (IH : P c st Q H)
                        (H' : Included state Q Q'),
               P c st Q' (Productive_Weaken Sigma st c Q Q' H H'))
           (c : com) (s : state) (e : Ensemble state) (p : Productive Sigma c s e) {struct p} :
    P c s e p.
  Proof.
    destruct p; eauto.
    - eapply f1.
      eapply Productive_ind'; eauto.
      intros; eapply Productive_ind'; eauto.
    - eapply f2.
      eapply Productive_ind'; eauto.
    - eapply f3.
      eapply Productive_ind'; eauto.
    - eapply f5.
      eapply Productive_ind'; eauto.
      intros; eapply Productive_ind'; eauto.
    - eapply f6.
      eapply Productive_ind'; eauto.
    - eapply f8.
      eapply Productive_ind'; eauto.
  Defined.

  Theorem ehoare_proof_complete Sigma
          (Sigma_OK : Consistent_Env Sigma)
    : forall P c Q,

      {| funSigs := funSigs; funSpecs := funSpecs; funDefs := empty |} |= {[P]} c {[Q]}# ->
      funExSpecs |- {[P]} c {[Q]}#.
  Proof.
    intros; econstructor.
    - eapply hoare_proof_ewp.
    - intros.
      eapply (ewp_is_weakest _ _ _ _ H) in H0.
      eapply ewp_gen_is_ewp; eauto.
      unfold Consistent_Env; eauto.
    - eauto.
  Qed.


  (*Fixpoint loop_size {Sigma : Env} {st c st'} (exe : Sigma |- st =[ c ]=> st') : nat :=
    match exe with
    | E_WhileTrue _ _ _ _ _ _ _ _ exew => S (loop_size exew)
    | _ => 0
    end.

  Definition loop_measureR (Sigma : Env) b c Q n st : Prop :=
    (exists st' (exe : Sigma |- st =[ WHILE b DO c END ]=> st'),
        Q st' /\
        n = loop_size exe).

  Lemma ewp_loop_measureR (Sigma : Env) b c Q st
    : ewp Sigma (WHILE b DO c END) Q st <-> exists n, loop_measureR Sigma b c Q n st.
  Proof.
    unfold ewp, loop_measureR. split.
    - intros H. destruct H as [st' [exe HQ]].
      exists (loop_size exe). firstorder eauto.
    - firstorder.
  Qed.

  Lemma nonempty_smallest_ex (P : nat -> Prop) :
    (exists n, P n) ->
    exists n, P n /\ (forall n', P n' -> n <= n').
  Proof.
    intros [n H]. induction n using (well_founded_ind lt_wf).
    destruct (classic (exists y, y < n /\ P y)).
    - firstorder.
    - exists n. intuition. apply Nat.nlt_ge. eauto.
  Qed.

  Lemma loop_measureR_smallest_ex (Sigma : Env) b c Q st :
    (exists st' (exe : Sigma |- st =[ WHILE b DO c END ]=> st'), Q st') ->
    exists st' (exe : Sigma |- st =[ WHILE b DO c END ]=> st'),
      Q st' /\
      (forall st'' (exe' : Sigma |- st =[ WHILE b DO c END ]=> st''),
          Q st'' -> loop_size exe <= loop_size exe').
  Proof.
    intros.
    edestruct (nonempty_smallest_ex
                 (fun m => exists st' (exe : Sigma |- st =[ WHILE b DO c END ]=> st'),
                      Q st' /\ loop_size exe = m)).
    - firstorder eauto.
    - destruct_conjs. subst. repeat econstructor; eauto.
      Grab Existential Variables.
      auto.
  Qed. *)



  (* WIP on completeness proofs. *)

  (*Lemma ex_fully_permissive_funDef
    : forall Sigs Sigma P Q f x args,
      (forall funDefs,
          productive_Env {| funSigs := Sigs; funSpecs := Sigma; funDefs := funDefs |}
          -> {| funSigs := Sigs; funSpecs := Sigma; funDefs := funDefs |} |= {[P]} x :::= f $ args {[Q]}#) ->
      exists fd : funDef,
        ~ AppearsIn f (funBody fd) /\
        productive_funDef {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} (Sigma f) fd.
  Proof.
  Admitted. *)

  (* Pretty sure this is the completeness statement we want. *)
  (*Theorem ehoare_proof_complete Sigs Sigma : forall P c Q,
      (forall funDefs,
          productive_Env {| funSigs := Sigs; funSpecs := Sigma; funDefs := funDefs |}
          -> {| funSigs := Sigs; funSpecs := Sigma; funDefs := funDefs |} |= {[P]} c {[Q]}#)
      -> Sigma |- {[P]} c {[Q]}#.
  Proof.
    intros P c. revert dependent P.
    induction c; intros P Q HT.
    - (* SKIP *)
      specialize (HT _ (productive_empty _ _)).
      eapply EH_Consequence; eauto with hoare.
      intros. edestruct HT as [? [exe ?]]; eauto.
      inversion exe; subst. eauto.
    - (* ::= *)
      specialize (HT _ (productive_empty _ _)).
      eapply EH_Consequence; eauto with hoare.
      intros. edestruct HT as [? [exe ?]]; eauto.
      inversion exe; subst. eauto.
    - (* :::= *)
      eapply EH_Consequence; eauto with hoare.
      simpl. intros.
      generalize (HT _ (productive_empty _ _)) as HT'; intros.
      edestruct HT' as [? [exe ?]]; eauto; clear HT'.
      inversion exe; subst.
      + firstorder; eauto.
        destruct (ex_fully_permissive_funDef _ _ _ _ _ _ _ HT) as [? [? ?] ].
        assert (productive_Env {| funSigs := Sigs;
                                  funSpecs := Sigma;
                                  funDefs := update empty f x0 |}).
        { eapply productive_Env_Extend with
              (Sigma := {| funSigs := Sigs;
                           funSpecs := Sigma;
                           funDefs := empty |}); eauto using productive_empty.
          simpl; intros; discriminate. }
        generalize (HT _ H5) as HT'; intros.
        edestruct HT' as [? [exe' ?] ]; eauto.
        inversion exe'; subst.
        * simpl in H12; unfold update in H12; rewrite t_update_eq in H12; congruence.
        * apply update_inv in H14; intuition; subst.
          simpl in H6.
          eapply H6.
      + compute in H6; discriminate.
    - (* ;; *)
      (*apply EH_Seq with (@ewp {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} c2 Q); eauto. apply IHc1.
      intros.
      destruct (HT _ H _ H0) as [? [exe ?] ].
      inversion exe; subst. repeat econstructor; eauto.


-
      eapply IHc1.
    - (* IFB *)
      apply EH_If.
      + apply IHc1. intros. destruct_conjs.
        edestruct HT as [? [exe ?]]; eauto.
        inversion exe; subst; firstorder with hoare.
      + apply IHc2. intros. destruct_conjs.
        edestruct HT as [? [exe ?]]; eauto.
        inversion exe; subst; firstorder with hoare.
    - (* WHILE *)
      eapply EH_Consequence
        (* These two conjunction components are actually equivalent. See ewp_loop_measureR *)
        with (P':=fun st => ewp _ (WHILE b DO c END) Q st /\ exists n, loop_measureR _ b c Q n st).
      + apply EH_While.
        intros. apply IHc. intros st [Hwp [Hb Hm]].
        edestruct (@loop_measureR_smallest_ex {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |}) as [st' [exe [HQ H]]]; eauto.
        remember (WHILE b DO c END)%imp eqn:Heq.
        destruct exe; inversion Heq; subst; clear Heq. exfalso. congruence.
        unfold loop_measureR in *. destruct_conjs. subst. simpl in H.
        exists st'. firstorder eauto.
        eexists exe1; firstorder eauto.
        eexists _; split.
        eexists _, exe2; firstorder eauto.
        subst; eauto.
      + setoid_rewrite <- ewp_loop_measureR. firstorder eauto.
      + simpl. intros ? [H ?]. destruct H as [? [exe ?]].
        inversion exe; subst; eauto. exfalso. eauto. *)
  Admitted. *)

  Inductive Productive_Bound {Sigma : ExEnv}
    : forall {st c Q}
              (prod : Productive Sigma c st Q), nat -> Prop :=
  | Bound_Skip :
      forall st n, Productive_Bound (Productive_Skip Sigma st) n
  | Bound_Ass :
      forall st x a n, Productive_Bound (Productive_Ass Sigma st x a) n
  | Bound_Seq : forall c1 c2 st Q Q' H H' n,
      Productive_Bound (Productive_Seq Sigma c1 c2 st Q Q' H H') n
  | Bound_IfTrue : forall st Q b c1 c2 H H' n,
      Productive_Bound (Productive_IfTrue Sigma st Q b c1 c2 H H') n
  | Bound_IfFalse : forall st Q b c1 c2 H H' n,
      Productive_Bound (Productive_IfFalse Sigma st Q b c1 c2 H H') n
  | Bound_WhileFalse : forall b st c H n,
      Productive_Bound (Productive_WhileFalse Sigma b st c H) n
  | Bound_WhileTrue : forall st b c (Q Q' : state -> Prop) beval_true prod_c prod_loop n,
      (forall st' (Q_st' : Q st'), Productive_Bound (prod_loop _ Q_st') n) ->
      Productive_Bound (Productive_WhileTrue Sigma st b c Q Q' beval_true prod_c prod_loop) (S n)
  | Bound_CallDef :
      forall st Q args x f fd H H' n,
        Productive_Bound (Productive_CallDef Sigma st Q args x f fd H H') n
  | Bound_CallSpec : forall st args x f n H H' H'' H3 H4 H5 n',
      Productive_Bound (Productive_CallSpec Sigma st args x f n H H' H'' H3 H4 H5) n'
  | Bound_Weaken : forall st c Q Q' H H' n,
      Productive_Bound H n ->
      Productive_Bound (Productive_Weaken Sigma st c Q Q' H H') n.

  Definition ewp' (Sigma : ExEnv) (c:com) (Q:Assertion) : Assertion :=
    fun st => Productive Sigma c st Q.

  Definition loop_measureR' (Sigma : ExEnv) b c Q n st : Prop :=
    forall (prod : Productive Sigma (WHILE b DO c END) st Q),
      Productive_Bound prod n.

  Lemma ewp'_loop_measureR' (Sigma : ExEnv) b c Q st
    : ewp' Sigma (WHILE b DO c END) Q st -> exists n, loop_measureR' Sigma b c Q n st.
  Proof.
    unfold ewp', loop_measureR'; intros.
    remember (CWhile b c).
    revert dependent b; revert c.
    pattern c0, st, Q, H.
    eapply Productive_ind'; intros;
    try solve [match goal with
                   |- context [Productive _ ?c _ _] =>
                   exists 0; intros;
                   remember c; destruct prod; try discriminate; injections;
                   try congruence; try econstructor
                 end].
    - injections.
      match goal with
        |- context [Productive _ ?c _ ?st'] =>
                   exists 0; intros;
                   remember c; remember st'
                 end.
      revert Heqc.
      revert dependent b0; revert c1; clear Heqe.
      pattern c, st0, e, prod.
      eapply Productive_ind'; intros; try discriminate; injections;
        try congruence; econstructor; eauto.
    - injections.
      admit.
    -

      (*with (P := (fun (c : com) (s : state) (e0 : Ensemble state) (p : Productive Sigma c s e0) =>
   e0 = Singleton state s ->
   forall (c1 : com) (b : bexp), beval s b = false -> c = (WHILE b DO c1 END)%imp -> Productive_Bound p 0))
      remember ((Singleton state st))
      econstructor.
      econstructor.

      subst; injections.

      injections; exists 0.
      intros.
      2: { eexists 0; intros.


    match goal with
      |- context [Productive _ ?c _ _] =>
      exists 0; intros;
        remember c
    end.
    induction prod. try discriminate; injections;
          try congruence; try econstructor



    Focus 2.
    destruct IHProductive.

    match goal with
      |- context [Productive _ ?c _ _] =>
      exists 0; intros;
        remember c; destruct prod; try discriminate; injections;
          try congruence; try econstructor
    end.
    eapply Bound_CallSpec.

    econstructor.
      exists 0; intros;
      remember CSkip; destruct prod; try discriminate; econstructor.
    - exists 0; intros;
      remember CSkip; destruct prod; try discriminate; econstructor.
    - intros H.
      eapply productive_com_produces in H.
      destruct H as [st' [exe HQ]].
      exists (loop_size exe). firstorder eauto.
    - firstorder.
  Qed. *)
  Admitted.
  (*Lemma loop_measureR_smallest_ex (Sigma : Env) b c Q st :
    (exists st' (exe : Sigma |- st =[ WHILE b DO c END ]=> st'), Q st') ->
    exists st' (exe : Sigma |- st =[ WHILE b DO c END ]=> st'),
      Q st' /\
      (forall st'' (exe' : Sigma |- st =[ WHILE b DO c END ]=> st''),
          Q st'' -> loop_size exe <= loop_size exe').
  Proof.
    intros.
    edestruct (nonempty_smallest_ex
                 (fun m => exists st' (exe : Sigma |- st =[ WHILE b DO c END ]=> st'),
                      Q st' /\ loop_size exe = m)).
    - firstorder eauto.
    - destruct_conjs. subst. repeat econstructor; eauto.
      Grab Existential Variables.
      auto.
  Qed. *)

  (*Fixpoint productive_bound {Sigma : Env} {st c Q}
           (prod : Productive Sigma c st Q) {struct prod} : Prop :=
    match prod return Prop with
    | Productive_WhileTrue _ _ _ Q' _ _ _ _ exew => True
    | _ => True
    end.

  (Sigma : Env) b c Q n st : Prop :=
    (exists st' (exe : Sigma |- st =[ WHILE b DO c END ]=> st'),
        Q st' /\
        n = loop_size exe).

  Lemma nonempty_smallest_ex (P : nat -> Prop) :
    (exists n, P n) ->
    exists n, P n /\ (forall n', P n' -> n <= n').
  Proof.
    intros [n H]. induction n using (well_founded_ind lt_wf).
    destruct (classic (exists y, y < n /\ P y)).
    - firstorder.
    - exists n. intuition. apply Nat.nlt_ge. eauto.
  Qed.

  Lemma loop_measureR_smallest_ex (Sigma : Env) b c Q st :
    (exists st' (exe : Sigma |- st =[ WHILE b DO c END ]=> st'), Q st') ->
    exists st' (exe : Sigma |- st =[ WHILE b DO c END ]=> st'),
      Q st' /\
      (forall st'' (exe' : Sigma |- st =[ WHILE b DO c END ]=> st''),
          Q st'' -> loop_size exe <= loop_size exe').
  Proof.
    intros.
    edestruct (nonempty_smallest_ex
                 (fun m => exists st' (exe : Sigma |- st =[ WHILE b DO c END ]=> st'),
                      Q st' /\ loop_size exe = m)).
    - firstorder eauto.
    - destruct_conjs. subst. repeat econstructor; eauto.
      Grab Existential Variables.
      auto.
  Qed. *)

  Lemma ewp'_is_precondition {Sigma : ExEnv}: forall c Q,
      forall st,
        ewp' Sigma c Q st ->
        Productive Sigma c st Q.
  Proof.
    firstorder.
  Qed.

  Lemma ewp'_is_weakest (Sigma : ExEnv) : forall c Q (P : Assertion),
      (forall st, P st -> Productive Sigma c st Q) ->
      P ->> ewp' Sigma c Q.
  Proof.
    firstorder.
  Qed.

  (* The Productive predicate and the existential hoare rules should
  be equivalent. This proof will let us prove the soundness of vc
  generation with respect to the hoare rules. *)
  Theorem produces_ehoare_proof {Sigma : ExEnv}
    : forall c (P Q : Assertion),
      productive_Env Sigma ->
      (forall st,
        P st ->
        Productive {| AllEnv := {| funSigs := @funSigs AllEnv;
                                   funSpecs := @funSpecs AllEnv;
                                   funDefs := empty |};
                      funExSpecs := funExSpecs |}
                      c st Q) ->
        funExSpecs |- {[P]} c {[Q]}#.
  Proof.
    induction c; intros.
    - eapply EH_Consequence; eauto with hoare; intros.
      eapply H0 in H1; remember CSkip in H1; clear H0.
      induction H1; try congruence; injections.
      + econstructor.
      + eapply H0; apply IHProductive; eauto.
    - eapply EH_Consequence; eauto with hoare; intros.
      eapply H0 in H1; remember (CAss x a) in H1; clear H0.
      induction H1; try congruence; injections.
      + econstructor.
      + eapply H0; apply IHProductive; eauto.
    - admit.
      (*eapply EH_Consequence; eauto with hoare; intros.
      eapply H0 in H1; remember (CCall x f args) in H1; clear H0.
      induction H1; try congruence; injections.
      + simpl in H0; discriminate.
      + firstorder eauto.
      + firstorder eauto. *)
    - eapply EH_Seq with (fun st => Productive {|AllEnv := {| funSigs := funSigs; funSpecs := funSpecs; funDefs := empty |} |} c2 st Q); eauto.
      + apply IHc1; eauto.
        intros.
        eapply H0 in H1; remember (CSeq c1 c2) in H1; clear H0.
        induction H1; try congruence; injections.
        * eapply Productive_Weaken; eauto with hoare; intros.
        * eapply Productive_Weaken; eauto with hoare; intros.
          unfold Included, In; intros; eauto using Productive_Weaken.
    - apply EH_If.
      + apply IHc1; intuition eauto.
        eapply H0 in H2; remember (CIf b c1 c2) in H2; clear H0.
        induction H2; try congruence; injections.
        eapply Productive_Weaken; eauto with hoare; intros.
      + apply IHc2; intuition eauto.
        eapply H0 in H2; remember (CIf b c1 c2) in H2; clear H0.
        induction H2; try congruence; injections.
        eapply Productive_Weaken; eauto with hoare; intros.
    - eapply EH_Consequence with (P' := fun st => ewp' {|AllEnv := {| funSigs := funSigs; funSpecs := funSpecs; funDefs := empty |} |} (WHILE b DO c END) Q st /\ (exists n : nat, loop_measureR' {|AllEnv := {| funSigs := funSigs; funSpecs := funSpecs; funDefs := empty |} |} b c Q n st)).
      + eapply EH_While.
        * intros; eapply IHc; eauto; intros st [Hwp [Hb Hm]].
          unfold loop_measureR', ewp' in *.
          remember (CWhile b c) in Hwp.
          clear H0.
          induction Hwp; try congruence; injections.
          2 : {
          (*eapply Productive_Weaken.
          eapply IHHwp; eauto.
          intros.
          simpl in *.
          Set Printing Implicit.
          eapply Hm; eapply H0; eauto.
          unfold Included, In; intros; intuition eauto using Productive_Weaken.
          destruct H3 as [? [? ?] ]; eexists; intuition eauto.
          eapply H1. *)
          admit.
          }
          admit.
          admit.
      + intros; eapply H0 in H1.
        unfold ewp'; split; eauto.
        unfold loop_measureR'.
        admit.
        (*eapply ewp'_loop_measureR'; eauto. *)
      + simpl; intros st [? ?].
        remember (CWhile b c) in H1; clear H0.
        induction H1; try congruence; injections.
        * econstructor.
        * eapply H0; apply IHProductive; eauto.
  Admitted. *)

End EHoare.

Notation "Sigma |= {[ P ]}  c  {[ Q ]}#" :=
  (ehoare_triple Sigma P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Notation "Sigma |- {[ P ]}  c  {[ Q ]}#" :=
  (ehoare_proof Sigma P c Q) (at level 90, c at next level)
  : hoare_spec_scope.
