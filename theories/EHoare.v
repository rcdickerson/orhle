Require Import
        Coq.Arith.Arith
        Coq.micromega.Psatz
        Coq.Sets.Ensembles
        Coq.Logic.Classical
        Coq.Program.Tactics.

Require Import Maps Imp HoareCommon.

Section EHoare.

  Reserved Notation "Sigma |- {[ P ]}  c  {[ Q ]}#"
           (at level 40, c at next level).

  Inductive ehoare_proof (Sigma : total_map funSpec)
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

  | EH_Spec : forall Q y f xs,
      Sigma |- {[fun st =>
            (Sigma f).(pre) (aseval st xs) /\
            exists v, (Sigma f).(post) v (aseval st xs) /\
                      forall v, (Sigma f).(post) v (aseval st xs) ->
                 Q[y |-> v] st]} y :::= f $ xs {[Q]}#

  where "Sigma |- {[ P ]}  c  {[ Q ]}#" := (ehoare_proof Sigma P c Q) : hoare_spec_scope.

  Definition ehoare_triple
             (Sigma : Env)
             (P : Assertion)
             (c : com)
             (Q : Assertion) : Prop :=
    forall st,
      P st ->
      exists st' (exe : Sigma |- st =[ c ]=> st'), Q st'.

  Notation "Sigma |= {[ P ]}  c  {[ Q ]}#" :=
    (ehoare_triple Sigma P c Q) (at level 90, c at next level)
    : hoare_spec_scope.

  Hint Resolve bassn_eval_true bassn_eval_false : hoare.
  Hint Constructors ehoare_proof : hoare.
  Hint Constructors ceval.

  Lemma ehoare_while (Sigma : Env)  : forall P M b c,
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
  Qed.

  Theorem ehoare_proof_sound Sigs Sigma : forall P c Q,
      Sigma |- {[P]} c {[Q]}# ->
      {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} |= {[P]} c {[Q]}#.
  Proof.
    unfold ehoare_triple.
    intros ? ? ? pf. induction pf; intros st HP.
    - (* SKIP *)
      eauto.
    - (* ::= *)
      repeat econstructor. eauto.
    - (* ;; *)
      firstorder eauto.
    - (* TEST *)
      destruct (beval st b) eqn:?.
      + edestruct IHpf1; firstorder eauto.
      + edestruct IHpf2; firstorder eauto. firstorder with hoare.
    - (* WHILE *)
      eapply ehoare_while; eauto.
      unfold ehoare_triple; intros; eapply H0; eauto.
    - (* Conseq *)
      firstorder eauto.
    - (* :::= *)
      destruct_conjs.
      repeat econstructor; eauto.
      eapply H2; eauto.
  Qed.

  Definition ewp (Sigma : Env) (c:com) (Q:Assertion) : Assertion :=
    fun st => exists st' (exe : Sigma |- st =[ c ]=> st'), Q st'.

  Lemma ewp_is_precondition {Sigma : Env}: forall c Q,
      Sigma |= {[ewp Sigma c Q]} c {[Q]}#.
  Proof.
    firstorder.
  Qed.

  Lemma ewp_is_weakest (Sigma : Env) : forall c Q P,
      Sigma |= {[P]} c {[Q]}# -> P ->> ewp Sigma c Q.
  Proof.
    firstorder.
  Qed.

  Hint Resolve ewp_is_precondition ewp_is_weakest : hoare.
  Hint Unfold ehoare_triple ewp.

  Fixpoint loop_size {Sigma : Env} {st c st'} (exe : Sigma |- st =[ c ]=> st') : nat :=
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
  Qed.

  (* Pretty sure this is the completeness statement we want. *)
  Theorem ehoare_proof_complete Sigs Sigma : forall P c Q,
      (forall funDefs,
          productive_Env {| funSigs := Sigs; funSpecs := Sigma; funDefs := funDefs |}
          -> {| funSigs := Sigs; funSpecs := Sigma; funDefs := funDefs |} |= {[P]} c {[Q]}#)
      -> Sigma |- {[P]} c {[Q]}#.
  Proof.
    unfold ehoare_triple.
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
      admit.
      (*inversion exe; subst.
      + firstorder; eauto.
        eexists _; split; eauto.
        intros.
        assert (productive_Env {| funSigs := Sigs;
                                  funSpecs := Sigma;
                                  funDefs := update empty f {| funArgs := nil;
                                                               funBody := SKIP;
                                                               funRet := v |} |}).
        { unfold productive_Env; simpl; intros.
          eapply update_inv in H2; intuition; subst.
          - unfold productive_funDef; intros.
            simpl.
            eassert (Productive
                                 {|
                                 funSigs := Sigs;
                                 funSpecs := Sigma;
                                 funDefs := f0 |-> {| funArgs := nil; funBody := SKIP; funRet := v |} |} SKIP
                                 (build_total_map nil args0 0) _).
            econstructor.
            simpl; eexists _, H3; eauto.
            intros.
      admit.
          - compute in H5; discriminate.
        } 
        admit.
      + *)
    - (* ;; *)
      apply EH_Seq with (@ewp {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} c2 Q); eauto. apply IHc1.
      intros.
  (* edestruct HT as [? [exe ?]]; eauto.
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
  Admitted.

  Hint Constructors Productive : hoare.

  Theorem ehoare_proof_produces {Sigma : Env}
    : forall (P Q : Assertion) c,
      productive_Env Sigma ->
      funSpecs |- {[P]} c {[Q]}# ->
      forall st,
        P st ->
        Productive {| funSigs := @funSigs Sigma;
                      funSpecs := @funSpecs Sigma;
                      funDefs := empty |} c st Q.
  Proof.
    induction 2; intros; eauto.
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
    - destruct H0 as [? [n [? ?] ] ].
      eapply Productive_Weaken; eauto.
      + eapply Productive_CallSpec; firstorder eauto.
      + unfold Included, In; intros.
        destruct H3 as [n' [? ?] ]; subst.
        eapply H2; eauto.
  Qed.

  (* The Productive predicate and the existential hoare rules should
  be equivalent. This proof will let us prove the soundness of vc
  generation with respect to the hoare rules. *)

  Theorem produces_ehoare_proof {Sigma : Env}
    : forall (P Q : Assertion) c,
      productive_Env Sigma ->
      (forall st,
        P st ->
        Productive {| funSigs := @funSigs Sigma;
                      funSpecs := @funSpecs Sigma;
                      funDefs := empty |} c st Q) ->
        funSpecs |- {[P]} c {[Q]}#.
  Proof.
    intros; eapply ehoare_proof_complete.
    intros.
    unfold ehoare_triple; intros.
    eapply productive_com_produces.
    eapply productive_Env_produces; eauto.
  Qed.

  Theorem ehoare_proof_link {Sigma : Env}
    : forall (P Q : Assertion) c,
      productive_Env Sigma ->
      funSpecs |- {[P]} c {[Q]}# ->
      Sigma |= {[P]} c {[Q]}#.
  Proof.
    intros; intros ? ?.
    eapply productive_com_produces.
    eapply productive_Env_produces; eauto.
    eapply ehoare_proof_produces; eauto.
  Qed.

End EHoare.

Notation "Sigma |= {[ P ]}  c  {[ Q ]}#" :=
  (ehoare_triple Sigma P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Notation "Sigma |- {[ P ]}  c  {[ Q ]}#" :=
  (ehoare_proof Sigma P c Q) (at level 90, c at next level)
  : hoare_spec_scope.
