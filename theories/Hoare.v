(** * Hoare Logic *)

(* Adapted from the Software Foundations series:
   https://softwarefoundations.cis.upenn.edu/ *)

Require Import Coq.Program.Tactics
        Coq.Lists.List.

Require Import Maps Imp HoareCommon.

(* ################################################################# *)
(** * Hoare Triples *)

Section Hoare.

  Reserved Notation "Sigma |- {{ P }}  c  {{ Q }}"
           (at level 40, c at next level).

  Inductive hoare_proof (Sigma : total_map funSpec) : Assertion -> com -> Assertion -> Prop :=
  | H_Skip : forall P,
      Sigma |- {{ P }} SKIP {{P}}
  | H_Asgn : forall Q V a,
      Sigma |- {{Q[V |-> a]}} V ::= a {{Q}}
  | H_Seq  : forall P c Q d R,
      Sigma|- {{P}} c {{Q}} ->
      Sigma |- {{Q}} d {{R}} ->
      Sigma |- {{P}} c;;d {{R}}
  | H_If : forall P Q b c1 c2,
      Sigma |- {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
      Sigma |- {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
      Sigma |- {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}
  | H_While : forall P b c,
      Sigma |- {{fun st => P st /\ bassn b st}} c {{P}} ->
      Sigma |- {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}
  | H_Consequence  : forall (P Q P' Q' : Assertion) c,
      Sigma |- {{P'}} c {{Q'}} ->
      (forall st, P st -> P' st) ->
      (forall st, Q' st -> Q st) ->
      Sigma |- {{P}} c {{Q}}

  | H_Call : forall Q y f xs,
      Sigma |- {{fun st =>
            (Sigma f).(pre) (aseval st xs) ->
            forall v, (Sigma f).(post) v (aseval st xs) ->
                 Q[y |-> v] st}} y :::= f $ xs {{Q}}


where "Sigma |- {{ P }}  c  {{ Q }}" := (hoare_proof Sigma P c Q) : hoare_spec_scope.

  Definition hoare_triple
             (Sigma : Env)
             (P : Assertion)
             (c : com)
             (Q : Assertion) : Prop :=
    forall st st',
      Sigma |- st =[ c ]=> st'  ->
      P st  ->
      Q st'.

  Notation "Sigma '|=' {{ P }}  c  {{ Q }}" :=
    (hoare_triple Sigma P c Q) (at level 40, c at next level)
    : hoare_spec_scope.

  Hint Resolve bassn_eval_true bassn_eval_false : hoare.
  Hint Constructors hoare_proof : hoare.
  Hint Unfold hoare_triple.
  Hint Constructors ceval.

  Lemma hoare_while (Sigma : Env) : forall P b c,
      Sigma |= {{fun st => P st /\ bassn b st}} c {{P}} ->
      Sigma |= {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
  Proof.
    unfold hoare_triple.
    intros ? ? ? ? ? ? HE ?. remember (WHILE b DO c END)%imp eqn:Heq.
    induction HE; try inversion Heq; subst.
    - firstorder with hoare.
    - eauto.
  Qed.

  Theorem hoare_proof_sound Sigs Sigma : forall P c Q,
      Sigma |- {{P}} c {{Q}} ->
       {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} |= {{P}} c {{Q}}.
  Proof.
  intros ? ? ? pf. induction pf; intros st st' HE HP.
  - (* SKIP *)
    inversion HE; subst. eauto.
  - (* ::= *)
    inversion HE; subst. eauto.
  - (* ;; *)
    inversion HE; subst. eauto.
  - (* TEST *)
    inversion HE; subst; firstorder with hoare.
  - (* WHILE *)
    eapply hoare_while; eauto.
  - (* Conseq *)
    eauto.
  - (* :::= *)
    inversion HE; subst; firstorder.
    simpl in H4; rewrite apply_empty in H4; discriminate.
  Qed.


  (* The weakest precondition for an assertion [Q] and command [c] is
     the set of initial states from which [c] always either fails to
     terminate, or ends in a final state satisfying [Q]. *)
  Definition wp (Sigma : Env)
             (c : com)
             (Q : Assertion) : Assertion :=
    fun s => forall s', Sigma |- s =[ c ]=> s' -> Q s'.

  Lemma wp_is_precondition (Sigma : Env): forall c Q,
      Sigma |= {{wp Sigma c Q}} c {{Q}}.
  Proof.
    firstorder.
  Qed.

  Lemma wp_is_weakest (Sigma : Env) : forall c Q P',
      Sigma |= {{P'}} c {{Q}} -> forall st, P' st -> wp Sigma c Q st.
  Proof.
    firstorder.
  Qed.

  (* Want: the set of initial states that cause the loop to either:
     - end in a state satisfying the post condition or
     - continue looping *)

  Definition FClosed {A : Type} (F : (A -> Prop) -> A -> Prop)
             (S : A -> Prop) : Prop :=
    forall a, F S a -> S a.

  Definition LFP {A : Type} (F : (A -> Prop) -> A -> Prop) : A -> Prop :=
    fun a => forall S, FClosed F S -> S a.

  Definition Monotonic_F {A : Type} (F : (A -> Prop) -> A -> Prop) : Prop :=
    forall (S S' : A -> Prop),
      (forall a, S a -> S' a) -> forall a, F S a -> F S' a.
  
  Lemma LFP_is_FixedPoint {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F)
             (a : A),
      F (LFP F) a <-> LFP F a.
  Proof.
    split; intros.
    - unfold LFP, FClosed; intros.
      eapply H0.
      eapply F_Monotone.
      2: eapply H.
      firstorder eauto.
    - unfold LFP, FClosed in H.
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

  Lemma Ind {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop) (Ind : A -> Prop),
      FClosed F Ind -> forall a, LFP F a -> Ind a.
  Proof.
    unfold LFP, FClosed; intros; eapply H0; eauto.
  Qed.

  Definition FConsistent {A : Type} (F : (A -> Prop) -> A -> Prop)
             (S : A -> Prop) : Prop :=
    forall a, S a -> F S a.
  
  Definition GFP {A : Type} (F : (A -> Prop) -> A -> Prop) : A -> Prop :=
    fun a => exists S, FConsistent F S /\ S a.

  Lemma CoInd {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop) (Ind : A -> Prop),
      FConsistent F Ind -> forall a, Ind a -> GFP F a.
  Proof.
    unfold GFP, FConsistent; intros; eauto.
  Qed.
  
  Lemma GFP_is_FClosed {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F),
      FClosed F (GFP F).
  Proof.
    intros ? ?.
    exists (F (GFP F)); intros; eauto.
    split; intros; eauto.
    unfold FConsistent.
    intros.
    eapply F_Monotone.
    2: eauto.
    intros.
    destruct H1 as [S [? ?] ].
    unfold FConsistent in H1.
    eapply F_Monotone.
    2: eapply H1; eauto.
    intros.
    unfold GFP; eauto.
  Qed.

  Lemma GFP_is_FConsistent {A : Type}
    : forall (F : (A -> Prop) -> A -> Prop)
             (F_Monotone : Monotonic_F F),
      FConsistent F (GFP F).
  Proof.
    intros ? ? ? ?.
    destruct H as [S [? ?] ].
    apply H in H0.
    eapply F_Monotone.
    2: eapply H0.
    intros.
    eexists; eauto.
  Qed.

  Fixpoint gamma
           (Q : Assertion)
           (c : com)
           (b : bexp)
           (WP : Assertion -> Assertion)
           (n : nat) : Assertion :=
    match n with
    | 0 => fun st => ~ bassn b st /\ Q st
    | S n' => fun st => bassn b st /\ WP (gamma Q c b WP n') st
    end.

  Fixpoint wp_gen
           (funSpecs : total_map funSpec)
           (c : com)
           (Q : Assertion) {struct c} : Assertion :=
    match c with
    | CSkip => Q
    | CAss x a => Q [x |-> a]
    | CCall x f args =>
      fun st => (forall v,
                    (funSpecs f).(pre) (aseval st args) /\
                    (funSpecs f).(post) v (aseval st args) ->
                           Q[x |-> v] st)
    | CSeq c1 c2 => wp_gen funSpecs c1 (wp_gen funSpecs c2 Q)
    | CIf b c1 c2 => fun st => (bassn b st -> wp_gen funSpecs c1 Q st)
                               /\ (~ bassn b st -> wp_gen funSpecs c2 Q st)
    | CWhile b c => fun st =>
                      exists n, gamma Q c b
                                      (fun Q st => (bassn b st -> wp_gen funSpecs c Q st)
                                                   /\ (~ bassn b st -> Q st))
                                      n st
    end.

  Definition gamma'
           (Q : Assertion)
           (c : com)
           (b : bexp)
           (WP : Assertion -> Assertion)
    : Assertion :=
    @GFP state (fun (G : _ -> _) (st : state) => (~ bassn b st /\ Q st)
                     \/ (bassn b st /\ WP G st)).

  Fixpoint wp_gen'
           (funSpecs : total_map funSpec)
           (c : com)
           (Q : Assertion) {struct c} : Assertion :=
    match c with
    | CSkip => Q
    | CAss x a => Q [x |-> a]
    | CCall x f args =>
      fun st => (forall v,
                    (funSpecs f).(pre) (aseval st args) /\
                    (funSpecs f).(post) v (aseval st args) ->
                           Q[x |-> v] st)
    | CSeq c1 c2 => wp_gen' funSpecs c1 (wp_gen' funSpecs c2 Q)
    | CIf b c1 c2 => fun st => (bassn b st -> wp_gen' funSpecs c1 Q st)
                               /\ (~ bassn b st -> wp_gen' funSpecs c2 Q st)
    | CWhile b c => gamma' Q c b
                           (fun Q st => (bassn b st -> wp_gen' funSpecs c Q st)
                                        /\ (~ bassn b st -> Q st))
    end.

  Lemma wp_gen'_is_monotone
    Sigma
    : forall (c : com) (a : state) (S S' : state -> Prop),
      (forall a0 : state, S a0 -> S' a0) -> wp_gen' Sigma c S a -> wp_gen' Sigma c S' a.
  Proof.
    induction c; simpl; intros; eauto.
    - unfold assn_sub; eauto.
    - unfold assn_sub in *; eauto.
    - intuition; eauto.
    - unfold gamma', GFP, FConsistent in *.
      destruct H0 as [S'' [? ?] ].
      eexists S''; intuition.
      eapply H0 in H2; intuition.
  Qed.

  Lemma wp_gen_is_wp Sigs Sigma
    : forall c Q sigma',
      wp {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} c Q sigma'
      -> wp_gen' Sigma c Q sigma'.
  Proof.
    induction c; simpl; intros; eauto.
    - eapply H; eauto.
    - eapply H; firstorder eauto.
    - unfold wp in *; intros; firstorder eauto.
    - firstorder eauto.
        unfold wp in *; eapply IHc2; intros.
        eapply H; eapply E_IfFalse; eauto.
        eapply bassn_eval_false; eauto.
    - unfold gamma'.
        eapply CoInd.
        unfold FConsistent.
        2: {
          instantiate (1 := fun st => wp {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} (WHILE b DO c END) Q st /\ _ st Q).
          simpl; split.
          apply H.
          exact (fun _ : state => IHc).
        }
        simpl; intros.
        destruct H0.
        specialize (H1 a).
        unfold bassn.
        destruct (beval a b) eqn: ?.
        2: left; eauto.
        right; intuition.
        eapply IHc.
        split.
      + intros ? ?.
        apply H0.
        econstructor; eauto.
      + eauto.
  Qed.

  Theorem hoare_proof_wp Sigma : forall c Q,
      Sigma |- {{wp_gen' Sigma c Q}} c {{Q}}.
  Proof.
    induction c; simpl; intros; try solve [econstructor].
    - eapply H_Consequence with (Q := Q); simpl; eauto.
      + apply H_Call.
      + simpl; intros; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
      + econstructor; firstorder eauto.
      + econstructor; firstorder eauto.
    - econstructor.
      econstructor.
      2: intros; eapply H.
      2: { simpl; intros.
           destruct H as [? ?].
           eapply GFP_is_FConsistent in H; intuition.
           unfold Monotonic_F.
           intros. intuition.
           right.
           intuition.
           eauto using wp_gen'_is_monotone.
      }
      econstructor.
      apply IHc.
      2: intros; eapply H.
      intros.
      intuition.
      eapply GFP_is_FConsistent in H0; intuition.
      unfold Monotonic_F.
      intros. intuition.
      right.
      intuition.
      eauto using wp_gen'_is_monotone.
  Qed.

  Theorem hoare_proof_complete' Sigs Sigma : forall P c Q,
      {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} |= {{P}} c {{Q}} ->
      Sigma |- {{P}} c {{Q}}.
  Proof.
    intros.
    econstructor.
    - eapply hoare_proof_wp.
    - intros.
      eapply (wp_is_weakest _ _ _ _ H) in H0.
      eapply wp_gen_is_wp in H0; eauto.
    - eauto.
  Qed.

  Print Assumptions hoare_proof_complete'.

  (*Lemma wp_gen_is_wp Sigs Sigma
    : forall c Q sigma',
      wp {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} c Q sigma'
      <-> wp_gen Sigma c Q sigma'.
  Proof.
    split; revert Q sigma'.
    - induction c; simpl; intros; eauto.
      + eapply H; eauto.
      + eapply H; firstorder eauto.
      + unfold wp in *; intros; firstorder eauto.
      + firstorder eauto.
        unfold wp in *; eapply IHc2; intros.
        eapply H; eapply E_IfFalse; eauto.
        eapply bassn_eval_false; eauto.
      + admit.
    - induction c; simpl; unfold wp; intros; eauto.
      + inversion H0; subst; eauto.
      + inversion H0; subst; eauto.
      + inversion H0; subst; firstorder eauto.
        simpl in H7; discriminate.
      + inversion H0; subst; eauto.
        eapply IHc1 in H; firstorder eauto.
      + inversion H0; subst; firstorder eauto.
        eapply IHc2; eauto.
        eapply H1.
        eapply bassn_eval_false; eauto.
      + destruct H as [n ?].
        eapply (unroll_loop_eqv_while _ n) in H0.
        revert Q sigma' s' b c IHc H H0; induction n; simpl; intros.
        * destruct H; inversion H0; subst; eauto.
          eapply bassn_eval_false in H; congruence.
        * destruct H as [? [? H2] ]; clear H2.
          inversion H0; subst; clear H0.
          2: eapply bassn_eval_false in H7; congruence.
          inversion H8; subst; clear H8.
          eapply H1 in H; clear H1.
          eapply IHc in H.
          eapply H in H3.
          eapply IHn in H3; eauto.
  Admitted.      *)  

  
  Hint Resolve wp_is_precondition wp_is_weakest : hoare.
  Hint Unfold wp.

  Theorem hoare_proof_complete Sigs Sigma : forall P c Q,
      {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} |= {{P}} c {{Q}} ->
      Sigma |- {{P}} c {{Q}}.
  Proof.
    unfold hoare_triple.
    intros P c. revert dependent P.
    induction c; intros P Q HT.
    - (* SKIP *)
      eapply H_Consequence; eauto with hoare.
    - (* ::= *)
      eapply H_Consequence; eauto with hoare.
      intros; eapply HT; eauto.
    - (* :::= *)
      eapply H_Consequence; eauto with hoare.
      simpl. intros. eapply HT; eauto.
    - (* ;; *)
      apply H_Seq with (@wp {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} c2 Q); firstorder eauto.
    - (* IFB *)
      apply H_If.
      + firstorder eauto.
      + apply IHc2. firstorder with hoare.
    - (* WHILE *)
      eapply H_Consequence with (P':= @wp {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} (WHILE b DO c END) Q).
      + constructor. firstorder eauto.
      + eauto.
      + firstorder with hoare.
  Qed.

  Theorem hoare_proof_link {Sigma : Env}
    : forall (P Q : Assertion) c,
      safe_Env Sigma ->
      (forall st, P st -> @Safe {| funSigs := @funSigs Sigma;
                                   funSpecs := @funSpecs Sigma;
                                   funDefs := empty |} c st) ->
      funSpecs |- {{P}} c {{Q}} ->
      Sigma |= {{P}} c {{Q}}.
  Proof.
    intros.
    pose proof (hoare_proof_sound (@funSigs Sigma) _ _ _ _ H1).
    eauto using safe_Env_refine, hoare_proof_sound.
  Qed.

  Lemma safe_funDef_hoare :
    forall (Sigma : Env) spec args body ret,
      safe_Env Sigma ->
      (forall args0,
          pre spec args0 ->
          Safe {| funSigs := funSigs; funSpecs := funSpecs; funDefs := empty |} body
               (build_total_map (funArgs {| funArgs := args; funBody := body; funRet := ret |}) args0 0)) ->
      (forall orig_args,
          funSpecs |- {{ fun st => Forall2 (fun orig arg => st arg = orig)
                                        orig_args
                                        args -> pre spec orig_args }}
                     body
                     {{ fun st => post spec (aeval st ret) orig_args }})
      -> safe_funDef Sigma spec {| funArgs := args; funBody := body; funRet := ret |}.
  Proof.
    intros.
    unfold safe_funDef in *; intros.
    specialize (H1 args0); eapply hoare_proof_sound in H1.
    unfold hoare_triple in H1.
    simpl; eapply H1; eauto.
    eapply safe_Env_refine; eauto.
  Qed.

  Fixpoint build_safe_Env_hoare'
           (Sigs : total_map funSig)
           (Specs : total_map funSpec)
           (names : list funName)
           (Defs : list funDef)
  : Prop :=
  match names, Defs with
  | f :: names', fd :: Defs' =>
    Forall (fun fd' => ~ AppearsIn f (funBody fd')) Defs' /\
    ~ AppearsIn f (funBody fd) /\
    (forall orig_args,
        Specs |- {{ fun st => Forall2 (fun orig arg => st arg = orig)
                                         orig_args
                                         (funArgs fd) -> pre (Specs f) orig_args }}
                   funBody fd
                   {{ fun st => post (Specs f) (aeval st (funRet fd)) orig_args }})
      /\ (build_safe_Env_hoare' Sigs Specs names' Defs')
  | _, _ => True
  end.

  Definition build_safe_Env_hoare
             (names : list funName)
             (Sigs : list funSig)
             (Specs : list funSpec)
             (Defs : list funDef)
    : Prop :=
    build_safe_Env_hoare'
      (build_funSigs names Sigs)
      (build_funSpecs names Specs)
      names Defs.

  Lemma build_safe_Env_hoare_is_safe
    : forall (names : list funName)
             (Sigs : list funSig)
             (Specs : list funSpec)
             (Defs : list funDef)
             (SafeDefs :
                (fold_right (fun ffd P =>
                               ((forall args0 : list nat,
                                   pre ((build_funSpecs names Specs) (fst ffd)) args0 ->
                                   Safe {| funSigs := build_funSigs names Sigs;
                                           funSpecs := build_funSpecs names Specs;
                                           funDefs := empty |} (Imp.funBody (snd ffd))
                                        (build_total_map (Imp.funArgs (snd ffd)) args0 0)) * P)%type)
                            unit
                            (combine names Defs))),
      NoDup names ->
      length names = length Defs ->
      build_safe_Env_hoare names Sigs Specs Defs ->
      safe_Env (build_Env names Sigs Specs Defs).
  Proof.
    unfold build_Env, build_safe_Env_hoare, build_safe_Env in *.
    intros ? ? ? ?.
    generalize
      Defs
      (build_funSigs names Sigs)
      (build_funSpecs names Specs); clear.
    induction names; destruct Defs; simpl in *; intros; try discriminate.
    intuition eauto.
    eapply safe_Env_Extend with (Sigma := {| funSigs := _; funSpecs := _; funDefs := _ |});
      eauto.
    - inversion H; subst; eauto.
    - inversion H; subst.
      simpl; generalize H7 Defs; clear.
      induction names; intros; destruct Defs; try reflexivity; intros.
      simpl.
      unfold update, t_update; find_if_inside; subst.
      + destruct H7; simpl; eauto.
      + eapply IHnames.
        intro; eapply H7; simpl; intuition.
    - simpl; generalize H2 names; clear.
      intro; induction H2; destruct names; simpl; intros;
        try (compute in H; discriminate).
      apply update_inv in H0; intuition; subst; eauto.
    - eapply safe_funDef_hoare; eauto.
      inversion H; subst; eauto.
  Qed.

  Corollary hoare_proof_link_safe_Env
    : forall (names : list funName)
             (Sigs : list funSig)
             (Specs : list funSpec)
             (Defs : list funDef)
             (SafeDefs :
                (fold_right (fun ffd P =>
                               ((forall args0 : list nat,
                                   pre ((build_funSpecs names Specs) (fst ffd)) args0 ->
                                   Safe {| funSigs := build_funSigs names Sigs;
                                           funSpecs := build_funSpecs names Specs;
                                           funDefs := empty |} (Imp.funBody (snd ffd))
                                        (build_total_map (Imp.funArgs (snd ffd)) args0 0)) * P)%type)
                            unit
                            (combine names Defs)))
             (P Q : Assertion) c,
      NoDup names ->
      length names = length Sigs ->
      length names = length Specs ->
      length names = length Defs ->
      build_safe_Env_hoare names Sigs Specs Defs ->
      (forall st,
          P st ->
          Safe {| funSigs := build_funSigs names Sigs;
                  funSpecs := build_funSpecs names Specs;
                  funDefs := empty |} c st) ->
      build_funSpecs names Specs |- {{P}} c {{Q}} ->
    (build_Env names Sigs Specs Defs) |= {{P}} c {{Q}}.
  Proof.
    intros.
    eapply hoare_proof_link; eauto.
    eapply build_safe_Env_hoare_is_safe; eauto.
  Qed.

End Hoare.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Notation "Sigma |- {{ P }}  c  {{ Q }}" :=
  (hoare_proof Sigma P c Q) (at level 90, c at next level)
  : hoare_spec_scope.
