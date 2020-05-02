(** * Hoare Logic *)

(* Adapted from the Software Foundations series:
   https://softwarefoundations.cis.upenn.edu/ *)

Require Import Coq.Program.Tactics
        Coq.Lists.List.

Require Import Maps
        Imp
        HoareCommon
        Fixpoints.

(* ################################################################# *)
(** * Hoare Triples *)

Section Divergence.
  (* Characterizing non-terminating commands. *)

  Reserved Notation "Sigma '|-' st '=[' c ']=><' "
           (at level 40).

  CoInductive com_diverges (Sigma : Env) : com -> state -> Prop :=
  | D_Seq_L : forall c1 c2 st,
      Sigma |- st =[ c1 ]=>< ->
      Sigma |- st =[ c1;; c2 ]=><

  | D_Seq_R : forall c1 c2 st st',
      Sigma |- st =[ c1 ]=> st' ->
      Sigma |- st' =[ c2 ]=>< ->
      Sigma |- st =[ c1;; c2 ]=><

  | Div_IfTrue : forall st b c1 c2,
      beval st b = true ->
      Sigma |- st =[ c1 ]=>< ->
      Sigma |- st =[ TEST b THEN c1 ELSE c2 FI ]=><

  | Div_IfFalse : forall st b c1 c2,
      beval st b = false ->
      Sigma |- st =[ c2 ]=>< ->
      Sigma |- st =[ TEST b THEN c1 ELSE c2 FI ]=><

  | Div_WhileTrue : forall st st' b c,
      beval st b = true ->
      Sigma |- st  =[ c ]=> st' ->
      Sigma |- st' =[ WHILE b DO c END ]=>< ->
      Sigma |- st  =[ WHILE b DO c END ]=><

  where "Sigma |- st =[ c ]=><" := (com_diverges Sigma c st).

  Inductive strongly_terminates (Sigma : Env) : com -> state -> Prop :=
  | ST_ceval : forall st,
      strongly_terminates Sigma CSkip st
  | ST_Ass  : forall st a1 x,
      strongly_terminates Sigma (CAss x a1) st
  | ST_Seq : forall c1 c2 st,
      strongly_terminates Sigma c1 st
      -> (forall st', Sigma |- st  =[ c1 ]=> st' ->
          strongly_terminates Sigma c2 st')
      -> strongly_terminates Sigma (CSeq c1 c2) st
  | ST_IfTrue : forall st b c1 c2,
      beval st b = true ->
      strongly_terminates Sigma c1 st ->
      strongly_terminates Sigma (TEST b THEN c1 ELSE c2 FI) st
  | ST_IfFalse : forall st b c1 c2,
      beval st b = false ->
      strongly_terminates Sigma c2 st ->
      strongly_terminates Sigma (TEST b THEN c1 ELSE c2 FI) st
  | ST_WhileFalse : forall b st c,
      beval st b = false ->
      strongly_terminates Sigma (WHILE b DO c END) st
  | ST_WhileTrue : forall st b c,
      beval st b = true ->
      strongly_terminates Sigma c st ->
      (forall st', Sigma |- st  =[ c ]=> st' ->
                   strongly_terminates Sigma (WHILE b DO c END) st') ->
      strongly_terminates Sigma (WHILE b DO c END) st

  (* Termination of Function Calls *)
  | ST_CallSpec : forall st args x f,
      strongly_terminates Sigma (x :::= f $ args) st.

  Lemma strong_termination_no_divergence
    : forall (Sigma : Env) (c : com) (st : state),
      strongly_terminates Sigma c st ->
      ~ Sigma |- st =[ c ]=><.
  Proof.
    induction 1; intro H'; try solve [inversion H'; subst; eauto; congruence].
    - inversion H'; subst; eauto.
      eapply H1; eauto.
    - inversion H'; subst; eauto.
      eapply H2; eauto.
  Qed.

  (*Lemma no_divergence_strong_termination
    : forall (Sigma : Env) (c : com) (st : state),
      ~ Sigma |- st =[ c ]=>< ->
        strongly_terminates Sigma c st.
  Proof.
    induction c; intros; try solve [econstructor].
    - admit.
    - econstructor.
      eapply IHc1.
      intro.
    eapply H; econstructor; eauto.
    intros; eapply IHc2; intro.
    eapply H; eapply D_Seq_R; eauto.
  - destruct (beval st b) eqn: ?.
    + econstructor; eauto.
      eapply IHc1; intro; eapply H; econstructor; eauto.
    + eapply ST_IfFalse; eauto.
      eapply IHc2; intro; eapply H; eapply Div_IfFalse; eauto.
  - destruct (beval st b) eqn: ?.
    + eapply ST_WhileTrue; eauto.
      eapply IHc; intro; eapply H.
      econstructor.

      eapply IHc1; intro; eapply H; econstructor; eauto.
    + eapply ST_IfFalse; eauto.
      eapply IHc2; intro; eapply H; eapply Div_IfFalse; eauto.

    inversion H'; subst; eauto.
    eapply H1; eauto.
  - inversion H'; subst; eauto.
    eapply H2; eauto.
Qed. *)

End Divergence.

Notation  "Sigma '|-' st '=[' c ']=><' "
  := (com_diverges Sigma c st) (at level 40).

Section HoareTotal.

  Reserved Notation "Sigma |- [[ P ]]  c  [[ Q ]]"
           (at level 40, c at next level).

  CoInductive infiniteDecreasingChain {A} (R : A -> A -> Prop) : A -> Prop :=
  | ChainCons : forall x y,
      infiniteDecreasingChain R y
      -> R y x
      -> infiniteDecreasingChain R x.

  Theorem noBadChains :
    forall A (R : A -> A -> Prop),
      well_founded R
      -> forall a, ~infiniteDecreasingChain R a.
  Proof.
    intros ? ? ? ? ?.
    specialize (H a).
    induction H.
    inversion H0; subst; eauto.
  Qed.

  Inductive hoare_total_proof (Sigma : total_map funSpec) : Assertion -> com -> Assertion -> Prop :=
  | HT_Skip : forall P,
      Sigma |- [[ P ]] SKIP [[P]]
  | HT_Asgn : forall Q V a,
      Sigma |- [[Q[V |-> a] ]] V ::= a [[Q]]
  | HT_Seq  : forall P c Q d R,
      Sigma|- [[P]] c [[Q]] ->
      Sigma |- [[Q]] d [[R]] ->
      Sigma |- [[P]] c;;d [[R]]
  | HT_If : forall P Q b c1 c2,
      Sigma |- [[fun st => P st /\ bassn b st]] c1 [[Q]] ->
      Sigma |- [[fun st => P st /\ ~(bassn b st)]] c2 [[Q]] ->
      Sigma |- [[P]] TEST b THEN c1 ELSE c2 FI [[Q]]
  | HT_While : forall {A : Type} (R : A -> A -> Prop) M P b c,
      well_founded R ->
      (forall (a : A),
          Sigma |- [[fun st => P st /\ bassn b st /\ M a st]] c [[fun st => P st /\ exists a', M a' st /\ R a' a]]) ->
      Sigma |- [[fun st => P st /\ exists a, M a st]] WHILE b DO c END [[fun st => P st /\ ~ (bassn b st)]]
  | HT_Consequence  : forall (P Q P' Q' : Assertion) c,
      Sigma |- [[P']] c [[Q']] ->
      (forall st, P st -> P' st) ->
      (forall st, Q' st -> Q st) ->
      Sigma |- [[P]] c [[Q]]

  | HT_Call : forall Q y f xs,
      Sigma |- [[fun st =>
            (Sigma f).(pre) (aseval st xs) ->
            forall v, (Sigma f).(post) v (aseval st xs) ->
                 Q[y |-> v] st]] y :::= f $ xs [[Q]]


where "Sigma |- [[ P ]]  c  [[ Q ]]" := (hoare_total_proof Sigma P c Q) : hoare_spec_scope.

  Definition hoare_total_triple
             (Sigma : Env)
             (P : Assertion)
             (c : com)
             (Q : Assertion) : Prop :=
    forall st st',
        Sigma |- st =[ c ]=> st'  ->
      P st  ->
      Q st'.

  Notation "Sigma '|=' [[ P ]]  c  [[ Q ]]" :=
    (hoare_total_triple Sigma P c Q) (at level 40, c at next level)
    : hoare_spec_scope.

  Hint Resolve bassn_eval_true bassn_eval_false : hoare.
  Hint Constructors hoare_total_proof : hoare.
  Hint Unfold hoare_total_triple.
  Hint Constructors ceval.

  Lemma hoare_while (Sigma : Env) : forall {A : Type} (R : A -> A -> Prop) M a P b c,
      (forall a, Sigma |= [[fun st : state => P st /\ bassn b st /\ M a st]] c
       [[fun st : state => P st /\ (exists a' : A, M a' st /\ R a' a)]]) ->
      Sigma |= [[fun st => P st /\ M a st]] WHILE b DO c END [[fun st => P st /\ ~ (bassn b st)]].
  Proof.
    unfold hoare_total_triple.
    intros ? ? ? ? ? ? ? ? ? ? HE [? ?]. remember (WHILE b DO c END)%imp eqn:Heq.
    revert a H1.
    induction HE; try inversion Heq; intros; subst.
    - firstorder with hoare.
    - eapply H in HE1; try solve [intuition eauto].
      destruct HE1 as [? [a' [? ?] ] ].
      eapply IHHE2; eauto.
  Qed.

  Lemma hoare_proof_safe Sigs Sigma : forall P c Q,
      Sigma |- [[P]] c [[Q]] ->
       {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} |= [[P]] c [[Q]].
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
    destruct HP as [? [n ?] ].
    eapply hoare_while; intuition eauto.
  - (* Conseq *)
    eauto.
  - (* :::= *)
    inversion HE; subst; firstorder.
    simpl in H4; rewrite apply_empty in H4; discriminate.
  Qed.

  Lemma hoare_proof_terminates Sigs Sigma : forall P c Q,
      Sigma |- [[P]] c [[Q]] ->
      forall st,
        P st ->
        strongly_terminates {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} c st.
  Proof.
  intros ? ? ? pf. induction pf; intros st HP.
  - (* SKIP *)
    econstructor.
  - (* ::= *)
    econstructor.
  - (* ;; *)
    econstructor; eauto.
    intros; eapply IHpf2.
    eapply hoare_proof_safe; eauto.
  - (* TEST *)
    destruct (beval st b) eqn: ?.
    + econstructor; eauto.
    + eapply ST_IfFalse; eauto.
      eapply IHpf2; intuition.
      eapply bassn_eval_false; eauto.
  - (* WHILE *)
    destruct HP as [? [a ?] ].
    revert H0 H1 st H2 H3.
    specialize (H a); induction H; intros.
    destruct (beval st b) eqn: ?.
    + eapply ST_WhileTrue; eauto.
      intros.
      generalize (hoare_proof_safe Sigs Sigma _ _ _ (H1 x) _ _ H5); intros [? [a' [? ?] ] ]; intuition eauto.
    + econstructor; eauto.
  - (* Conseq *)
    eapply IHpf; eauto.
  - (* :::= *)
    econstructor.
  Qed.

  Theorem hoare_proof_sound Sigs Sigma : forall P c Q,
      Sigma |- [[P]] c [[Q]] ->
      {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} |= [[P]] c [[Q]]
      /\ forall st,
         P st ->
         strongly_terminates {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} c st.
  Proof.
    intros; split; eauto using hoare_proof_safe, hoare_proof_terminates.
  Qed.

  (* The weakest precondition for an assertion [Q] and command [c] is
     the set of initial states from which [c] always terminates, and
     always ends in a final state satisfying [Q]. *)
  Definition wp (Sigma : Env)
             (c : com)
             (Q : Assertion) : Assertion :=
    fun s => (forall s', Sigma |- s =[ c ]=> s' -> Q s')
             /\ strongly_terminates Sigma c s.

  Lemma wp_is_precondition (Sigma : Env): forall c Q,
      Sigma |= [[wp Sigma c Q]] c [[Q]].
  Proof.
    firstorder.
  Qed.

  Lemma wp_is_weakest (Sigma : Env) : forall c Q P',
      Sigma |= [[P']] c [[Q]] ->
      forall st, P' st -> strongly_terminates Sigma c st -> wp Sigma c Q st.
  Proof.
    firstorder.
  Qed.

  (* For total correctness, we want the set of initial states that
  cause the loop to end in a state satisfying the post condition *)

  Definition gamma'
           (Q : Assertion)
           (c : com)
           (b : bexp)
           (WP : Assertion -> Assertion)
    : Assertion :=
    @LFP state (fun (G : _ -> _) (st : state) => (~ bassn b st /\ Q st)
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

  Definition wp_while
             (Sigma : total_map funSpec)
             (Q : Assertion)
             (c : com)
             (b : bexp) :=
    gamma' Q c b
           (fun (Q : Assertion) (st : state) =>
              (bassn b st -> wp_gen' Sigma c Q st) /\ ((bassn b st -> False) -> Q st)).

  Lemma wp_gen'_is_monotone
        Sigma
    : forall (c : com) (a : state) (S S' : state -> Prop),
      (forall a0 : state, S a0 -> S' a0) -> wp_gen' Sigma c S a -> wp_gen' Sigma c S' a.
  Proof.
    induction c; simpl; intros; eauto.
    - unfold assn_sub; eauto.
    - unfold assn_sub in *; eauto.
    - intuition; eauto.
    - unfold gamma', LFP, FClosed, Subset, In in *.
      intros; eapply H0; intros.
      intuition eauto.
  Qed.

  Corollary wp_gen'_CWhile_is_monotone
    : forall Sigma b Q c,
      Monotone_F
        (fun (G : state -> Prop) (st0 : state) =>
           (bassn b st0 -> False) /\ Q st0 \/
     bassn b st0 /\ (bassn b st0 -> wp_gen' Sigma c G st0) /\ ((bassn b st0 -> False) -> G st0)).
  Proof.
    unfold Monotone_F, Subset, In.
    intros. intuition.
    right.
    intuition.
    eauto using wp_gen'_is_monotone.
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
      eapply H; eauto.
    - destruct H as [? ?].
      inversion H0; subst.
      eapply IHc1; intuition.
      split; intros; eauto.
      eapply IHc2; intros.
      split; intros; eauto.
    - destruct H as [? ?].
      firstorder eauto.
      + eapply IHc1; split; intros; eauto.
        inversion H0; subst; eauto.
        eapply bassn_eval_true in H1; congruence.
      + eapply IHc2; split; intros; eauto.
        eapply H; eauto.
        eapply E_IfFalse; eauto; eapply bassn_eval_false; eauto.
        inversion H0; subst; eauto.
        eapply bassn_eval_false in H1; congruence.
    - unfold gamma'.
      unfold wp in H.
      intuition.
      remember (WHILE b DO c END)%imp eqn:Heq.
      revert Q H0; induction H1; intros; try congruence.
      + injections.
        eapply LFP_is_FClosed; eauto using wp_gen'_CWhile_is_monotone.
        unfold In; intuition.
        left.
        intuition.
        eapply bassn_eval_false; eauto.
      + injections.
        eapply LFP_is_FClosed; eauto using wp_gen'_CWhile_is_monotone.
        unfold In; intuition.
        right; intuition; intros.
        eapply IHc; split; eauto.
  Qed.

  Definition succR
             (Sigma : Env)
             (b : bexp)
             (c : com)
             (Inv : Assertion)
             (st st' : state) :=
    Inv st /\ bassn b st /\ Sigma |- st =[ c ]=> st'.

  Inductive succRstar
            (Sigma : Env)
            (b : bexp)
            (c : com)
            (Inv : Assertion)
    : state -> state -> Prop :=
  | succROne : forall st st',
      succR Sigma b c Inv st st' ->
      succRstar Sigma b c Inv st st'
  | succRtrans : forall st st' st'',
      succR Sigma b c Inv st st' ->
      succRstar Sigma b c Inv st' st'' ->
      succRstar Sigma b c Inv st st''.

  Lemma Acc_succRStar
    : forall (Sigma : Env)
             (b : bexp)
             (c : com)
             (Inv : Assertion),
      (forall st, Inv st ->
                  (bassn b st -> forall st', Sigma |- st =[ c ]=> st' -> Inv st')
                  /\ strongly_terminates Sigma (CWhile b c) st) ->
      forall st,
        Inv st ->
        strongly_terminates Sigma (CWhile b c) st ->
        Acc (fun st' st => succRstar Sigma b c Inv st st') st.
  Proof.
    intros.
    revert H1 H H0.
    remember (WHILE b DO c END)%imp.
    induction 1; intros; try discriminate.
    - econstructor; intros.
      injections.
      induction H2.
      + unfold succR in H2; intuition.
        eapply bassn_eval_true in H2; congruence.
      + unfold succR in H2; intuition.
        eapply bassn_eval_true in H2; congruence.
    - injections.
      econstructor; intro.
      intro.
      revert H5 H3 H2 H4; clear. induction 1; intros.
      * unfold succR in H.
        apply (H2 st'); intuition eauto.
        eapply H3; eauto.
      * unfold succR in H; intuition.
        assert (Inv st') as Inv_st' by (eapply H3; eauto).
        (* Invariant preservation; Acc fact; Invarant *)
        eapply H1; intros; eauto.
        eapply H2 in H6; eauto.
        inversion H6; eapply H10.
        econstructor; unfold succR.
        intuition.
        revert H5; clear; intros.
        induction H5; unfold succR in *; intuition.
  Qed.

  Lemma well_founded_succRStar
    : forall (Sigma : Env)
             (b : bexp)
             (c : com)
             (Inv : Assertion),
      (forall st, Inv st ->
                  (bassn b st -> forall st', Sigma |- st =[ c ]=> st' -> Inv st')
                  /\ strongly_terminates Sigma (CWhile b c) st) ->
      well_founded (fun st' st => succRstar Sigma b c Inv st st').
  Proof.
    unfold well_founded; intros.
    constructor; intros.
    induction H0.
    - destruct H0 as [? [? ?] ].
      eapply Acc_succRStar; eauto.
      + eapply H; eauto.
      + eapply H; eauto.
        eapply H; eauto.
    - assumption.
  Qed.

  Theorem hoare_proof_wp (Sigs : total_map funSig)
          (Sigma : total_map funSpec) : forall c Q,
      Sigma |- [[wp_gen' Sigma c Q]] c [[Q]].
  Proof.
    induction c; simpl; intros; try solve [econstructor].
    - eapply HT_Consequence with (Q := Q); simpl; eauto.
      + apply HT_Call.
      + simpl; intros; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
      + econstructor; firstorder eauto.
      + econstructor; firstorder eauto.
    - econstructor.
      eapply HT_While with (M := eq) (P := gamma' Q c b _).
      * eapply (well_founded_succRStar {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |}
                                       b c
                                       (wp_while Sigma Q c b)).
        split; intros.
        -- eapply @LFP_is_FConsistent in H; unfold In in H;
             intuition eauto using wp_gen'_CWhile_is_monotone.
           eapply hoare_proof_safe in H3.
           2: eapply IHc.
           2: eassumption.
           eapply H3.
        -- unfold gamma' in H.
           pattern st.
           eapply Ind; try eassumption.
           unfold FClosed, Subset, In; intros.
           intuition.
           ++ econstructor; eauto.
              eapply bassn_eval_false; eauto.
           ++ eapply ST_WhileTrue; eauto.
              2: intros; eapply hoare_proof_safe in H2; [ | eapply IHc | eassumption ]; eauto.
              eapply hoare_proof_terminates in H2; eauto.
      * intros; simpl.
        econstructor.
        -- eapply IHc with (Q := fun st =>
                                   wp_while Sigma Q c b st
                                   /\ succR {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} b c
                                            (wp_while Sigma Q c b) a st).
        -- instantiate (1:= (fun Q st => (bassn b st -> wp_gen' Sigma c Q st)
                                         /\ (~ bassn b st -> Q st))).
           intros; intuition; subst.
           generalize H0; intro H'; eapply @LFP_is_FConsistent in H'; unfold In in H';
             intuition.
           2: { unfold Monotone_F, Subset, In; intros.
                eapply wp_gen'_CWhile_is_monotone; eauto.  }
           eapply wp_gen_is_wp; unfold wp, succR; split; intros.
           intuition eauto.
           eapply hoare_proof_sound; eauto.
           eapply hoare_proof_terminates; eauto.
        -- simpl; intros; split.
           eapply H.
           eexists _; split; eauto.
           econstructor.
           eapply H.
      * intros; simpl; split; [eapply H | eauto].
      * intros; simpl in H; intuition.
        eapply @LFP_is_FConsistent in H0; unfold In in H0; intuition.
        eapply wp_gen'_CWhile_is_monotone.
  Qed.

  Theorem hoare_proof_complete' Sigs Sigma : forall P c Q,
      {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} |= [[P]] c [[Q]] ->
      (forall st, P st -> strongly_terminates {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} c st) ->
      Sigma |- [[P]] c [[Q]].
  Proof.
    intros.
    econstructor.
    - eapply hoare_proof_wp; eauto.
    - intros.
      eapply (wp_is_weakest _ _ _ _ H) in H1.
      eapply wp_gen_is_wp in H1; eauto.
      eauto.
    - eauto.
  Qed.

  Print Assumptions hoare_proof_complete'.

  Theorem hoare_proof_link {Sigma : Env}
    : forall (P Q : Assertion) c,
      safe_Env Sigma ->
      (forall st, P st -> @Safe {| funSigs := @funSigs Sigma;
                                   funSpecs := @funSpecs Sigma;
                                   funDefs := empty |} c st) ->
      funSpecs |- [[P]] c [[Q]] ->
      Sigma |= [[P]] c [[Q]].
  Proof.
    intros.
    pose proof (hoare_proof_sound (@funSigs Sigma) _ _ _ _ H1).
    intuition.
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
          funSpecs |- [[ fun st => Forall2 (fun orig arg => st arg = orig)
                                        orig_args
                                        args -> pre spec orig_args ]]
                     body
                     [[ fun st => post spec (aeval st ret) orig_args ]])
      -> safe_funDef Sigma spec {| funArgs := args; funBody := body; funRet := ret |}.
  Proof.
    intros.
    unfold safe_funDef in *; intros.
    specialize (H1 args0); eapply hoare_proof_sound in H1.
    unfold hoare_total_triple in H1.
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
        Specs |- [[ fun st => Forall2 (fun orig arg => st arg = orig)
                                         orig_args
                                         (funArgs fd) -> pre (Specs f) orig_args ]]
                   funBody fd
                   [[ fun st => post (Specs f) (aeval st (funRet fd)) orig_args ]])
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
      build_funSpecs names Specs |- [[P]] c [[Q]] ->
    (build_Env names Sigs Specs Defs) |= [[P]] c [[Q]].
  Proof.
    intros.
    eapply hoare_proof_link; eauto.
    eapply build_safe_Env_hoare_is_safe; eauto.
  Qed.

End HoareTotal.

Notation "[[ P ]]  c  [[ Q ]]" :=
  (hoare_total_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Notation "Sigma |- [[ P ]]  c  [[ Q ]]" :=
  (hoare_total_proof Sigma P c Q) (at level 90, c at next level)
  : hoare_spec_scope.
