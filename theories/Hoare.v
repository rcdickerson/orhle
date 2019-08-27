(** * Hoare Logic *)

(* Adapted from the Software Foundations series:
   https://softwarefoundations.cis.upenn.edu/ *)

Require Import Coq.Program.Tactics.
Require Import Maps Imp HoareCommon.

(* ################################################################# *)
(** * Hoare Triples *)

Section Hoare.

  Reserved Notation "Sigma |- {{ P }}  c  {{ Q }}"
           (at level 90, c at next level).

  Inductive hoare_proof (Sigma : total_map funSpec) : Assertion -> com -> Assertion -> Prop :=
  | H_Skip : forall P,
      Sigma |- {{P}} SKIP {{P}}
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
             {env : Env}
             (P : Assertion) (c : com) (Q : Assertion) : Prop :=
    forall st st',
      st =[ c ]=> st'  ->
      P st  ->
      Q st'.

  Notation "{{ P }}  c  {{ Q }}" :=
    (hoare_triple P c Q) (at level 90, c at next level)
    : hoare_spec_scope.

  Hint Resolve bassn_eval_true bassn_eval_false : hoare.
  Hint Constructors hoare_proof : hoare.
  Hint Unfold hoare_triple.
  Hint Constructors ceval.

  Lemma hoare_while {env : Env} : forall P b c,
      {{fun st => P st /\ bassn b st}} c {{P}} ->
      {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
  Proof.
    unfold hoare_triple.
    intros ? ? ? ? ? ? HE ?. remember (WHILE b DO c END)%imp eqn:Heq.
    induction HE; try inversion Heq; subst.
    - firstorder with hoare.
    - eauto.
  Qed.

  Theorem hoare_proof_sound Sigma : forall P c Q,
      Sigma |- {{P}} c {{Q}} ->
      @hoare_triple {| funSpecs := Sigma; funDefs := empty |} P c Q.
  Proof.
  intros ? ? ? pf. induction pf; intros st st' HE HP.
  - (* SKIP *)
    inversion HE; subst. eauto.
  - (* ::= *)
    inversion HE; subst. eauto.
  - (* ;; *)
    inversion HE; subst. eauto.
  - (* TEST *)
    inversion HE; subst. eauto.
    firstorder with hoare.
  - (* WHILE *)
    eapply hoare_while; eauto.
  - (* Conseq *)
    eauto.
  - (* :::= *)
    inversion HE; subst; try firstorder.
    simpl in H4; rewrite apply_empty in H4; discriminate.
  Qed.

  Definition wp {env : Env} (c:com) (Q:Assertion) : Assertion :=
    fun s => forall s', s =[ c ]=> s' -> Q s'.

  Lemma wp_is_precondition {env : Env}: forall c Q,
      {{wp c Q}} c {{Q}}.
  Proof.
    firstorder.
  Qed.

  Lemma wp_is_weakest {env : Env} : forall c Q P',
      {{P'}} c {{Q}} -> forall st, P' st -> wp c Q st.
  Proof.
    firstorder.
  Qed.

  Hint Resolve wp_is_precondition wp_is_weakest : hoare.
  Hint Unfold wp.

  Theorem hoare_proof_complete Sigma : forall P c Q,
      @hoare_triple {| funSpecs := Sigma; funDefs := empty |} P c Q->
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
      apply H_Seq with (@wp {| funSpecs := Sigma; funDefs := empty |} c2 Q); firstorder eauto.
    - (* IFB *)
      apply H_If.
      + firstorder eauto.
      + apply IHc2. firstorder with hoare.
    - (* WHILE *)
      eapply H_Consequence with (P':= @wp {| funSpecs := Sigma; funDefs := empty |} (WHILE b DO c END) Q).
      + constructor. firstorder eauto.
      + eauto.
      + firstorder with hoare.
  Qed.

  Theorem hoare_proof_link {Sigma : Env}
    : forall (P Q : Assertion) c,
      valid_Env Sigma ->
      (forall st, P st -> @Safe {| funSpecs := @funSpecs Sigma; funDefs := empty |} c st) ->
      funSpecs |- {{P}} c {{Q}} ->
      @hoare_triple Sigma P c Q.
  Proof.
    intros.
    pose proof (hoare_proof_sound _ _ _ _ H0);
      eauto using valid_Env_refine, hoare_proof_sound.
  Qed.

  (* This one is going to require more care...*)
  Theorem hoare_valid_Env
    : forall {Sigma : Env},
      (forall f fd,
          funDefs f = Some fd ->
          funSpecs |- {{ fun st => pre (funSpecs f) (List.map st (funArgs fd)) }}
                        funBody fd
                      {{ fun st => post (funSpecs f) (aeval st (funRet fd)) (List.map st (funArgs fd)) }}) ->
      valid_Env Sigma.
  Proof.
  Abort.

End Hoare.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Notation "Sigma |- {{ P }}  c  {{ Q }}" :=
  (hoare_proof Sigma P c Q) (at level 90, c at next level)
  : hoare_spec_scope.
