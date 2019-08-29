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
      valid_Env Sigma ->
      (forall st, P st -> @Safe {| funSigs := @funSigs Sigma;
                                   funSpecs := @funSpecs Sigma;
                                   funDefs := empty |} c st) ->
      funSpecs |- {{P}} c {{Q}} ->
      Sigma |= {{P}} c {{Q}}.
  Proof.
    intros.
    pose proof (hoare_proof_sound (@funSigs Sigma) _ _ _ _ H0);
      eauto using valid_Env_refine, hoare_proof_sound.
  Qed.

  (*Fixpoint prove_safe_Env
           (names : list funName)
           (Sigs : list funSig)
           (Specs : list funSpec)
           (Defs : list funDef)
  : Prop :=
  match names, Sigs, Specs, Defs with
  | f :: names', sig :: Sigs', spec :: Specs', fd :: Defs' =>
    Forall (fun fd' => ~ AppearsIn f (funBody fd)) Defs' /\
    ~ AppearsIn f (funBody fd) /\
      (forall orig_args,
          Specs |- {{ fun st => Forall2 (fun orig arg => st arg = orig)
                                           orig_args
                                           args -> pre (funSpecs f) orig_args }}
                        body
                        {{ fun st => post (funSpecs f) (aeval st ret) orig_args }})


    valid_funDef (build_Env names' Sigs' Specs' Defs')
                 spec fd
  | _, _, _, _ => True
  end.

Fixpoint safe_Env
           (names : list funName)
           (Sigs : list funSig)
           (Specs : list funSpec)
           (Defs : list funDef)
  : Prop :=
  match names, Sigs, Specs, Defs with
  | f :: names', sig :: Sigs', spec :: Specs', fd :: Defs' =>
    Forall (fun fd' => ~ AppearsIn f (funBody fd)) Defs' /\
    ~ AppearsIn f (funBody fd) /\
    valid_funDef (build_Env names' Sigs' Specs' Defs')
                 spec fd
  | _, _, _, _ => True
  end.

Lemma safe_Env_is_valid
  : forall (names : list funName)
           (Sigs : list funSig)
           (Specs : list funSpec)
           (Defs : list funDef),
    NoDup names ->
    length names = length Sigs ->
    length names = length Specs ->
    length names = length Defs ->
    safe_Env names Sigs Specs Defs ->
    valid_Env (build_Env names Sigs Specs Defs).
Proof.
  induction names; simpl; intros.
  - unfold valid_Env; unfold build_Env; simpl; intros;
      compute in H1; discriminate.
  - destruct Sigs; destruct Specs; destruct Defs; simpl in *;
      try discriminate; injections.
    simpl.
    unfold build_Env; simpl.
(* This is a straightforward proof. *)
Admitted.

  Lemma extend_funDefs
    : forall
      (Sigma' : Env)
      (c : com)
      (st st' : total_map nat)
      (H : Sigma' |- st =[ c ]=> st')
      (Sigma : Env)
      (fd : funDef)
      (f : String.string),
      (Safe {| funSigs := funSigs; funSpecs := funSpecs; funDefs := empty |} c st) ->
      Sigma' = {| funSigs := funSigs;
                  funSpecs := funSpecs;
                  funDefs := fun x' : String.string => if String.string_dec f x' then Some fd else funDefs x' |} ->
      funDefs f = None ->
      Sigma |- st =[ c ]=> st'.
  Proof.
    induction 1; intros; eauto; subst; simpl in *.
    - inversion X; subst; econstructor; eauto.
      eapply IHceval2; eauto.
      eapply X1.
      admit.
    - simpl in *.

  (*- find_if_inside; try discriminate; econstructor; eauto.
    - find_if_inside; injections; eauto.
      + econstructor; eauto. *)
  Admitted.

  Lemma hoare_valid_funDef
    : forall {Sigma : Env} f args body ret,
      valid_Env Sigma ->
      funDefs f = None ->
      (forall orig_args st,
          (Forall2 (fun orig arg => st arg = orig)
                   orig_args
                   args -> pre (funSpecs f) orig_args)
          -> @Safe {| funSigs := @funSigs Sigma;
                      funSpecs := @funSpecs Sigma;
                      funDefs := empty |} body st) ->
      (forall orig_args,
          funSpecs |- {{ fun st => Forall2 (fun orig arg => st arg = orig)
                                           orig_args
                                           args -> pre (funSpecs f) orig_args }}
                        body
                        {{ fun st => post (funSpecs f) (aeval st ret) orig_args }}) ->
      valid_Env {|
          funSigs := funSigs;
          funSpecs := funSpecs;
                   funDefs := f |-> {| funArgs := args;
                                       funBody := body;
                                       funRet := ret |};
                   funDefs |}.
  Proof.
    unfold valid_Env; simpl; unfold update, t_update; intros.
    find_if_inside; subst; injections.
    - assert (forall orig_args,
                 Sigma |= {{ fun st => Forall2 (fun orig arg => st arg = orig)
                                               orig_args
                                               args -> pre (funSpecs f0) orig_args}} body
                       {{fun st : state => post (funSpecs f0) (aeval st ret) orig_args}}) by
          eauto using hoare_proof_link.
      unfold valid_funDef, hoare_triple in *; intros.
      simpl in *; eapply H2 with (st := build_total_map args args0 0); eauto.
      replace body with (funBody {| funArgs := args; funBody := body; funRet := ret |}) in X by reflexivity.
      simpl in X.
      eapply extend_funDefs in X0; eauto.
    -


        inversion X0; subst; eapply E_IfFalse; eauto; congruence.

        econstructor; eauto.
          eapply IHbody1; eauto; intros; eapply X in H; inversion H; subst; eauto.


      + admit.
      + eauto.


    intros.
    eapply hoare_proof_link
    - injections.
      unfold valid_funDef; intros.
      eapply hoare_proof_sound in H1; unfold hoare_triple in H1;
        eapply H1 with (st := build_total_map args args0 0); simpl in *; firstorder.
      admit.
    - unfold valid_funDef in *; intros.
      eapply H; eauto.

      Unset Printing Notations.
      Set Printing Implicit.



    - injection H2; intros; subst.
      Focus 2.
    eapply H in
    2: eapply H.
  Abort. *)

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
