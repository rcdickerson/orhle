(** * Hoare Logic *)

(* Adapted from the Software Foundations series:
   https://softwarefoundations.cis.upenn.edu/ *)

Require Import Coq.Program.Tactics
        Coq.Lists.List.

Require Import
        Common
        Maps
        FunImp
        HoareCommon
        Fixpoints.

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
  | H_Havoc : forall Q V,
     Sigma |- {{fun st => forall (n : nat), Q[V |-> n] st}} (CHavoc V) {{Q}}
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
            (Sigma f).(pre) (aseval st xs) /\
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

  #[local] Hint Resolve bassn_eval_true bassn_eval_false : hoare.
  Hint Constructors hoare_proof : hoare.
  Hint Unfold hoare_triple : hoare.
  Hint Constructors ceval : core.

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
  - (* Havoc *)
    inversion HE; subst; eapply HP.
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

  Theorem hoare_proof_link {Sigma : Env}
    : forall (P Q : Assertion) c,
      compatible_env Sigma ->
      funSpecs |- {{P}} c {{Q}} ->
      Sigma |= {{P}} c {{Q}}.
  Proof.
    intros.
    pose proof (hoare_proof_sound (@funSigs Sigma) _ _ _ _ H0).
    eauto using compatible_Env_refine, hoare_proof_sound with hoare.
  Qed.

  Lemma compatible_funDef_hoare :
    forall (Sigma : Env) spec args body ret,
      compatible_env Sigma ->
      (forall orig_args,
          funSpecs |- {{ fun st => Forall2 (fun orig arg => st arg = orig)
                                        orig_args
                                        args -> pre spec orig_args }}
                     body
                     {{ fun st => post spec (aeval st ret) orig_args }})
      -> compatible_funDef Sigma spec {| funArgs := args; funBody := body; funRet := ret |}.
  Proof.
    intros.
    unfold compatible_funDef in *; intros.
    specialize (H0 args0); eapply hoare_proof_sound in H0.
    unfold hoare_triple in H0.
    simpl; eapply H0; eauto.
    eapply compatible_Env_refine; eauto.
  Qed.

  Fixpoint build_compatible_Env_hoare'
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
      /\ (build_compatible_Env_hoare' Sigs Specs names' Defs')
  | _, _ => True
  end.

  Definition build_compatible_Env_hoare
             (names : list funName)
             (Sigs : list funSig)
             (Specs : list funSpec)
             (Defs : list funDef)
    : Prop :=
    build_compatible_Env_hoare'
      (build_funSigs names Sigs)
      (build_funSpecs names Specs)
      names Defs.

  Lemma build_compatible_Env_hoare_is_safe
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
                                           funDefs := empty |} (FunImp.funBody (snd ffd))
                                        (build_total_map (FunImp.funArgs (snd ffd)) args0 0)) * P)%type)
                            unit
                            (combine names Defs))),
      NoDup names ->
      length names = length Defs ->
      build_compatible_Env_hoare names Sigs Specs Defs ->
      compatible_env (build_Env names Sigs Specs Defs).
  Proof.
    unfold build_Env, build_compatible_Env_hoare, build_compatible_env in *.
    intros ? ? ? ?.
    generalize
      Defs
      (build_funSigs names Sigs)
      (build_funSpecs names Specs); clear.
    induction names; destruct Defs; simpl in *; intros; try discriminate.
    intuition eauto.
    eapply compatible_env_Extend with (Sigma := {| funSigs := _; funSpecs := _; funDefs := _ |});
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
    - eapply compatible_funDef_hoare; eauto.
      inversion H; subst; eauto.
  Qed.

  Corollary hoare_proof_link_compatible_Env
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
                                           funDefs := empty |} (FunImp.funBody (snd ffd))
                                        (build_total_map (FunImp.funArgs (snd ffd)) args0 0)) * P)%type)
                            unit
                            (combine names Defs)))
             (P Q : Assertion) c,
      NoDup names ->
      length names = length Sigs ->
      length names = length Specs ->
      length names = length Defs ->
      build_compatible_Env_hoare names Sigs Specs Defs ->
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
    eapply build_compatible_Env_hoare_is_safe; eauto.
  Qed.

End Hoare.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Notation "Sigma |- {{ P }}  c  {{ Q }}" :=
  (hoare_proof Sigma P c Q) (at level 90, c at next level)
  : hoare_spec_scope.
