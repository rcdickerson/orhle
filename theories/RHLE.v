Require Import
        Coq.Arith.Arith
        Coq.micromega.Psatz
        Coq.Program.Tactics.

Require Import Maps Imp.

Require Import HoareCommon Hoare EHoare.
Require Import Coq.Vectors.Vector.

Definition RelAssertion {n m} := Vector.t state n -> Vector.t state m -> Prop.

Definition relAssert_implies {n m} (P Q : RelAssertion) : Prop :=
  forall (st : Vector.t state n)
         (st' : Vector.t state m),
    P st st' -> Q st st'.

Section RHLE.

  Variables n m : nat.
  Definition Ustate := Vector.t state n.
  Definition Estate := Vector.t state m.

  Definition Uprogs := Vector.t com n.
  Definition Eprogs := Vector.t com m.

  Definition rhle_triple
             (Sigma : ExEnv)
             (P : RelAssertion)
             (Uc : Uprogs)
             (Ec : Eprogs)
             (Q : RelAssertion) : Prop :=
    forall (Ust Ust' : Ustate)
           (Est : Estate),
      (forall i : Fin.t n,
          AllEnv |- Vector.nth Ust i =[ Vector.nth Uc i ]=> Vector.nth Ust' i) ->
      P Ust Est ->
      exists Est' (exe : forall i, AllEnv |- Vector.nth Est i =[ Vector.nth Ec i ]=> Vector.nth Est' i), Q Ust' Est'.

  Notation "Sigma |= {{ P }}  c1 ~# c2  {[ Q ]}" :=
    (rhle_triple Sigma P c1 c2 Q) (at level 90, c1 at next level, c2 at next level)
    : hoare_spec_scope.

  Reserved Notation "Sigma , ESigma |- {{ P }}  c1 ~# c2  {[ Q ]}"
           (at level 40, c1 at next level, c2 at next level).

  Inductive rhle_proof Sigma ESigma
    : @RelAssertion n m -> Uprogs -> Eprogs -> @RelAssertion n m -> Prop :=
  | RHE_Skip : forall P Uc Ec,
      (forall i, Vector.nth Uc i = CSkip)
      -> (forall i, Vector.nth Ec i = CSkip)
      -> rhle_proof Sigma ESigma P Uc Ec P

  | RHE_SkipIntroL : forall P Q Uc Ec Uc' i,
      (forall i', i <> i' -> Vector.nth Uc i' = Vector.nth Uc' i') ->
      Vector.nth Uc' i = CSeq (Vector.nth Uc i) CSkip ->
      rhle_proof Sigma ESigma P Uc' Ec Q ->
      rhle_proof Sigma ESigma P Uc Ec Q

    | RHE_SkipIntroR : forall P Q Uc Ec Ec' i,
      (forall i', i <> i' -> Vector.nth Ec i' = Vector.nth Ec' i') ->
      Vector.nth Ec' i = CSeq (Vector.nth Ec i) CSkip ->
      rhle_proof Sigma ESigma P Uc Ec' Q ->
      rhle_proof Sigma ESigma P Uc Ec Q

  | RHE_StepL :
      forall P Q R Uc Ec Uc' i c1 c2,
        (forall i', i <> i' -> Vector.nth Uc i' = Vector.nth Uc' i') ->
        Vector.nth Uc i = CSeq c1 c2 ->
        Vector.nth Uc' i = c2 ->
        (forall Ast Est,
            hoare_proof Sigma (fun st =>
                                 Vector.nth Ast i = st /\
                                 P Ast Est) c1
                        (fun st =>
                           R (replace Ast i st) Est)) ->
        rhle_proof Sigma ESigma R Uc' Ec Q ->
        rhle_proof Sigma ESigma P Uc Ec Q

  | RHE_StepR :
      forall P Q R Uc Ec Ec' i c1 c2,
        (forall i', i <> i' -> Vector.nth Ec i' = Vector.nth Ec' i') ->
        Vector.nth Ec i = CSeq c1 c2 ->
        Vector.nth Ec' i = c2 ->
        (forall Ast Est,
            ehoare_proof ESigma (fun st =>
                                 Vector.nth Est i = st /\
                                 P Ast Est) c1
                        (fun st => R Ast (replace Est i st))) ->

        rhle_proof Sigma ESigma R Uc Ec' Q ->
        rhle_proof Sigma ESigma P Uc Ec Q

  where "Sigma , ESigma |- {{ P }}  c1 ~# c2  {[ Q ]}" := (rhle_proof Sigma ESigma P c1 c2 Q) : hoare_spec_scope.

  Hint Resolve bassn_eval_true bassn_eval_false : hoare.
  Hint Constructors rhle_proof : hoare.
  Hint Unfold rhle_triple hoare_triple ehoare_triple.
  Hint Constructors ceval.

  (*Ltac apply_sound :=
    match goal with
    | H : context[_ |- {{_}} _ {{_}}] |- _ =>
      eapply hoare_proof_sound in H
    | H : context[_ |- {[_]} _ {[_]}#] |- _ =>
      eapply ehoare_proof_sound in H
    end. *)

  Lemma vector_nth_replace {A} {k}:
    forall (i : Fin.t k) (v : t A k) (a : A),
      nth (replace v i a) i = a.
  Proof.
    induction i;
      intros; pattern v; eapply caseS'; eauto; intros.
    simpl; eauto.
  Qed.

  Lemma vector_nth_replace' {A} {k}:
    forall (i i0 : Fin.t k) (v : t A k) (a : A),
      i <> i0 ->
      nth (replace v i a) i0 = nth v i0.
  Proof.
    induction i0;
      intros; pattern v; eapply caseS'; eauto; intros.
    - simpl; revert v a H h t.
      pattern i; eapply Fin.caseS'; intros; eauto.
      congruence.
    - simpl; revert v a H h t.
      pattern i; eapply Fin.caseS'; intros; eauto.
      eapply IHi0; congruence.
  Qed.

  Theorem rhle_proof_sound Sigs Sigma ESigma
          (Cons_Env : Consistent_Env {| AllEnv := {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |}; funExSpecs := ESigma |})
    : forall P c1 c2 Q,
      rhle_proof Sigma ESigma P c1 c2 Q ->
      {| AllEnv := {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |};
         funExSpecs := ESigma |} |= {{P}} c1 ~# c2 {[Q]}.
  Proof.
    intros ? ? ? ? pf.
    unfold rhle_triple.
    induction pf; intros Ust Ust' Est exe HP.
    - eexists Est.
      assert (Ust' = Ust).
      { revert H exe; clear.
        unfold Ustate in *; revert Ust Ust'.
        induction Uc.
        - intro; pattern Ust; eapply VectorDef.case0.
          intro; pattern Ust'; eapply VectorDef.case0.
          eauto.
        - intro; pattern Ust; eapply VectorDef.caseS'.
          intros h0 t Ust'; pattern Ust'; eapply VectorDef.caseS'.
          intros; f_equal.
          + specialize (H Fin.F1); specialize (exe Fin.F1); simpl in *.
            subst; inversion exe; eauto.
          + eapply IHUc; intros; eauto.
            eapply (fun i => H (Fin.FS i)).
            eapply (fun i => exe (Fin.FS i)).
      }
      assert (forall (i : Fin.t m), ceval {| funSigs := Sigs; funSpecs := Sigma; funDefs := @empty funDef |}  (nth Ec i) (nth Est i) (nth Est i)).
      { revert H0; clear.
        intros.
        rewrite H0.
        econstructor.
      }
      eexists X; subst; eauto.
    - eapply IHpf; eauto.
      intros.
      destruct (Fin.eq_dec i i0); subst.
      + rewrite H0; eauto.
      + rewrite <- H by eauto.
        eapply exe.
    - edestruct IHpf as [Est' [exe' HQ]]; eauto.
      assert (forall (i0 : Fin.t m), ceval {| funSigs := Sigs; funSpecs := Sigma; funDefs := @empty funDef |} (nth Ec i0) (nth Est i0)  (nth Est' i0) ).
      { intros; destruct (Fin.eq_dec i i0); subst.
        + specialize (exe' i0); rewrite H0 in exe'; simpl in *.
          inversion exe'; subst.
          inversion X0; subst.
          eauto.
        + rewrite H by eauto.
          eapply exe'.
      }
      eauto.
    - generalize (exe i); intros exe'.
      rewrite H0 in exe'; inversion exe'; subst.
      edestruct (IHpf (replace Ust i st') Ust'); eauto.
      + intros; destruct (Fin.eq_dec i i0); subst.
        * rewrite vector_nth_replace; eauto.
        * rewrite vector_nth_replace', <- H; eauto.
      + eapply (hoare_proof_sound _ _ _ _ _ (H2 Ust Est) _ _ X); eauto.
    - specialize (H2 Ust Est).
      eapply (@ehoare_proof_link {| AllEnv := {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |}; funExSpecs := ESigma |}) in H2; eauto using productive_empty.
      edestruct H2 as [? [? ?] ]; try tauto.
      edestruct IHpf as [Est' [exe' HQ]]; eauto.
      assert (forall (i0 : Fin.t m), ceval {| funSigs := Sigs; funSpecs := Sigma; funDefs := @empty funDef |}
                                           (nth Ec i0)
                                           (nth Est i0)
                                           (nth Est' i0)); eauto.
      intros; destruct (Fin.eq_dec i i0); subst.
      + rewrite H0; econstructor; eauto.
        specialize (exe' i0); rewrite vector_nth_replace in exe'; eauto.
      + specialize (exe' i0); rewrite vector_nth_replace' in exe'; eauto.
        rewrite H; eauto.
  Qed.

  (* Definition rwp (Sigma : Env) c (Q : Assertion2) : Assertion2 :=
    fun st1 st2 => exists st2' (exe : Sigma |- st2 =[ c ]=> st2'), Q st1 st2'. *)

        (* Need to adjust this proof to align with new semantics. *)
  (*Theorem rhle_proof_complete Sigs Sigma : forall P c1 c2 Q,
      {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} |= {{P}} c1 ~# c2 {[Q]} ->
      Sigma |- {{P}} c1 ~# c2 {[Q]}.
  Proof.
    unfold rhle_triple.
    intros P c1 c2 Q H.
    apply RHE_SkipIntroL.
    apply RHE_StepL with (@rwp {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |} c2 Q).
    - intros st2. eapply hoare_proof_complete with (Sigs := Sigs); firstorder.
    - apply RHE_SkipIntroR. eapply RHE_StepR. 2: constructor.
      intros st1.

      (* apply ehoare_proof_complete with (Sigs := Sigs); firstorder. *)
  Admitted. *)

End RHLE.

(*Lemma existential_not_universal :
    ~(forall Sigma P Q p, (~ (hoare_triple Sigma P p (fun st => ~ Q st)) ->
        (ehoare_triple Sigma P p Q))).
Proof.
  unfold not; intros.
  assert  *)



Notation "Sigma |= {{ P }}  c1 ~# c2  {[ Q ]}" :=
  (rhle_triple Sigma P c1 c2 Q) (at level 90, c1 at next level, c2 at next level)
  : hoare_spec_scope.

Notation "Sigma |- {{ P }}  c1 ~# c2  {[ Q ]}" :=
  (rhle_proof Sigma P c1 c2 Q) (at level 90, c1 at next level, c2 at next level)
  : hoare_spec_scope.
