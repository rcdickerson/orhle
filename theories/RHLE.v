Require Import
        Coq.Arith.Arith
        Coq.Sets.Ensembles
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

  Lemma vector_replace_nth_id {A} {k}:
    forall (i : Fin.t k) (v : t A k),
      replace v i (nth v i) = v.
  Proof.
    induction i;
      intros; pattern v; eapply caseS'; eauto; intros.
    simpl; eauto.
    rewrite IHi; reflexivity.
  Qed.

  Lemma vector_nth_exists {A} {k} (P : A -> Fin.t k -> Prop):
    (forall (i : Fin.t k), exists (a : A), P a i) ->
    exists (v : t A k), forall (i : Fin.t k), P (Vector.nth v i) i.
  Proof.
    induction k; intros.
    - eexists (nil _); intros; inversion i.
    - specialize (IHk (fun a i => P a (Fin.FS i)) (fun i => H (Fin.FS i))); destruct IHk.
      destruct (H Fin.F1).
      eexists (Vector.cons _ x0 _ x).
      intros.
      pattern i; eapply Fin.caseS'; intros; eauto.
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
      eexists _; subst; eauto.
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
          inversion H6; subst.
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
      + eapply (hoare_proof_sound _ _ _ _ _ (H2 Ust Est) _ _ H5); eauto.
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
        admit.
      + specialize (exe' i0); rewrite vector_nth_replace' in exe'; eauto.
        rewrite H; eauto.
        Grab Existential Variables.
        admit.
        intros; eauto.
  Admitted.

  Inductive RelProductive
            (Sigma : ExEnv)
    : Estate -> Eprogs -> Ensemble Estate -> Prop :=
  | RelP_Finish : forall Est Ec,
      (forall i, Vector.nth Ec i = CSkip)
      -> RelProductive Sigma Est Ec (Singleton _ Est)

    | RelP_SkipIntro : forall Est Q Ec Ec' i,
      (forall i', i <> i' -> Vector.nth Ec i' = Vector.nth Ec' i') ->
      Vector.nth Ec' i = CSeq (Vector.nth Ec i) CSkip ->
      RelProductive Sigma Est Ec' Q ->
      RelProductive Sigma Est Ec Q

  | RelP_Step :
      forall Est Q (R : Ensemble state) Ec Ec' i c1 c2,
        (forall i', i <> i' -> Vector.nth Ec i' = Vector.nth Ec' i') ->
        Vector.nth Ec i = CSeq c1 c2 ->
        Vector.nth Ec' i = c2 ->
        Productive Sigma c1 (nth Est i) R ->
        (forall st,
            R st ->
            RelProductive Sigma (replace Est i st) Ec' Q) ->
        RelProductive Sigma Est Ec Q

  | RelP_Weaken :
      forall Est Ec Q Q',
        RelProductive Sigma Est Ec Q ->
        Included _ Q Q' ->
        RelProductive Sigma Est Ec Q'.

  Theorem RelProductive_produces (Sigma : ExEnv)
  : forall (Est : Estate)
           (Ec : Eprogs)
           (Q : Ensemble Estate),
      RelProductive Sigma Est Ec Q ->
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
    - destruct IHRelProductive as [Est' [exe QEst] ].
      assert (forall (i' : Fin.t m), AllEnv |- nth Est i' =[ nth Ec i' ]=> nth Est' i')
        as exe'.
      { intros; destruct (Fin.eq_dec i i'); subst.
        + specialize (exe i'); rewrite H0 in exe.
          inversion exe; subst.
          inversion H7; subst; eauto.
        + rewrite H; eauto.
      }
      eauto.
    - eapply productive_com_produces in H2; destruct H2 as [st' [exe' R_st'] ].
      destruct (H4 _ R_st') as [Est' [exes' Q_exes'] ].
      eexists Est'.
      assert (forall (i' : Fin.t m), AllEnv |- nth Est i' =[ nth Ec i' ]=> nth Est' i'); eauto.
      { intros; destruct (Fin.eq_dec i i'); subst.
        + rewrite H0.
          econstructor; eauto.
          specialize (exes' i'); rewrite vector_nth_replace in exes'; eauto.
        + rewrite H; eauto.
          specialize (exes' i'); rewrite vector_nth_replace' in exes'; eauto.
      }
    - destruct IHRelProductive as [Est' [exes' Q_exes'] ].
      eexists Est', exes'.
      eapply H0; eauto.
  Qed.

  Theorem productive_Env_produces (Sigma : ExEnv)
      : forall (Est : Estate)
               (Ec : Eprogs)
               (Q : Ensemble Estate),
      productive_Env Sigma ->
      RelProductive {| AllEnv := {|
                                  funSigs := funSigs;
                                  funSpecs := funSpecs;
                                  funDefs := empty |};
                       funExSpecs := funExSpecs |} Est Ec Q ->
      RelProductive Sigma Est Ec Q.
  Proof.
    induction 2; intros; try (solve [econstructor; eauto]).
    eapply RelP_Step; eauto using productive_Env_produces.
  Qed.

  Theorem rhle_proof_RelProductive Sigs Sigma ESigma
          (Cons_Env : Consistent_Env {| AllEnv := {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |}; funExSpecs := ESigma |})
    : forall P Uc Ec Q,
      rhle_proof Sigma ESigma P Uc Ec Q ->
      forall (Ust Ust' : Ustate)
             (Est : Estate),
        (forall (i : Fin.t n),
            {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |}
            |- Vector.nth Ust i =[ Vector.nth Uc i ]=> Vector.nth Ust' i) ->
        P Ust Est ->
        RelProductive {| AllEnv := {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |}; funExSpecs := ESigma |} Est Ec (Q Ust').
  Proof.
    intros ? ? ? ? pf.
    induction pf; intros Ust Ust' Est exe HP.
    - assert (Ust' = Ust).
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
      eapply RelP_Weaken.
      econstructor; eauto.
      unfold Included, Ensembles.In; intros Est' Inc_Est'; inversion Inc_Est'; subst; eauto.
    - eapply IHpf in HP; eauto.
      intros.
      destruct (Fin.eq_dec i i0); subst.
      + rewrite H0; eauto.
      + rewrite <- H by eauto.
        eapply exe.
    - eapply IHpf in HP; eauto.
      econstructor; eauto.
    - generalize (exe i); intros exe'.
      rewrite H0 in exe'; inversion exe'; subst.
      eapply IHpf with (Ust := (replace Ust i st')).
      + intros; destruct (Fin.eq_dec i i0); subst.
        * rewrite vector_nth_replace; eauto.
        * rewrite vector_nth_replace', <- H; eauto.
      + eapply (hoare_proof_sound _ _ _ _ _ (H2 Ust Est) _ _ H5); eauto.
    - assert (nth Est i = nth Est i /\ P Ust Est) as H3 by tauto.
      eapply RelP_Step; eauto.
      eapply @ehoare_proof_produces with (Sigma := {| AllEnv := {| funSigs := _ |} |});
        cbv beta; eauto using productive_empty.
      + simpl; eauto.
      + simpl; intros; eauto.
  Qed.

  Theorem rhle_proof_link
          {Sigma : ExEnv}
    : forall (P : RelAssertion)
             (Uc : Uprogs)
             (Ec : Eprogs)
             (Q : RelAssertion),
      productive_Env Sigma ->
      Consistent_Env Sigma ->
      safe_Env (@AllEnv Sigma) ->
      (forall i Ust Est, P Ust Est ->
                       @Safe {| funSigs := @funSigs (@AllEnv Sigma);
                                funSpecs := @funSpecs (@AllEnv Sigma);
                                funDefs := empty |} (Vector.nth Uc i) (Vector.nth Ust i)) ->
      rhle_proof (@funSpecs (@AllEnv Sigma)) funExSpecs P Uc Ec Q ->
      Sigma |= {{P}} Uc ~# Ec {[Q]}.
  Proof.
    unfold rhle_triple; intros.
    eapply (rhle_proof_RelProductive funSigs _ _ H0 _ _ _ _ H3) in H5;
      eauto using safe_Env_refine.
    eapply productive_Env_produces in H5; eauto.
    eapply RelProductive_produces in H5; eauto.
  Qed.

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
