Require Import
        Coq.Arith.Arith
        Coq.Sets.Ensembles
        Coq.micromega.Psatz
        Coq.Program.Tactics.

Require Import
        Common
        Maps
        FunImp
        HoareCommon
        Hoare
        Productive
        HLE.

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
            hle_proof ESigma (fun st =>
                                 Vector.nth Est i = st /\
                                 P Ast Est) c1
                        (fun st => R Ast (replace Est i st))) ->

        rhle_proof Sigma ESigma R Uc Ec' Q ->
        rhle_proof Sigma ESigma P Uc Ec Q

(*  | RHE_StepIfL :
      forall P Q Uc Ec Uct Uce i b ct ce c2,
        (forall i', i <> i' -> Vector.nth Uc i' = Vector.nth Uce i') ->
        (forall i', i <> i' -> Vector.nth Uc i' = Vector.nth Uct i') ->
        Vector.nth Uc i = CSeq (CIf b ct ce) c2 ->
        Vector.nth Uct i = CSeq ct c2 ->
        Vector.nth Uce i = CSeq ce c2 ->
        rhle_proof Sigma ESigma (fun Ast Est => P Ast Est /\ bassn b (Vector.nth Ast i)) Uct Ec Q ->
        rhle_proof Sigma ESigma (fun Ast Est => P Ast Est /\ ~ bassn b (Vector.nth Ast i)) Uce Ec Q ->
        rhle_proof Sigma ESigma P Uc Ec Q

  | RHE_StepIfR :
      forall P Q Uc Ec Ect Ece i b ct ce c2,
        (forall i', i <> i' -> Vector.nth Ec i' = Vector.nth Ece i') ->
        (forall i', i <> i' -> Vector.nth Ec i' = Vector.nth Ect i') ->
        Vector.nth Ec i = CSeq (CIf b ct ce) c2 ->
        Vector.nth Ect i = CSeq ct c2 ->
        Vector.nth Ece i = CSeq ce c2 ->
        rhle_proof Sigma ESigma (fun Ast Est => P Ast Est /\ bassn b (Vector.nth Est i)) Uc Ect Q ->
        rhle_proof Sigma ESigma (fun Ast Est => P Ast Est /\ ~ bassn b (Vector.nth Est i)) Uc Ece Q ->
        rhle_proof Sigma ESigma P Uc Ec Q

  | RHE_StepAll :
      forall P Q R Uc Ec Uc1 Uc2 Ec1 Ec2,
        (forall i, Vector.nth Uc i = CSeq (Vector.nth Uc1 i) (Vector.nth Uc2 i)) ->
        (forall i, Vector.nth Ec i = CSeq (Vector.nth Ec1 i) (Vector.nth Ec2 i)) ->
        rhle_proof Sigma ESigma P Uc1 Ec1 R ->
        rhle_proof Sigma ESigma R Uc2 Ec2 Q ->
        rhle_proof Sigma ESigma P Uc Ec Q *)


  where "Sigma , ESigma |- {{ P }}  c1 ~# c2  {[ Q ]}" := (rhle_proof Sigma ESigma P c1 c2 Q) : hoare_spec_scope.

  Hint Resolve bassn_eval_true bassn_eval_false : hoare.
  Hint Constructors rhle_proof : hoare.
  Hint Unfold rhle_triple hoare_triple hle_triple.
  Hint Constructors ceval.

  (*Lemma ceval_Ex_single_step :
    forall Sigma i Ec c' (Est : Estate) Q,
      (forall R, ceval_Ex Sigma (Vector.nth Ec i) (Vector.nth Est i) R ->
                 ceval_Ex Sigma c' (Vector.nth Est i) R) ->
      Relceval_Ex _ Sigma Est (Vector.replace Ec i c') Q ->
      Relceval_Ex _ Sigma Est Ec Q.
  Proof.
    intros.
    replace Ec with (replace (replace Ec i c') i (nth Ec i)).
    - generalize (replace Ec i c') H0; clear H0; intros t H0.
      revert H; induction H0.
      + admit.
      +
  Admitted. *)

  Theorem rhle_proof_Relceval_Ex Sigs Sigma ESigma
    : forall P Uc Ec Q,
      rhle_proof Sigma ESigma P Uc Ec Q ->
      forall (Ust Ust' : Ustate)
             (Est : Estate),
        (forall (i : Fin.t n),
            {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |}
            |- Vector.nth Ust i =[ Vector.nth Uc i ]=> Vector.nth Ust' i) ->
        P Ust Est ->
        Relceval_Ex _ {| AllEnv := {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |}; funExSpecs := ESigma |} Est Ec (Q Ust').
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
      eapply @hle_proof_sound with (Sigma := {| AllEnv := {| funSigs := _ |} |});
        cbv beta; eauto using productive_empty.
      + simpl; eauto.
      + simpl; intros; eauto.
    (*- destruct (beval (Vector.nth Ust i) b) eqn: ?.
      + eapply IHpf1; eauto.
        intros.
        destruct (Fin.eq_dec i i0); subst.
        * specialize (exe i0); rewrite H1 in exe;
            inversion exe; subst.
          inversion H6; subst; try congruence.
          rewrite H2; eauto.
        * rewrite <- H0 by eauto; eapply exe.
      + eapply IHpf2; intuition eauto.
        intros.
        destruct (Fin.eq_dec i i0); subst.
        * specialize (exe i0); rewrite H1 in exe;
            inversion exe; subst.
          inversion H6; subst; try congruence.
          rewrite H3; eauto.
        * rewrite <- H by eauto; eapply exe.
        * rewrite bassn_eval_false in Heqb0; tauto.
    - destruct (beval (Vector.nth Est i) b) eqn: ?.
      + eapply ceval_Ex_single_step with (i := i) (c' := CSeq ct c2).
        * rewrite H1. revert Heqb0.
          clear.
          remember ((TEST b THEN ct ELSE ce FI);; c2)%imp; intros.
          revert b ct ce Heqb0 Heqc; induction H; intros; try discriminate.
          -- injections.
             econstructor; eauto.
             revert H Heqb0; clear.
             remember (TEST b THEN ct ELSE ce FI)%imp.
             intro; revert b ct ce Heqc; induction H; try discriminate; intros.
             ++ injections; eauto.
             ++ congruence.
             ++ econstructor; eauto.
          -- eapply ceval_Ex_Weaken; eauto.
        * replace ((replace Ec i (ct;; c2)%imp)) with Ect; eauto.
          rewrite <- H2.
          eapply eq_nth_iff.
          intros; destruct (Fin.eq_dec i p1); subst.
          -- rewrite vector_nth_replace; eauto.
          -- rewrite vector_nth_replace'; eauto.
             rewrite <- H0; eauto.
      + eapply ceval_Ex_single_step with (i := i) (c' := CSeq ce c2).
        * rewrite H1. revert Heqb0.
          clear.
          remember ((TEST b THEN ct ELSE ce FI);; c2)%imp; intros.
          revert b ct ce Heqb0 Heqc; induction H; intros; try discriminate.
          -- injections.
             econstructor; eauto.
             revert H Heqb0; clear.
             remember (TEST b THEN ct ELSE ce FI)%imp.
             intro; revert b ct ce Heqc; induction H; try discriminate; intros.
             ++ congruence.
             ++ injections; eauto.
             ++ econstructor; eauto.
          -- eapply ceval_Ex_Weaken; eauto.
        * replace ((replace Ec i (ce;; c2)%imp)) with Ece; eauto.
          eapply IHpf2; intuition eauto.
          -- rewrite bassn_eval_false in Heqb0; tauto.
          -- eapply eq_nth_iff.
             intros; destruct (Fin.eq_dec i p1); subst.
             ++ rewrite vector_nth_replace; eauto.
             ++ rewrite vector_nth_replace'; eauto.
                rewrite <- H; eauto.
    - generalize P Q R Ec Uc1 Uc2 Ec1 Ec2 H H0 IHpf1 IHpf2 Ust Ust' Est exe HP; clear.
      revert Uc.
      unfold RelAssertion, Ustate, Estate.
      induction n.
      + intro; pattern Uc; eapply VectorDef.case0; intros.
        admit.
      + intro; pattern Uc; eapply VectorDef.caseS with (v := Uc); simpl; intros.*)

  Qed.

  Theorem rhle_proof_refine
          {Sigma : ExEnv}
          (Complete_Env : forall f, exists fd,  @funDefs (@AllEnv Sigma) f = Some fd)
    : forall (P : RelAssertion)
             (Uc : Uprogs)
             (Ec : Eprogs)
             (Q : RelAssertion),
      ex_compatible_env Sigma ->
      compatible_env (@AllEnv Sigma) ->
      rhle_proof (@funSpecs (@AllEnv Sigma)) funExSpecs P Uc Ec Q ->
      Sigma |= {{P}} Uc ~# Ec {[Q]}.
  Proof.
    unfold rhle_triple; intros.
    eapply (rhle_proof_Relceval_Ex funSigs _ _ _ _ _ _ H1) in H3;
      eauto using compatible_Env_refine.
    eapply Relceval_Ex_strong in H3; eauto.
    eapply Relceval_Ex_sufficient in H3; eauto.
  Qed.

End RHLE.

Notation "Sigma |= {{ P }}  c1 ~# c2  {[ Q ]}" :=
  (rhle_triple Sigma P c1 c2 Q) (at level 90, c1 at next level, c2 at next level)
  : hoare_spec_scope.

Notation "Sigma |- {{ P }}  c1 ~# c2  {[ Q ]}" :=
  (rhle_proof Sigma P c1 c2 Q) (at level 90, c1 at next level, c2 at next level)
  : hoare_spec_scope.
