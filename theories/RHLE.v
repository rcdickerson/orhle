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


  where "Sigma , ESigma |- {{ P }}  c1 ~# c2  {[ Q ]}" := (rhle_proof Sigma ESigma P c1 c2 Q) : hoare_spec_scope.

  #[local] Hint Resolve bassn_eval_true bassn_eval_false : hoare.
  Hint Constructors rhle_proof : hoare.
  #[local] Hint Unfold rhle_triple hoare_triple hle_triple : hoare.
  Hint Constructors ceval : core.

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
