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

Definition BinAssertion := state -> state -> Prop.

Definition relAssert_implies (P Q : BinAssertion) : Prop :=
  forall (st : state)
         (st' : state),
    P st st' -> Q st st'.

Section RHLE.

  Definition Ustate := state.
  Definition Estate := state.

  Definition Uprogs := com.
  Definition Eprogs := com.

  Definition rhle_triple
             (Sigma : ExEnv)
             (P : BinAssertion)
             (Uc : Uprogs)
             (Ec : Eprogs)
             (Q : BinAssertion) : Prop :=
    forall (Ust Ust' : Ustate)
           (Est : Estate),
      AllEnv |- Ust =[ Uc ]=> Ust' ->
      P Ust Est ->
      exists Est' (exe : AllEnv |- Est =[ Ec ]=> Est'), Q Ust' Est'.

  Notation "Sigma |= {{ P }}  c1 ~# c2  {[ Q ]}" :=
    (rhle_triple Sigma P c1 c2 Q) (at level 90, c1 at next level, c2 at next level)
    : hoare_spec_scope.

  Reserved Notation "Sigma , ESigma |- {{ P }}  c1 ~# c2  {[ Q ]}"
           (at level 40, c1 at next level, c2 at next level).

  Inductive rhle_proof Sigma ESigma
    : BinAssertion -> Uprogs -> Eprogs -> BinAssertion -> Prop :=
  | RHE_Skip : forall P Uc Ec,
      (Uc = CSkip)
      -> (Ec = CSkip)
      -> rhle_proof Sigma ESigma P Uc Ec P

  | RHE_SkipIntroL : forall P Q Uc Ec Uc',
      Uc' = CSeq Uc CSkip ->
      rhle_proof Sigma ESigma P Uc' Ec Q ->
      rhle_proof Sigma ESigma P Uc Ec Q

  | RHE_SkipIntroR : forall P Q Uc Ec Ec',
      Ec' = CSeq Ec CSkip ->
      rhle_proof Sigma ESigma P Uc Ec' Q ->
      rhle_proof Sigma ESigma P Uc Ec Q

  | RHE_StepL :
      forall P Q R Uc Ec Uc' c1 c2,
        Uc = CSeq c1 c2 ->
        Uc' = c2 ->
        (forall Est,
            hoare_proof Sigma (fun st => P st Est) c1
                        (fun st => R st Est)) ->
        rhle_proof Sigma ESigma R Uc' Ec Q ->
        rhle_proof Sigma ESigma P Uc Ec Q

  | RHE_StepR :
      forall P Q R Uc Ec Ec' c1 c2,
        Ec = CSeq c1 c2 ->
        Ec' = c2 ->
        (forall Ast,
            hle_proof ESigma (fun st => P Ast st) c1
                        (fun st => R Ast st)) ->

        rhle_proof Sigma ESigma R Uc Ec' Q ->
        rhle_proof Sigma ESigma P Uc Ec Q

  | RHE_StepIfL :
      forall P Q Uc Ec Uct Uce b ct ce c2,
        Uc = CSeq (CIf b ct ce) c2 ->
        Uct = CSeq ct c2 ->
        Uce = CSeq ce c2 ->
        rhle_proof Sigma ESigma (fun Ast Est => P Ast Est /\ bassn b Ast) Uct Ec Q ->
        rhle_proof Sigma ESigma (fun Ast Est => P Ast Est /\ ~ bassn b Ast) Uce Ec Q ->
        rhle_proof Sigma ESigma P Uc Ec Q

  | RHE_StepIfR :
      forall P Q Uc Ec Ect Ece b ct ce c2,
        Ec = CSeq (CIf b ct ce) c2 ->
        Ect = CSeq ct c2 ->
        Ece = CSeq ce c2 ->
        rhle_proof Sigma ESigma (fun Ast Est => P Ast Est /\ bassn b Est) Uc Ect Q ->
        rhle_proof Sigma ESigma (fun Ast Est => P Ast Est /\ ~ bassn b Est) Uc Ece Q ->
        rhle_proof Sigma ESigma P Uc Ec Q

  | RHE_StepAll :
      forall P Q R Uc Ec Uc1 Uc2 Ec1 Ec2,
        Uc = CSeq Uc1 Uc2 ->
        Ec = CSeq Ec1 Ec2 ->
        rhle_proof Sigma ESigma P Uc1 Ec1 R ->
        rhle_proof Sigma ESigma R Uc2 Ec2 Q ->
        rhle_proof Sigma ESigma P Uc Ec Q

  | RHE_FuseLoops :
      forall (Q I : BinAssertion) Uc Ec Ub Uc' Eb Ec',
        Uc = CWhile Ub Uc' ->
        Ec = CWhile Eb Ec' ->
        (forall Ust Est, I Ust Est /\ ~ bassn Ub Ust /\ ~ bassn Eb Est -> Q Ust Est) ->
        (forall Ust Est, I Ust Est /\ ~ bassn Ub Ust -> ~ bassn Eb Est) ->
        (forall Ust Est, I Ust Est /\ ~ bassn Eb Est -> ~ bassn Ub Ust) ->
        rhle_proof Sigma ESigma (fun Ust Est => I Ust Est /\ bassn Ub Ust) Uc' Ec' I ->
        rhle_proof Sigma ESigma I  Uc Ec Q

  where "Sigma , ESigma |- {{ P }}  c1 ~# c2  {[ Q ]}" := (rhle_proof Sigma ESigma P c1 c2 Q) : hoare_spec_scope.

  #[local] Hint Resolve bassn_eval_true bassn_eval_false : hoare.
  Hint Constructors rhle_proof : hoare.
  Hint Unfold rhle_triple hoare_triple hle_triple : hoare.
  Hint Constructors ceval : core.

  Lemma ceval_Ex_single_step' :
    forall Sigma c' (Est : Productive.Estate 1) Q,
      Relceval_Ex _ Sigma Est c' Q ->
      ceval_Ex Sigma (Vector.nth c' Fin.F1) (Vector.nth Est Fin.F1)  (fun Est' => Q (Vector.cons _ Est' _ (Vector.nil _))).
  Proof.
    intros.
    induction H.
    - specialize (H Fin.F1); simpl in H; subst.
      rewrite H.
      econstructor.
      econstructor.
      unfold Included, In; intros; inversion H0; subst.
      pattern Est; eapply Vector.caseS'; simpl; intros.
      pattern t; eapply Vector.case0; simpl;
      econstructor.
    - generalize dependent i; intro i; pattern i; eapply @Fin.caseS' with (n := 0); simpl; intros.
      + rewrite H0 in IHRelceval_Ex.
        revert IHRelceval_Ex; clear.
        remember (Vector.nth Ec Fin.F1;; SKIP)%imp; remember (Vector.nth Est Fin.F1).
        induction 1; try congruence.
        * injections.
          econstructor.
          eauto.
          unfold Included, In; intros.
          eapply H in H1.
          revert H1; clear; remember CSkip; induction 1; try congruence; eauto.
          econstructor.
          eapply H; eapply IHceval_Ex; eauto.
        * econstructor; eauto.
      + eapply Fin.case0; eauto.
    - subst.
      generalize dependent i; intro i; pattern i; eapply @Fin.caseS' with (n := 0); simpl; intros.
      + generalize dependent Est; intro; pattern Est; eapply Vector.caseS'; simpl.
        rewrite H0.
        econstructor; eauto; intros.
      + eapply Fin.case0; eauto.
    - econstructor; eauto.
      unfold Included, In; intros.
      eapply H0; eapply H1.
  Qed.

  Lemma ceval_Ex_single_step :
    forall Sigma Ec c' (Est : Estate) Q,
      (forall R, ceval_Ex Sigma c' Est R ->
                 ceval_Ex Sigma Ec Est R) ->
      Relceval_Ex _ Sigma (Vector.cons _ Est _ (Vector.nil _)) (Vector.cons _ c' _ (Vector.nil _)) Q ->
      Relceval_Ex _ Sigma (Vector.cons _ Est _ (Vector.nil _))  (Vector.cons _ Ec _ (Vector.nil _)) Q.
  Proof.
    intros.
    intros; eapply ceval_Ex_single_step' in H0.
    eapply H in H0.
    eapply RelP_SkipIntro with (i := Fin.F1) (Ec' := Vector.cons _ (CSeq _ _) _ (Vector.nil _)); simpl; eauto.
    - intro i'; pattern i'; eapply @Fin.caseS' with (n := 0); simpl; intros.
      + elimtype False; eapply H1; eauto.
      + eapply Fin.case0; eauto.
    - eapply RelP_Step with (i := Fin.F1) (Ec' := Vector.cons _ CSkip _ (Vector.nil _)); simpl; eauto.
      intro; pattern i'; eapply @Fin.caseS' with (n := 0); simpl; intros.
      + elimtype False; eapply H1; eauto.
      + eapply Fin.case0; eauto.
      + intros; eapply RelP_Weaken.
        econstructor.
        * intro i'; pattern i'; eapply @Fin.caseS' with (n := 0); simpl; intros; eauto.
          eapply Fin.case0; eauto.
        * unfold Included, In in *; intros; eauto.
          inversion H2; subst; eauto.
  Qed.

  Theorem rhle_proof_Relceval_Ex Sigs Sigma ESigma
    : forall P Uc Ec Q,
      rhle_proof Sigma ESigma P Uc Ec Q ->
      forall (Ust Ust' : Ustate)
             (Est : Estate),
        ( {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |}
            |- Ust =[ Uc ]=> Ust') ->
        P Ust Est ->
        Relceval_Ex _ {| AllEnv := {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |}; funExSpecs := ESigma |} (Vector.cons _ Est _ (Vector.nil _)) (Vector.cons _ Ec _ (Vector.nil _ )) (fun Est => Q Ust' (Vector.hd Est)).
  Proof.
    intros ? ? ? ? pf.
    induction pf; intros Ust Ust' Est exe HP.
    - subst.
      eapply RelP_Weaken.
      + econstructor; eauto.
        intro; pattern i; eapply @Fin.caseS' with (n := 0).
        * reflexivity.
        * eapply Fin.case0.
      + unfold Included, Ensembles.In; intros Est' Inc_Est'; inversion Inc_Est'; subst; eauto.
        inversion exe; subst; simpl; eauto.
    - eapply IHpf in HP; eauto.
      intros; subst.
      econstructor; eauto.
    - eapply IHpf in HP; eauto.
      eapply RelP_SkipIntro with (i := Fin.F1) (Ec' := Vector.cons _ Ec' _ (Vector.nil _)); eauto.
      + intro; pattern i'; eapply Fin.caseS'; try congruence.
        intro; apply Fin.case0; eauto.
    - subst; inversion exe; subst.
      eapply IHpf with (Ust := st'); eauto.
      + eapply (hoare_proof_sound _ _ _ _ _ (H1 Est) _ _ H2); eauto.
    - specialize (H1 Ust); subst.
      eapply @hle_proof_sound with (Sigma := {| AllEnv := {| funSigs := _ |} |}) (P := fun Est => P Ust Est) in HP;
        eauto using productive_empty.
      eapply RelP_Step with (i := Fin.F1) (Ec' := (Vector.cons _ c2 _ _)); simpl; eauto.
      + intro; pattern i'; eapply Fin.caseS'; try congruence.
        intro; apply Fin.case0; eauto.
      + simpl in *; eauto.
    - destruct (beval Ust b) eqn: ?.
      + eapply IHpf1; subst; eauto.
        inversion exe; subst.
        inversion H1; subst; try congruence; eauto.
      + eapply IHpf2; subst; intuition eauto.
        inversion exe; subst.
        inversion H1; subst; try congruence; eauto.
        rewrite bassn_eval_false in Heqb0; tauto.
    - destruct (beval Est b) eqn: ?.
      + eapply IHpf1 with (Est := Est) in exe; try tauto.
        subst.
        eapply ceval_Ex_single_step with (c' := CSeq ct c2).
        * revert Heqb0.
          clear.
          remember (ct;; c2)%imp; intros.
          generalize H b ct ce Heqb0 Heqc; clear; intro; induction H; intros; try discriminate.
          -- injections.
             econstructor; eauto.
             revert H Heqb0; clear.
             econstructor; eauto.
          -- eapply ceval_Ex_Weaken; eauto.
        * eauto.
      + eapply IHpf2 with (Est := Est) in exe; try tauto.
        subst.
        eapply ceval_Ex_single_step with (c' := CSeq ce c2).
        * revert Heqb0.
          clear.
          remember (ce;; c2)%imp; intros.
          generalize H b ct ce Heqb0 Heqc; clear; intro; induction H; intros; try discriminate.
          -- injections.
             econstructor; eauto.
             revert H Heqb0; clear.
             intros; eapply ceval_Ex_IfFalse; eauto.
          -- eapply ceval_Ex_Weaken; eauto.
        * eauto.
        * intuition eauto using bassn_eval_false.
          rewrite bassn_eval_false in Heqb0; tauto.
    - subst; inversion exe; subst; clear exe.
      specialize (IHpf1 _ _ _ H1 HP).
      eapply RelP_Step with (i := Fin.F1) (Ec' := Vector.cons _ Ec2 _ _); simpl; eauto.
      + intro; pattern i'; eapply @Fin.caseS' with (n := 0); try congruence.
        intro; eapply Fin.case0; eauto.
      + revert IHpf1; clear.
        intro.
        assert (exists Q,
                   Relceval_Ex 1 {| AllEnv := {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |}; funExSpecs := ESigma |}
                               (Vector.cons Estate Est 0 (Vector.nil Estate)) (Vector.cons Eprogs Ec1 0 (Vector.nil Eprogs))
                               Q /\ Included _ Q (fun Est0 : Productive.Estate 1 => R st' (Vector.hd Est0))).
        eexists; split; eauto.
        unfold Included;  eauto.
        clear IHpf1; destruct H as [Q [? ?] ].
        remember (Vector.cons Estate Est 0 (Vector.nil Estate));
          remember (Vector.cons Eprogs Ec1 0 (Vector.nil Eprogs)).
        generalize H Est Ec1 R Heqt Heqt0 H0; clear; induction 1.
        * revert H; pattern Ec; eapply Vector.caseS';
            intros h t; pattern t; eapply VectorDef.case0.
          pattern Est; eapply Vector.caseS';
            intros h' t'; pattern t'; eapply VectorDef.case0; clear;
              intros; injections.
          specialize (H Fin.F1); simpl in H; rewrite H.
          econstructor.
          eapply ceval_Ex_Skip.
          unfold Included, Ensembles.In; intros Est' Inc_Est'; inversion Inc_Est'; subst; eauto.
          unfold Included in *.
          eapply (H0 (Vector.cons _ _ _ _)); unfold In; simpl; econstructor.
        * intros; subst.
          assert  (ceval_Ex
                    {|
                    AllEnv := {| funSigs := Sigs; funSpecs := Sigma; funDefs := empty |};
                    funExSpecs := ESigma |} (Ec1;; SKIP)%imp Est0 (R st')).
          eapply IHRelceval_Ex; eauto.
          revert H0; pattern Ec'; eapply Vector.caseS'; intros h t'; pattern t';
            eapply Vector.case0; pattern i; eapply Fin.caseS'; simpl; intros; subst; eauto.
          eapply Fin.case0; eauto.
          revert H3; clear; remember (Ec1;; SKIP)%imp; intro; revert Heqc; induction H3;
            intros; try discriminate.
          -- injections; econstructor; eauto.
             unfold Included, In; intros.
             eapply H in H1.
             revert H1; clear.
             remember CSkip; intro; revert Heqc; induction H1; intros; try discriminate.
             econstructor.
             eapply H; eapply IHceval_Ex; eauto.
          -- econstructor; eauto.
        * intros; subst.
          assert (Ec1 = (c1;; Vector.nth Ec' i)%imp).
          { revert H0; pattern i; eapply Fin.caseS'; simpl; eauto.
            intro; apply Fin.case0; eauto. }
          subst.
          revert H2; pattern i; eapply Fin.caseS'; simpl; intros; eauto.
          eapply ceval_Ex_Seq.
          eauto.
          intros.
          eapply H4; eauto.
          pattern i; eapply Fin.caseS'; simpl; intros; eauto.
          apply Fin.case0; eauto.
          pattern Ec'; eapply Vector.caseS';
            intros h t; pattern t; eapply VectorDef.case0.
          simpl; eauto.
          apply Fin.case0; eauto.
        * intros; subst.
          eapply IHRelceval_Ex; eauto.
          unfold Included in *; intros; eauto.
    - clear pf. revert Ec Eb Ec' Est H0 H1 H2 H3 HP IHpf; induction exe; intros; try congruence.
      eapply RelP_SkipIntro with (i := Fin.F1) (Ec := Vector.cons _ Ec _ _) (Ec' := Vector.cons _ _ _ (Vector.nil _)).
      + intro i.
        pattern i; eapply Fin.caseS'; simpl; intros; try discriminate.
        congruence.
        eapply Fin.case0; eauto.
      + simpl; reflexivity.
      + eapply RelP_Step with (i := Fin.F1) (Ec' := Vector.cons _ CSkip _ _); simpl; eauto.
        * intro i'.
          pattern i'; eapply Fin.caseS'; simpl; intros; try discriminate.
          congruence.
          eapply Fin.case0; eauto.
        * rewrite H1.
          apply ceval_Ex_WhileFalse.
          apply bassn_eval_false.
          injections.
          eapply H3; intuition eauto.
          eapply bassn_eval_false in H0; intuition.
        * intros.
          injections.
          eapply RelP_Weaken.
          eapply RelP_Finish.
          instantiate (1 := Vector.nil _).
          intro; pattern i; eapply Fin.caseS'; simpl; intros; eauto.
          apply Fin.case0; eauto.
          unfold Included, In; intros.
          eapply H2.
          inversion H; subst; simpl.
          inversion H5; subst; intuition.
          apply bassn_eval_false in H0; intuition.
          eapply H3; intuition eauto.
          apply bassn_eval_false in H0; intuition.
      + eapply ceval_Ex_single_step with (c' := CSeq Ec' (CWhile Eb Ec')).
        * subst.
          assert (beval Est Eb = true).
          { destruct (beval Est Eb) eqn: ?; eauto.
            injections.
            eapply bassn_eval_false in Heqb0.
            elimtype False; eapply H4; intuition eauto. }
            intuition.
            remember (Ec';; WHILE Eb DO Ec' END)%imp.
          revert Heqc0 H1 R H6; clear;
          intros Heqc0 H1 R H'; revert Heqc0 H1.
          induction H'; intros; try congruence; injections.
          -- econstructor; eauto.
          -- eapply ceval_Ex_Weaken; eauto.
        * eapply RelP_Step with (i := Fin.F1) (Ec' := Vector.cons _ (CWhile Eb Ec') _ _) (R := I st'); simpl; eauto.
          -- intro i'; pattern i'; eapply Fin.caseS'; simpl; intros; try congruence.
             apply Fin.case0; eauto.
          -- injections.
             intuition.
             assert (I st Est /\ bassn Ub st) by intuition.
             specialize (IHpf _ _ _ exe1 H1).
             eapply ceval_Ex_single_step' in IHpf.
             simpl in IHpf.
             eapply ceval_Ex_Weaken.
             eauto.
             unfold Included, In; intros; intuition.
  Qed.

  Theorem rhle_proof_refine
          {Sigma : ExEnv}
          (Complete_Env : forall f, exists fd,  @funDefs (@AllEnv Sigma) f = Some fd)
    : forall (P : BinAssertion)
             (Uc : Uprogs)
             (Ec : Eprogs)
             (Q : BinAssertion),
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
    destruct H3 as [? [? ?] ]; eauto.
    specialize (x0 Fin.F1); simpl in *; eauto.
    eexists _; eexists x0; eauto.
    revert H3; pattern x; apply Vector.caseS'; simpl; eauto.
  Qed.

End RHLE.

Notation "Sigma |= {{ P }}  c1 ~# c2  {[ Q ]}" :=
  (rhle_triple Sigma P c1 c2 Q) (at level 90, c1 at next level, c2 at next level)
  : hoare_spec_scope.

Notation "Sigma |- {{ P }}  c1 ~# c2  {[ Q ]}" :=
  (rhle_proof Sigma P c1 c2 Q) (at level 90, c1 at next level, c2 at next level)
  : hoare_spec_scope.
