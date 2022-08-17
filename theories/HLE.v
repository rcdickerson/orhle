Require Import
        Coq.Arith.Arith
        Coq.micromega.Psatz
        Coq.Sets.Ensembles
        Coq.Logic.Classical
        Coq.Program.Tactics.

Require Import
        Common
        Maps
        FunImp
        HoareCommon
        Fixpoints
        Productive.

Section HLE.

  Reserved Notation "Sigma |- {[ P ]}  c  {[ Q ]}#"
           (at level 40, c at next level).

  Inductive hle_proof (Sigma : total_map funExSpec)
    : Assertion -> com -> Assertion -> Prop :=
  | EH_Skip : forall P,
      Sigma |- {[P]} SKIP {[P]}#
  | EH_Asgn : forall Q V a,
      Sigma |- {[Q[V |-> a]]} V ::= a {[Q]}#
  | EH_Havoc : forall Q V,
      Sigma |- {[fun st => exists n : nat, Q[V |-> n] st]} (CHavoc V) {[Q]}#
  | EH_Seq  : forall P c Q d R,
      Sigma |- {[P]} c {[Q]}# ->
      Sigma |- {[Q]} d {[R]}# ->
      Sigma |- {[P]} c;;d {[R]}#
  | EH_If : forall P Q b c1 c2,
      Sigma |- {[fun st => P st /\ bassn b st]} c1 {[Q]}# ->
      Sigma |- {[fun st => P st /\ ~(bassn b st)]} c2 {[Q]}# ->
               Sigma |- {[P]} TEST b THEN c1 ELSE c2 FI {[Q]}#
  | EH_While : forall {A : Type} (R : A -> A -> Prop) M P b c,
      well_founded R ->
      (forall (a : A),
          Sigma |- {[fun st => P st /\ bassn b st /\ M a st]} c {[fun st => P st /\ exists a', M a' st /\ R a' a]}#) ->
      Sigma |- {[fun st => P st /\ exists a, M a st]} WHILE b DO c END {[fun st => P st /\ ~ (bassn b st)]}#
  | EH_Consequence  : forall (P Q P' Q' : Assertion) c,
      Sigma |- {[P']} c {[Q']}# ->
      (forall st, P st -> P' st) ->
      (forall st, Q' st -> Q st) ->
      Sigma |- {[P]} c {[Q]}#

  | EH_Spec : forall Q y f xs,
      Sigma |- {[fun st =>
                   exists i,
                   (exists inits,
                       exists returns,
                         (Sigma f).(preEx) (Vector.replace inits i (aseval st xs)) /\
                         (Sigma f).(postEx) (Vector.replace inits i (aseval st xs))
                                                         returns) /\
                   forall inits returns,
                     (Sigma f).(preEx) (Vector.replace inits i (aseval st xs)) ->
                     (Sigma f).(postEx) (Vector.replace inits i (aseval st xs))
                                                        returns ->
                               Q[y |-> Vector.nth returns i] st]} y :::= f $ xs {[Q]}#

  where "Sigma |- {[ P ]}  c  {[ Q ]}#" := (hle_proof Sigma P c Q) : hoare_spec_scope.

  Definition hle_triple
             (ESigma : ExEnv)
             (P : Assertion)
             (c : com)
             (Q : Assertion) : Prop :=
    forall st,
      P st ->
      ceval_Ex ESigma c st Q.

  Notation "ESigma |= {[ P ]}  c  {[ Q ]}#" :=
    (hle_triple ESigma P c Q) (at level 90, c at next level)
    : hoare_spec_scope.

  Hint Resolve bassn_eval_true bassn_eval_false : hoare.
  Hint Constructors hle_proof : hoare.
  Hint Constructors ceval.

  Local Hint Constructors ceval.
  Local Hint Constructors AppearsIn.

  Hint Constructors ceval_Ex : hoare.

  Theorem hle_proof_sound {Sigma : ExEnv}
    : forall (P Q : Assertion) c,
      ex_compatible_env Sigma ->
      funExSpecs |- {[P]} c {[Q]}# ->
      forall st,
        P st ->
        ceval_Ex {| AllEnv := {| funSigs := @funSigs AllEnv;
                                   funSpecs := @funSpecs AllEnv;
                                   funDefs := empty |};
                      funExSpecs := funExSpecs |} c st Q.
  Proof.
    induction 2; intros; eauto.
    - eapply ceval_Ex_Weaken; try solve [econstructor; eauto].
      unfold Included, In; intros; inversion H1; subst; eauto.
    - eapply ceval_Ex_Weaken; try solve [econstructor].
      unfold Included, In; intros; inversion H1; subst; eauto.
    - destruct H0.
      eapply ceval_Ex_Weaken; try solve [econstructor; eauto].
      instantiate (1 := x).
      unfold Included, In; intros; inversion H1; subst; eauto.
    - eapply ceval_Ex_Weaken; try solve [econstructor; eauto].
      firstorder.
    - destruct (beval st b) eqn:?.
      + eapply ceval_Ex_Weaken; try solve [econstructor; eauto].
        firstorder.
      + eapply ceval_Ex_Weaken.
        * eapply ceval_Ex_IfFalse; firstorder eauto.
          eapply IHhle_proof2; firstorder eauto with hoare.
          eapply bassn_eval_false; eauto.
        * firstorder.
    - destruct H3 as [P_st [a M'] ].
      revert dependent st.
      induction a as [a IH] using (well_founded_ind H0). intros.
      destruct (beval st b) eqn:?.
      + econstructor; eauto; intros.
        destruct H3 as [P_st' [a' [M_a' lt_a'] ] ]; eauto.
      + eapply ceval_Ex_Weaken; eauto using ceval_Ex_WhileFalse.
        unfold Included, Ensembles.In; intros.
        inversion H3; subst; intuition.
        eapply bassn_eval_false; eauto.
    - eapply ceval_Ex_Weaken; eauto.
    - destruct H0 as [i [ [inits [returns [? ?] ] ] ? ] ].
      eapply ceval_Ex_Weaken; eauto.
      + (*specialize (consistent_Sigma f);
          destruct consistent_Sigma as [pre_f post_f]. *)
        eapply ceval_Ex_CallSpec; firstorder eauto.
        * eapply vector_nth_replace.
      + unfold Included, Ensembles.In; intros.
        destruct H3 as [v0 [? [? [? [? ?] ] ] ] ].
        subst.
        eapply (H2 v0 x0).
        rewrite <- H5, vector_replace_nth_id; eauto.
        rewrite <- H5, vector_replace_nth_id; eauto.
  Qed.

  Theorem hle_proof_very_sound {Sigma : ExEnv}
          (Complete_Env : forall f, exists fd,  @funDefs (@AllEnv Sigma) f = Some fd) :
    forall (P Q : Assertion) c,
      ex_compatible_env Sigma ->
      Consistent_Env Sigma ->
      funExSpecs |- {[P]} c {[Q]}# ->
      forall st, P st
                 -> exists st' (exe : (AllEnv) |- st =[c]=> st'), Q st'.
  Proof.
    unfold hle_triple; intros.
    eapply (hle_proof_sound _ _ _ H H1) in H2.
    eapply productive_strong in H2; eauto.
    eapply productive_sufficient; eauto.
  Qed.

  Print Assumptions hle_proof_very_sound.


 Lemma Empty_PreCondition :
    forall Sigma c Q,
        Sigma |- {[fun _ : state => False]} c {[Q]}#.
  Proof.
    induction c.
    - intros; econstructor; intuition eauto; econstructor.
    - intros; econstructor; intuition eauto; econstructor.
    - intros; econstructor; intuition eauto; econstructor.
    - intros; econstructor.
      eapply EH_Spec.
      intros; intuition eauto.
      eauto.
    - econstructor; eauto.
    - econstructor; eauto.
      + econstructor; intuition eauto.
      + econstructor; intuition eauto.
    - intros; econstructor.
      econstructor.
      apply lt_wf.
      econstructor.
      eapply IHc.
      instantiate (1 := fun _ _ => False).
      intros ? [? [? ?] ].
      apply H.
      intros.
      split; try eapply H.
      intuition.
      intuition.
      simpl; intuition eauto.
      simpl; intuition eauto.
  Qed.

Section HLEPlus.
  (* Proof that the EH_SpecK' rule is admissible. *)
  Inductive hle_proof' (Sigma : total_map funExSpec)
    : Assertion -> com -> Assertion -> Prop :=
  | EH_Skip' : forall P,
      Sigma |- {[P]} SKIP {[P]}#
  | EH_Asgn' : forall Q V a,
      Sigma |- {[Q[V |-> a]]} V ::= a {[Q]}#
  | EH_Havoc' : forall Q V,
      Sigma |- {[fun st => exists n : nat, Q[V |-> n] st]} (CHavoc V) {[Q]}#
  | EH_Seq'  : forall P c Q d R,
      Sigma |- {[P]} c {[Q]}# ->
      Sigma |- {[Q]} d {[R]}# ->
      Sigma |- {[P]} c;;d {[R]}#
  | EH_If' : forall P Q b c1 c2,
      Sigma |- {[fun st => P st /\ bassn b st]} c1 {[Q]}# ->
      Sigma |- {[fun st => P st /\ ~(bassn b st)]} c2 {[Q]}# ->
               Sigma |- {[P]} TEST b THEN c1 ELSE c2 FI {[Q]}#
  | EH_While' : forall {A : Type} (R : A -> A -> Prop) M P b c,
      well_founded R ->
      (forall (a : A),
          Sigma |- {[fun st => P st /\ bassn b st /\ M a st]} c {[fun st => P st /\ exists a', M a' st /\ R a' a]}#) ->
      Sigma |- {[fun st => P st /\ exists a, M a st]} WHILE b DO c END {[fun st => P st /\ ~ (bassn b st)]}#
  | EH_Consequence'  : forall (P Q P' Q' : Assertion) c,
      Sigma |- {[P']} c {[Q']}# ->
      (forall st, P st -> P' st) ->
      (forall st, Q' st -> Q st) ->
      Sigma |- {[P]} c {[Q]}#

  | EH_Spec' : forall Q y f xs,
      Sigma |- {[fun st =>
                   exists i,
                   (exists inits,
                       exists returns,
                         (Sigma f).(preEx) (Vector.replace inits i (aseval st xs)) /\
                         (Sigma f).(postEx) (Vector.replace inits i (aseval st xs))
                                                         returns) /\
                   forall inits returns,
                     (Sigma f).(preEx) (Vector.replace inits i (aseval st xs)) ->
                     (Sigma f).(postEx) (Vector.replace inits i (aseval st xs))
                                                        returns ->
                               Q[y |-> Vector.nth returns i] st]} y :::= f $ xs {[Q]}#
  | EH_SpecK'
    : forall Q y f xs i,
      Sigma |- {[fun st =>
                   (exists inits,
                       exists returns,
                         (Sigma f).(preEx) (Vector.replace inits i (aseval st xs)) /\
                         (Sigma f).(postEx) (Vector.replace inits i (aseval st xs))
                                            returns) /\
                   forall inits returns,
                     (Sigma f).(preEx) (Vector.replace inits i (aseval st xs)) ->
                     (Sigma f).(postEx) (Vector.replace inits i (aseval st xs))
                                        returns ->
                     Q[y |-> Vector.nth returns i] st]} y :::= f $ xs {[Q]}#
  where "Sigma |- {[ P ]}  c  {[ Q ]}#" := (hle_proof' Sigma P c Q) : hoare_spec'_scope.

  Lemma EH_SpecK'_Admissible Sigma :
    forall P c Q,
      hle_proof Sigma P c Q <-> hle_proof' Sigma P c Q.
  Proof.
    split; induction 1; try solve [econstructor; eauto].
    - eapply EH_Consequence.
    eapply EH_Spec.
    2: eauto.
    simpl; intros.
    eexists i; eauto.
  Qed.

End HLEPlus.

End HLE.

Notation "Sigma |= {[ P ]}  c  {[ Q ]}#" :=
  (hle_triple Sigma P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Notation "Sigma |- {[ P ]}  c  {[ Q ]}#" :=
  (hle_proof Sigma P c Q) (at level 90, c at next level)
  : hoare_spec_scope.
