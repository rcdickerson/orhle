Require Import
        Coq.Arith.Arith
        Coq.micromega.Psatz
        Coq.Program.Tactics.

Require Import Maps Imp.

Ltac inv_ceval :=
  let t H := (inversion H; subst; clear H) in
  match goal with
  | H : _ =[ SKIP ]=> _
                      |- _ => t H
  | H : _ =[ _;;_ ]=> _ |- _ => t H
  end.

Require Import HoareCommon Hoare EHoare.

Definition Assertion2 := state -> state -> Prop.

Definition assert2_implies (P Q : Assertion2) : Prop :=
  forall st st', P st st' -> Q st st'.

Section RHLE.

  Definition rhle_triple {env : Env}
             (P : Assertion2) (c1 : com) (c2 : com) (Q : Assertion2) : Prop :=
    forall st1 st2 st1',
      st1 =[ c1 ]=> st1'  ->
                    P st1 st2 ->
                    exists st2' (exe : st2 =[ c2 ]=> st2'), Q st1' st2'.

  Notation "{{ P }}  c1 ~# c2  {[ Q ]}" :=
    (rhle_triple P c1 c2 Q) (at level 90, c1 at next level, c2 at next level)
    : hoare_spec_scope.

  Reserved Notation "Sigma |- {{ P }}  c1 ~# c2  {[ Q ]}"
           (at level 90, c1 at next level, c2 at next level).

  Inductive rhle_proof Sigma : Assertion2 -> com -> com -> Assertion2 -> Prop :=
  | RHE_Skip : forall P,
      Sigma |- {{P}} SKIP ~# SKIP {[P]}
  | RHE_SkipIntroL : forall P Q c1 c2,
      Sigma |- {{P}} c1;;SKIP ~# c2 {[Q]} ->
      Sigma |- {{P}} c1 ~# c2 {[Q]}
  | RHE_SkipIntroR : forall P Q c1 c2,
      Sigma |- {{P}} c1 ~# c2;;SKIP {[Q]} ->
      Sigma |- {{P}} c1 ~# c2 {[Q]}
  | RHE_StepL : forall P Q R c1 c2 c3,
      (forall st2, Sigma |- {{fun st => P st st2}} c1 {{fun st => Q st st2}}) ->
      Sigma |- {{Q}} c2 ~# c3 {[R]} ->
      Sigma |- {{P}} c1;;c2 ~# c3 {[R]}
  | RHE_StepR : forall P Q R c1 c2 c3,
      (forall st1, Sigma |- {[fun st => P st1 st]} c2 {[fun st => Q st1 st]}#) ->
      Sigma |- {{Q}} c1 ~# c3 {[R]} ->
      Sigma |- {{P}} c1 ~# c2;;c3 {[R]}

  where "Sigma |- {{ P }}  c1 ~# c2  {[ Q ]}" := (rhle_proof Sigma P c1 c2 Q) : hoare_spec_scope.

  Hint Resolve bassn_eval_true bassn_eval_false : hoare.
  Hint Constructors rhle_proof : hoare.
  Hint Unfold rhle_triple hoare_triple ehoare_triple.
  Hint Constructors ceval.

  Ltac apply_sound :=
    match goal with
    | H : context[_ |- {{_}} _ {{_}}] |- _ =>
      eapply hoare_proof_sound in H
    | H : context[_ |- {[_]} _ {[_]}#] |- _ =>
      eapply ehoare_proof_sound in H
    end.

  Theorem rhle_proof_sound Sigma : forall P c1 c2 Q,
      Sigma |- {{P}} c1 ~# c2 {[Q]} ->
      @rhle_triple {| funSpecs := Sigma; funDefs := empty |} P c1 c2 Q.
  Proof.
    intros ? ? ? ? pf.
    unfold rhle_triple.
    induction pf; intros st1 st2 st1' exe HP.
    - inv_ceval. eauto.
    - firstorder eauto.
    - edestruct IHpf as [st2' [exe' HQ]]; eauto.
      inv_ceval. inv_ceval. eauto.
    - inv_ceval. edestruct IHpf; eauto.
      apply_sound. eauto.
    - apply_sound.
      edestruct H as [st' [exe' HQ]]; eauto.
      edestruct IHpf as [st2' [? ?]]; eauto.
  Qed.

  Definition rwp {env : Env} c (Q : Assertion2) : Assertion2 :=
    fun st1 st2 => exists st2' (exe : st2 =[ c ]=> st2'), Q st1 st2'.

  Theorem rhle_proof_complete Sigma : forall P c1 c2 Q,
      @rhle_triple {| funSpecs := Sigma; funDefs := empty |} P c1 c2 Q -> 
      Sigma |- {{P}} c1 ~# c2 {[Q]}.
  Proof.
    unfold rhle_triple.
    intros P c1 c2 Q H.
    apply RHE_SkipIntroL. apply RHE_StepL with (@rwp {| funSpecs := Sigma; funDefs := empty |} c2 Q).
    intros st2. apply hoare_proof_complete.
    firstorder.
    apply RHE_SkipIntroR. eapply RHE_StepR. 2: constructor.
    intros st1. apply ehoare_proof_complete.
    firstorder.
  Qed.

End RHLE.

Notation "{{ P }}  c1 ~# c2  {[ Q ]}" :=
  (rhle_triple P c1 c2 Q) (at level 90, c1 at next level, c2 at next level)
  : hoare_spec_scope.

Notation "Sigma |- {{ P }}  c1 ~# c2  {[ Q ]}" :=
  (rhle_proof Sigma P c1 c2 Q) (at level 90, c1 at next level, c2 at next level)
  : hoare_spec_scope.
