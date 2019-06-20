Require Import Coq.Program.Tactics.
Require Import Maps Imp HoareCommon.

Section EHoare.

Context {env : Env}.

Definition ehoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st,
     (exists st', st =[ c ]=> st') ->
     P st ->
     exists st', st =[ c ]=> st' /\ Q st'.

Notation "{{ P }}  c  {{ Q }}#" :=
  (ehoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Definition ewp (c:com) (Q:Assertion) : Assertion :=
  fun st => (exists st', st =[ c ]=> st') -> exists st', st =[ c ]=> st' /\ Q st'.

Lemma ewp_is_precondition: forall c Q,
  {{ewp c Q}} c {{Q}}#.
Proof.
  firstorder.
Qed.

Lemma ewp_is_weakest: forall c Q P,
   {{P}} c {{Q}}# -> P ->> ewp c Q.
Proof.
  firstorder.
Qed.

Reserved Notation "|- {{ P }}  c  {{ Q }}#"
         (at level 90, c at next level).

Inductive ehoare_proof : Assertion -> com -> Assertion -> Type :=
  | EH_Skip : forall P,
      |- {{P}} SKIP {{P}}#
  | EH_Asgn : forall Q V a,
      |- {{assn_sub V a Q}} V ::= a {{Q}}#
  (* EH_Spec *)
  | EH_Seq  : forall P c Q d R,
      |- {{P}} c {{Q}}# -> |- {{Q}} d {{R}}# ->
      |- {{P}} c;;d {{R}}#
  | EH_If : forall P Q b c1 c2,
      |- {{fun st => P st /\ bassn b st}} c1 {{Q}}# ->
      |- {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}}# ->
      |- {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}#
  | EH_While : forall P b c,
      |- {{fun st => P st /\ bassn b st}} c {{P}}# ->
      |- {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}#
  | EH_Consequence  : forall (P Q P' Q' : Assertion) c,
      |- {{P'}} c {{Q'}}# ->
      (forall st, P st -> P' st) ->
      (forall st, Q' st -> Q st) ->
      |- {{P}} c {{Q}}#

where "|- {{ P }}  c  {{ Q }}#" := (ehoare_proof P c Q) : hoare_spec_scope.


Hint Resolve bassn_eval_true bassn_eval_false : hoare.
Hint Resolve ewp_is_precondition ewp_is_weakest : hoare.
Hint Constructors ehoare_proof : hoare.
Hint Unfold ehoare_triple ewp.
Hint Constructors ceval.

Theorem ehoare_proof_sound : forall P c Q,
    |- {{P}} c {{Q}}# -> {{P}} c {{Q}}#.
Proof.
  unfold ehoare_triple.
  intros ? ? ? pf. induction pf; intros st [st' HE] HP.
  - (* SKIP *)
    inversion HE; subst. eauto.
  - (* ::= *)
    inversion HE; subst. eauto.
  - (* ;; *)
    admit.
  - (* TEST *)
    inversion HE; subst.
    firstorder eauto.
    edestruct IHpf2; intuition eauto. congruence.
  - (* WHILE *)
    admit.
  - (* Conseq *)
    firstorder eauto.
Admitted.

Theorem ehoare_proof_complete: forall P c Q,
    {{P}} c {{Q}}# -> |- {{P}} c {{Q}}#.
Proof.
  Admitted.

End EHoare.
