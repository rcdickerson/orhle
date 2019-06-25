(** * Hoare Logic *)

(* Adapted from the Software Foundations series:
   https://softwarefoundations.cis.upenn.edu/ *)

Require Import Coq.Program.Tactics.
Require Import Maps Imp HoareCommon.

(* ################################################################# *)
(** * Hoare Triples *)

Section Hoare.

Context {env : Env}.

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st'  ->
     P st  ->
     Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => forall s', s =[ c ]=> s' -> Q s'.

Lemma wp_is_precondition: forall c Q,
  {{wp c Q}} c {{Q}}.
Proof.
  firstorder.
Qed.

Lemma wp_is_weakest: forall c Q P',
   {{P'}} c {{Q}} -> forall st, P' st -> wp c Q st.
Proof.
  firstorder.
Qed.

Reserved Notation "|- {{ P }}  c  {{ Q }}"
         (at level 90, c at next level).

Inductive hoare_proof : Assertion -> com -> Assertion -> Type :=
  | H_Skip : forall P,
      |- {{P}} SKIP {{P}}
  | H_Asgn : forall Q V a,
      |- {{Q[V |-> a]}} V ::= a {{Q}}
  | H_Spec : forall Q y f xs,
      |- {{fun st =>
            (funsig f).(pre) (aseval st xs) ->
            forall v, (funsig f).(post) v (aseval st xs) ->
                 Q[y |-> v] st}} y :::= f $ xs {{Q}}
  | H_Seq  : forall P c Q d R,
      |- {{P}} c {{Q}} -> |- {{Q}} d {{R}} ->
      |- {{P}} c;;d {{R}}
  | H_If : forall P Q b c1 c2,
      |- {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
      |- {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
      |- {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}
  | H_While : forall P b c,
      |- {{fun st => P st /\ bassn b st}} c {{P}} ->
      |- {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}
  | H_Consequence  : forall (P Q P' Q' : Assertion) c,
      |- {{P'}} c {{Q'}} ->
      (forall st, P st -> P' st) ->
      (forall st, Q' st -> Q st) ->
      |- {{P}} c {{Q}}

where "|- {{ P }}  c  {{ Q }}" := (hoare_proof P c Q) : hoare_spec_scope.


Hint Resolve bassn_eval_true bassn_eval_false : hoare.
Hint Resolve wp_is_precondition wp_is_weakest : hoare.
Hint Constructors hoare_proof : hoare.
Hint Unfold hoare_triple wp.
Hint Constructors ceval.

Lemma hoare_while : forall P b c,
    {{fun st => P st /\ bassn b st}} c {{P}} ->
    {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  unfold hoare_triple.
  intros ? ? ? ? ? ? HE ?. remember (WHILE b DO c END)%imp eqn:Heq.
  induction HE; try inversion Heq; subst.
  - firstorder with hoare.
  - eauto.
Qed.

Theorem hoare_proof_sound : forall P c Q,
    |- {{P}} c {{Q}} -> {{P}} c {{Q}}.
Proof.
  unfold hoare_triple.
  intros ? ? ? pf. induction pf; intros st st' HE HP.
  - (* SKIP *)
    inversion HE; subst. eauto.
  - (* ::= *)
    inversion HE; subst. eauto.
  - (* :::= *)
    inversion HE; subst. firstorder.
  - (* ;; *)
    inversion HE; subst. eauto.
  - (* TEST *)
    inversion HE; subst. eauto.
    firstorder with hoare.
  - (* WHILE *)
    eapply hoare_while; eauto.
  - (* Conseq *)
    eauto.
Qed.

Theorem hoare_proof_complete: forall P c Q,
    {{P}} c {{Q}} -> |- {{P}} c {{Q}}.
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
    apply H_Seq with (wp c2 Q); firstorder eauto.
  - (* IFB *)
    apply H_If.
    + firstorder eauto.
    + apply IHc2. firstorder with hoare.
  - (* WHILE *)
    eapply H_Consequence with (P':=wp (WHILE b DO c END) Q).
    + constructor. firstorder eauto.
    + eauto.
    + firstorder with hoare.
Qed.

End Hoare.
