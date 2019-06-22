Require Import
        Coq.Arith.Arith
        Coq.micromega.Psatz
        Coq.Logic.Classical
        Coq.Logic.ClassicalUniqueChoice
        Coq.Program.Tactics.

Require Import Maps Imp HoareCommon.

Section EHoare.

Context {env : Env}.

Definition ehoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st,
     P st ->
     exists st' (exe : st =[ c ]=> st'), Q st'.

Notation "{{ P }}  c  {{ Q }}#" :=
  (ehoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Definition ewp (c:com) (Q:Assertion) : Assertion :=
  fun st => exists st' (exe : st =[ c ]=> st'), Q st'.

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

Inductive ehoare_proof : Assertion -> com -> Assertion -> Prop :=
  | EH_Skip : forall P,
      |- {{P}} SKIP {{P}}#
  | EH_Asgn : forall Q V a,
      |- {{Q[V |-> a]}} V ::= a {{Q}}#
  | EH_Spec : forall Q y f xs,
      |- {{fun st =>
            (funsig f).(pre) (aseval st xs) /\
            exists v, (funsig f).(post) v (aseval st xs) /\
                 Q[y |-> v] st}} y :::= f $ xs {{Q}}#
  | EH_Seq  : forall P c Q d R,
      |- {{P}} c {{Q}}# -> |- {{Q}} d {{R}}# ->
      |- {{P}} c;;d {{R}}#
  | EH_If : forall P Q b c1 c2,
      |- {{fun st => P st /\ bassn b st}} c1 {{Q}}# ->
      |- {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}}# ->
      |- {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}#
  | EH_While : forall P E b c,
      (forall n : nat, |- {{fun st => P st /\ bassn b st /\ E st = n}} c {{fun st => P st /\ E st < n}}#) ->
      (* E st is nat. *)
      (* (forall st, P st /\ bassn b st -> 0 <= E st) -> *)
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

Lemma ehoare_while : forall P E b c,
    (forall n : nat, {{fun st => P st /\ bassn b st /\ E st = n}} c {{fun st => P st /\ E st < n}}#) ->
    {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}#.
Proof.
  unfold ehoare_triple.
  intros. remember (E st). revert dependent st.
  induction n as [n IH] using (well_founded_ind lt_wf). intros. subst.
  destruct (beval st b) eqn:?.
  - edestruct H; eauto. destruct_conjs.
    edestruct IH; eauto. destruct_conjs.
    eauto.
  - repeat econstructor; eauto. firstorder with hoare.
Qed.

Theorem ehoare_proof_sound : forall P c Q,
    |- {{P}} c {{Q}}# -> {{P}} c {{Q}}#.
Proof.
  unfold ehoare_triple.
  intros ? ? ? pf. induction pf; intros st HP.
  - (* SKIP *)
    eauto.
  - (* ::= *)
    repeat econstructor. eauto.
  - (* :::= *)
    destruct_conjs.
    repeat econstructor; eauto.
  - (* ;; *)
    firstorder eauto.
  - (* TEST *)
    destruct (beval st b) eqn:?.
    + edestruct IHpf1; firstorder eauto.
    + edestruct IHpf2; firstorder eauto. firstorder with hoare.
  - (* WHILE *)
    eapply ehoare_while; eauto.
  - (* Conseq *)
    firstorder eauto.
Qed.

Fixpoint loop_size {st c st'} (exe : st =[ c ]=> st') : nat :=
  match exe with
  | E_WhileTrue _ _ _ _ _ _ _ exew => S (loop_size exew)
  | _ => 0
  end.

Definition loop_measureR b c (Q : Assertion)
           (st : state) (n : nat) : Prop :=
  (~ (exists st' (exe : st =[ WHILE b DO c END ]=> st'), Q st') -> n = 0) /\
  (forall st' (exe : st =[ WHILE b DO c END ]=> st'),
      Q st' ->
      (forall st'' (exe' : st =[ WHILE b DO c END ]=> st''),
          Q st'' ->
          loop_size exe <= loop_size exe') ->
      n = loop_size exe).

Lemma nonempty_smallest_ex (P : nat -> Prop) :
  (exists n, P n) ->
  exists n, P n /\ (forall n', P n' -> n <= n').
Proof.
  intros [n H]. induction n using (well_founded_ind lt_wf).
  destruct (classic (exists y, y < n /\ P y)).
  - firstorder.
  - exists n. intuition. apply Nat.nlt_ge. eauto.
Qed.

Lemma loop_measureR_ex b c Q st :
  (exists st' (exe : st =[ WHILE b DO c END ]=> st'), Q st') ->
  exists st' (exe : st =[ WHILE b DO c END ]=> st'),
    Q st' /\
    (forall st'' (exe' : st =[ WHILE b DO c END ]=> st''),
        Q st'' -> loop_size exe <= loop_size exe').
Proof.
  intros.
  edestruct (nonempty_smallest_ex
               (fun m => exists st' (exe : st =[ WHILE b DO c END ]=> st'),
                    Q st' /\ loop_size exe = m)).
  - firstorder eauto.
  - destruct_conjs. subst. repeat econstructor; eauto.
    Grab Existential Variables.
    auto.
Qed.

Lemma loop_measureR_is_fun b c Q : forall (st : state),
    exists! n, loop_measureR b c Q st n.
Proof.
  unfold unique.
  intros. destruct (classic (exists st' (exe : st =[ WHILE b DO c END ]=> st'), Q st')) as [H | H].
  - apply loop_measureR_ex in H. destruct H as [? [exe ?]]. destruct_conjs.
    exists (loop_size exe). split.
    + split. intros. exfalso. eauto.
      intros ? exe'. intros.
      assert (loop_size exe <= loop_size exe') by eauto.
      assert (loop_size exe' <= loop_size exe) by eauto.
      lia.
    + intros ? H'. destruct H' as [? H'].
      symmetry. eauto.
  - exists 0. split.
    + split; intros; eauto. exfalso. eauto.
    + intros ? H'. destruct H' as [? H'].
      symmetry. eauto.
Qed.

Lemma loop_measureR_order : forall (Q : Assertion) st st' st'' b c pft exec exew,
    Q st'' ->
    (forall st''' (exe' : st =[ WHILE b DO c END ]=> st'''),
        Q st''' ->
        loop_size (E_WhileTrue st st' st'' b c pft exec exew) <= loop_size exe') ->
    forall m, loop_measureR b c Q st' m ->
         S m = loop_size (E_WhileTrue st st' st'' b c pft exec exew).
Proof.
  intros until exew. intros HQ H m H'. destruct H' as [_ H'].
  simpl loop_size in *. f_equal. eapply H'; eauto.
  intros ? exe' ?.
  apply le_S_n. etransitivity.
  eapply (H _ (E_WhileTrue _ _ _ _ _ _ _ exe')); eauto.
  simpl. eauto.
  Grab Existential Variables.
  all : eauto.
Qed.

Theorem ehoare_proof_complete: forall P c Q,
    {{P}} c {{Q}}# -> |- {{P}} c {{Q}}#.
Proof.
  unfold ehoare_triple.
  intros P c. revert dependent P.
  induction c; intros P Q HT.
  - (* SKIP *)
    eapply EH_Consequence; eauto with hoare.
    intros. edestruct HT as [? [exe ?]]; eauto.
    inversion exe; subst. eauto.
  - (* ::= *)
    eapply EH_Consequence; eauto with hoare.
    intros. edestruct HT as [? [exe ?]]; eauto.
    inversion exe; subst. eauto.
  - (* :::= *)
    eapply EH_Consequence; eauto with hoare.
    simpl. intros. edestruct HT as [? [exe ?]]; eauto.
    inversion exe; subst. eauto.
  - (* ;; *)
    apply EH_Seq with (ewp c2 Q); eauto. apply IHc1.
    intros. edestruct HT as [? [exe ?]]; eauto.
    inversion exe; subst. repeat econstructor; eauto.
  - (* IFB *)
    apply EH_If.
    + apply IHc1. intros. destruct_conjs.
      edestruct HT as [? [exe ?]]; eauto.
      inversion exe; subst; firstorder with hoare.
    + apply IHc2. intros. destruct_conjs.
      edestruct HT as [? [exe ?]]; eauto.
      inversion exe; subst; firstorder with hoare.
  - (* WHILE *)
    eapply EH_Consequence with (P':=ewp (WHILE b DO c END) Q).
    + destruct (unique_choice _ _
                              (loop_measureR b c Q)
                              (loop_measureR_is_fun b c Q)) as [measure Hm].
      apply EH_While with (E:=measure).
      intros. apply IHc. intros. destruct_conjs. subst.
      destruct (Hm st) as [_ Hm'].
      edestruct loop_measureR_ex as [st' [exe ?]]; eauto. destruct_conjs.
      remember (WHILE b DO c END)%imp eqn:Heq.
      destruct exe; inversion Heq; subst; clear Heq. exfalso. congruence.
      exists st'. eexists; eauto. intuition eauto.
      eapply loop_measureR_order in Hm; eauto.
      rewrite <- Hm' in Hm; eauto. lia.
    + eauto.
    + simpl. intros ? [H ?]. destruct H as [? [exe ?]].
      inversion exe; subst; eauto. exfalso. eauto.
Qed.

End EHoare.
