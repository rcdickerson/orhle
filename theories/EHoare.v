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
     exists st', st =[ c ]=> st' /\ Q st'.

Notation "{{ P }}  c  {{ Q }}#" :=
  (ehoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Definition ewp (c:com) (Q:Assertion) : Assertion :=
  fun st => exists st', st =[ c ]=> st' /\ Q st'.

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
  - firstorder with hoare.
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
    destruct (beval st b) eqn:?; firstorder with hoare.
  - (* WHILE *)
    eapply ehoare_while; eauto.
  - (* Conseq *)
    firstorder eauto.
Qed.

Inductive loop_sizeR : forall {st c st'}, st =[ c ]=> st' -> nat -> Prop :=
| LS_WhileFalse : forall b st c pff,
    loop_sizeR (E_WhileFalse b st c pff) 0
| LS_WhileTrue : forall st st' st'' b c pft pfc pfw n,
    loop_sizeR pfw n ->
    loop_sizeR (E_WhileTrue st st' st'' b c pft pfc pfw) (S n)
.

Definition loop_measureR b c (Q : Assertion)
           (st : state) (n : nat) : Prop :=
  (~ (exists st', st =[ WHILE b DO c END ]=> st' /\ Q st') -> n = 0) /\
  (forall m st' (pf : st =[ WHILE b DO c END ]=> st'),
      Q st' ->
      loop_sizeR pf m ->
      (forall m' st'' (pf' : st =[ WHILE b DO c END ]=> st''),
          Q st'' ->
          loop_sizeR pf' m' ->
          m <= m') ->
      n = m).

Scheme ceval_ind_dep := Induction for ceval Sort Prop.

Lemma loop_sizeR_ex : forall st b c st' (pf : st =[ WHILE b DO c END ]=> st'),
    exists n, loop_sizeR pf n.
Proof.
  intros. remember (WHILE b DO c END)%imp as c' eqn:Heq.
  induction pf using ceval_ind_dep; inversion Heq; subst.
  - repeat econstructor.
  - destruct IHpf2; auto. repeat econstructor. eauto.
Qed.

Lemma loop_sizeR_inv : forall st st' st'' b c pft pfc pfw n,
    loop_sizeR (E_WhileTrue st st' st'' b c pft pfc pfw) n ->
    exists m, loop_sizeR pfw m /\ S m = n.
Proof.
  Admitted.

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
  (exists st', st =[ WHILE b DO c END ]=> st' /\ Q st') ->
  exists m st' (pf : st =[ WHILE b DO c END ]=> st'),
    Q st' /\ loop_sizeR pf m /\
    (forall m' st'' (pf' : st =[ WHILE b DO c END ]=> st''),
        Q st'' -> loop_sizeR pf' m' -> m <= m').
Proof.
  intros.
  edestruct (nonempty_smallest_ex
               (fun m => exists st' (pf : st =[ WHILE b DO c END ]=> st'),
                    Q st' /\ loop_sizeR pf m)) as [m ?].
  - destruct H as [? [H ?]]. edestruct loop_sizeR_ex with (pf:=H). eauto.
  - destruct_conjs. exists m. repeat econstructor; eauto.
Qed.

Lemma loop_measureR_is_fun b c Q : forall (st : state),
    exists! n, loop_measureR b c Q st n.
Proof.
  unfold unique.
  intros. destruct (classic (exists st', st =[ WHILE b DO c END ]=> st' /\ Q st')) as [H | H].
  - apply loop_measureR_ex in H. destruct H as [m [st' [pf ?]]]. destruct_conjs.
    exists m. split.
    + split. intros. exfalso. eauto.
      intros m'. intros. assert (m <= m') by eauto. assert (m' <= m) by eauto.
      lia.
    + intros ? H'. destruct H' as [? H'].
      symmetry. eauto.
  - exists 0. split.
    + split; intros; eauto. exfalso. eauto.
    + intros ? H'. destruct H' as [? H'].
      symmetry. eauto.
Qed.

Lemma loop_measureR_order : forall (Q : Assertion) st st' st'' b c pft pfc pfw m,
    Q st'' ->
    loop_sizeR (E_WhileTrue st st' st'' b c pft pfc pfw) m ->
    (forall m' st''' (pf' : st =[ WHILE b DO c END ]=> st'''),
        Q st''' ->
        loop_sizeR pf' m' ->
        m <= m') ->
    forall m', loop_measureR b c Q st' m' ->
          S m' = m.
Proof.
  intros until m. intros HQ Hs H m' H'. destruct H' as [_ H'].
  apply loop_sizeR_inv in Hs. destruct Hs as [n [? ?]].
  subst. f_equal. eapply H'; eauto.
  intros. apply le_S_n.
  eapply H; eauto. constructor. eauto.
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
    intros. edestruct HT as [? [HE ?]]; eauto.
    inversion HE; subst. eauto.
  - (* ::= *)
    eapply EH_Consequence; eauto with hoare.
    intros. edestruct HT as [? [HE ?]]; eauto.
    inversion HE; subst. eauto.
  - (* :::= *)
    eapply EH_Consequence; eauto with hoare.
    simpl. intros. edestruct HT as [? [HE ?]]; eauto.
    inversion HE; subst. eauto.
  - (* ;; *)
    apply EH_Seq with (ewp c2 Q); eauto. apply IHc1.
    intros. edestruct HT as [? [HE ?]]; eauto.
    inversion HE; subst. firstorder.
  - (* IFB *)
    apply EH_If.
    + apply IHc1. intros. destruct_conjs.
      edestruct HT as [? [HE ?]]; eauto.
      inversion HE; subst; firstorder with hoare.
    + apply IHc2. intros. destruct_conjs.
      edestruct HT as [? [HE ?]]; eauto.
      inversion HE; subst; firstorder with hoare.
  - (* WHILE *)
    eapply EH_Consequence with (P':=ewp (WHILE b DO c END) Q).
    + destruct (unique_choice _ _
                              (loop_measureR b c Q)
                              (loop_measureR_is_fun b c Q)) as [measure Hm].
      apply EH_While with (E:=measure).
      intros. apply IHc. intros ? [Hwp ?]. destruct_conjs. subst.
      destruct (Hm st) as [_ Hm'].
      edestruct loop_measureR_ex as [m [st' [pf ?]]]; eauto. destruct_conjs.
      remember (WHILE b DO c END)%imp eqn:Heq.
      destruct pf; inversion Heq; subst; clear Heq. exfalso. congruence.
      eexists. intuition eauto.
      eapply loop_measureR_order in Hm; eauto.
      assert (measure st = m) by eauto. lia.
    + eauto.
    + simpl. intros ? [H ?]. destruct H as [? [H ?]].
      inversion H; subst; eauto. exfalso. eauto.
Qed.

End EHoare.
