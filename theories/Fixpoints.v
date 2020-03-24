Section Fixpoints.

  (* Propositional analogues to definitions from above. *)

  Definition PSet (A : Type) := A -> Prop.

  Definition In {A} (a : A) (e : PSet A) : Prop := e a.
  Notation "x '∈' e" := (In x e) (at level 60).

  Definition Subset {A} (e1 e2 : PSet A) : Prop :=
    forall x, x ∈ e1 -> x ∈ e2.

  Notation "s1 ⊆ s2" := (Subset s1 s2) (at level 60).

  Context {U : Type}. (* The universal set, i.e. our domain of discourse. *)
  Variable F : (PSet U) -> PSet U. (* Our generating function--
  takes a set of Us and builds a new set.*)

  (* A generator function is monotone if it preserves the subset
  relation on its argument. *)
  Definition Monotone_F : Prop :=
    forall (S S' : PSet U),
      S ⊆ S' -> F S ⊆ F S'.

  Definition FClosed (S : PSet U) : Prop := F S ⊆ S.

  Definition FConsistent (S : PSet U) : Prop := S ⊆ F S.

  Definition FixedPoint (S : PSet U) : Prop :=
    S ⊆ F S /\ F S ⊆ S.

  (* The least fixed point of a monotone generator function exists,
   and it is the intersection of all F-closed sets. *)
  Definition LFP : PSet U :=
    fun a => forall S, FClosed S -> S a.

  (* The greatest fixed point of a generator function exists,
   and it is the union of all F-consistent sets. *)
  Definition GFP : PSet U :=
    fun a => exists S, FConsistent S /\ S a.

  Lemma GFP_is_FConsistent
    : Monotone_F -> FConsistent GFP.
  Proof.
    intros F_Monotone.
    unfold FConsistent.
    intros ? ?.
    (* By the definition of GFP, there must be some F-consistent set, X, that contains x *)
    destruct H as [X [? ?] ].
    (* Since X is F-consistent, by definition x is a member of F X. *)
    apply H in H0.
    (* We have now established that F X ⊆ F GFP: *)
    revert x H0; fold (Subset (F X) (F GFP)).
    (* Since F is monotone, it suffices to show that X ⊆ GFP *)
    eapply F_Monotone.
    (* To show X ⊆ GFP, we just need to show that every x in X is in GFP *)
    intros ? ?.
    (* By definition, x is an element of GFP if it is a member of an
    F-consistent set. By assumption, x is in X and F is F-consistent,
    so we're done!*)
    unfold In, GFP.
    eexists X.
    eauto.
  Qed.

  Lemma GFP_is_FClosed
    : Monotone_F -> FClosed GFP.
  Proof.
    intros F_Monotone ? ?.
    (* By our previous lemma, we know that GFP ⊆ F GFP. By monotonicity of
       F, F GFP ⊆ F (F GFP). *)
    assert (F GFP ⊆ F (F GFP)).
    { apply F_Monotone.
      apply GFP_is_FConsistent.
      eassumption. }
    (* By definition, this means F GFP is F-consistent. *)
    assert (FConsistent (F GFP)).
    { intros ? ?.
      apply H0.
      assumption. }
    (* Since F is a member of an F-consistent set, it must be a member
    of GFP.*)
    unfold In, GFP.
    exists (F GFP).
    eauto.
  Qed.

  Theorem GFP_is_FixedPoint
    : Monotone_F -> FixedPoint GFP.
  Proof.
    intro F_Monotone.
    unfold FixedPoint.
    split.
    - apply GFP_is_FConsistent; eauto.
    - apply GFP_is_FClosed; eauto.
  Qed.

  Theorem LFP_is_FClosed
    : Monotone_F -> FClosed LFP.
  Proof.
    intro F_Monotone.
    unfold FClosed; intros ? ? ? ?.
    apply H0.
    revert x H.
    eapply F_Monotone.
    unfold LFP; intros ? ?.
    apply H.
    apply H0.
  Qed.

  Theorem LFP_is_FConsistent
    : Monotone_F -> FConsistent LFP.
  Proof.
    intro F_Monotone.
    unfold FClosed; intros ? ?.
    assert (F (F LFP) ⊆ F LFP).
    { apply F_Monotone.
      apply LFP_is_FClosed.
      eassumption. }
    (* By definition, this means F LFP is F-closed. *)
    assert (FClosed (F LFP)).
    { intros ? ?.
      apply H0.
      assumption. }
    (* Since F is a member of every F-closed set, it must be a member
    of the F-closed set (F LFP) .*)
    eapply H.
    apply H1.
  Qed.

  Theorem LFP_is_FixedPoint
    : Monotone_F -> FixedPoint LFP.
  Proof.
    intro F_Monotone.
    unfold FixedPoint.
    split.
    - apply LFP_is_FConsistent; eauto.
    - apply LFP_is_FClosed; eauto.
  Qed.

  Lemma Ind
    : forall (Ind : PSet U),
      FClosed Ind -> forall a, LFP a -> Ind a.
  Proof.
    unfold LFP, FClosed; intros; eapply H0; eauto.
  Qed.

  Lemma CoInd
    : forall (Ind : PSet U),
      FConsistent Ind -> forall a, Ind a -> GFP a.
  Proof.
    unfold GFP, FConsistent; intros; eauto.
  Qed.

End Fixpoints.
