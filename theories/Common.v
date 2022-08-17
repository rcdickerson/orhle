Require Import Coq.Bool.Bool
        Coq.Vectors.Vector.

Ltac injections :=
  repeat match goal with
         | [ H : _ = _ |- _ ]
           => injection H; intros; subst; clear H
         end.

Ltac find_if_inside :=
  match goal with
  | [ |- context[if ?X then _ else _] ] => destruct X
  | [ H : context[if ?X then _ else _] |- _ ]=> destruct X
  end.

Ltac split_and :=
  repeat match goal with
           H : _ /\ _ |- _ => destruct H
         end.

Section VectorFacts.

  Lemma vector_nth_replace {A} {k}:
    forall (i : Fin.t k) (v : Vector.t A k) (a : A),
      Vector.nth (Vector.replace v i a) i = a.
  Proof.
    induction i;
      intros; pattern v; eapply Vector.caseS'; eauto; intros.
    simpl; eauto.
  Qed.

  Lemma vector_nth_replace' {A} {k}:
    forall (i i0 : Fin.t k) (v : Vector.t A k) (a : A),
      i <> i0 ->
      Vector.nth (Vector.replace v i a) i0 = Vector.nth v i0.
  Proof.
    induction i0;
      intros; pattern v; eapply Vector.caseS'; eauto; intros.
    - simpl; revert v a H h t.
      pattern i; eapply Fin.caseS'; intros; eauto.
      congruence.
    - simpl; revert v a H h t.
      pattern i; eapply Fin.caseS'; intros; eauto.
      eapply IHi0; congruence.
  Qed.

  Lemma vector_replace_nth_id {A} {k}:
    forall (i : Fin.t k) (v : Vector.t A k),
      Vector.replace v i (Vector.nth v i) = v.
  Proof.
    induction i;
      intros; pattern v; eapply Vector.caseS'; eauto; intros.
    simpl; eauto.
    rewrite IHi; reflexivity.
  Qed.

  Lemma vector_replace_replace_id {A} {k}:
    forall (i : Fin.t k) (v : Vector.t A k) (a a' : A),
      Vector.replace (Vector.replace v i a) i a'  = Vector.replace v i a'.
  Proof.
    induction i;
      intros; pattern v; eapply Vector.caseS'; eauto; intros.
    simpl; eauto.
    rewrite IHi; reflexivity.
  Qed.

  Lemma vector_nth_exists {A} {k} (P : A -> Fin.t k -> Prop):
    (forall (i : Fin.t k), exists (a : A), P a i) ->
    exists (v : Vector.t A k), forall (i : Fin.t k), P (Vector.nth v i) i.
  Proof.
    induction k; intros.
    - eexists (Vector.nil _); intros; inversion i.
    - specialize (IHk (fun a i => P a (Fin.FS i)) (fun i => H (Fin.FS i))); destruct IHk.
      destruct (H Fin.F1).
      eexists (Vector.cons _ x0 _ x).
      intros.
      pattern i; eapply Fin.caseS'; intros; eauto.
  Qed.

End VectorFacts.
