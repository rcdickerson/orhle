(* Adapted from the Software Foundations series:
   https://softwarefoundations.cis.upenn.edu/ *)

Require Import Maps Imp.

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level).

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bassn_eval_true : forall b st,
  beval st b = true <-> bassn b st.
Proof.
  firstorder.
Qed.

Lemma bassn_eval_false : forall b st,
  beval st b = false <-> ~ bassn b st.
Proof.
  intros. destruct (beval st b) eqn:?; firstorder congruence.
Qed.

Open Scope hoare_spec_scope.
