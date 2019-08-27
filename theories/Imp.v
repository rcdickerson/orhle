(** * Imp: Simple Imperative Programs *)

(* Adapted from the Software Foundations series:
   https://softwarefoundations.cis.upenn.edu/ *)

Require Import
        Coq.Bool.Bool
        Coq.Lists.List
        Coq.Strings.String.

Import Nat.
Require Import Maps.

(* ================================================================= *)
(** ** States *)

Definition state := total_map nat.

(* ================================================================= *)
(** ** Syntax  *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** Notations *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.

(* ================================================================= *)
(** ** Evaluation *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Definition aseval (st : state) (al : list aexp) : list nat :=
  map (aeval st) al.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).

Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

(* ################################################################# *)
(** * Commands *)

(* ================================================================= *)
(** ** Syntax *)

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CCall (x : string) (f : string) (args : list aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "x ':::=' f '$' a" :=
  (CCall x f a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.

(* ################################################################# *)
(** * Evaluating Commands *)

(* ----------------------------------------------------------------- *)
(** *** Operational Semantics *)

Structure funSpec : Type :=
  { pre : list nat -> Prop; post : nat -> list nat -> Prop }.

Structure funDef : Type :=
  { funArgs : list string;
    funBody : com;
    funRet : aexp
  }.

Class Env : Type :=
  { funSpecs : total_map funSpec;
    funDefs : partial_map funDef
  }.

Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40).

Inductive ceval {env : Env} : com -> state -> state -> Type :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st  =[ WHILE b DO c END ]=> st''

  (* Evaluation of Function Calls *)
  | E_CallSpec : forall st args n x f,
      funDefs f = None ->
      (funSpecs f).(pre) (aseval st args) ->
      (funSpecs f).(post) n (aseval st args) ->
      st =[ x :::= f $ args ]=> (x !-> n ; st)

  | E_CallImpl : forall st st' args fd x f,
      funDefs f = Some fd ->
      build_total_map (funArgs fd) (aseval st args) 0 =[ funBody fd ]=> st' ->
      st =[ x :::= f $ args ]=> (x !-> aeval st' (funRet fd); st)

  where "st =[ c ]=> st'" := (ceval c st st').

(* A safe program is one that is guaranteed not to crash / get stuck *)
CoInductive Safe {env : Env} : com -> state -> Type :=
    | Safe_Skip : forall st,
      Safe SKIP st
  | Safe_Ass  : forall st x a,
      Safe (x ::= a) st
  | Safe_Seq : forall c1 c2 st,
      Safe c1 st ->
      (forall st', st  =[ c1 ]=> st' -> Safe c2 st') ->
      Safe (c1 ;; c2) st
  | Safe_IfTrue : forall st b c1 c2,
      beval st b = true ->
      Safe c1 st ->
      Safe (TEST b THEN c1 ELSE c2 FI) st
  | Safe_IfFalse : forall st b c1 c2,
      beval st b = false ->
      Safe c2 st ->
      Safe (TEST b THEN c1 ELSE c2 FI) st
  | Safe_WhileFalse : forall b st c,
      beval st b = false ->
      Safe (WHILE b DO c END) st
  | Safe_WhileTrue : forall st b c,
      beval st b = true ->
      Safe c st ->
      (forall st', st =[ c ]=> st' -> Safe (WHILE b DO c END) st') ->
      Safe (WHILE b DO c END) st
  | Safe_CallDef :
      forall st args x f fd,
        funDefs f = Some fd ->
        Safe (x :::= f $ args) (build_total_map (funArgs fd) (aseval st args) 0)->
        Safe (x :::= f $ args) st
  | Safe_CallSpec : forall st args x f,
      funDefs f = None ->
      (funSpecs f).(pre) (aseval st args) ->
      Safe (x :::= f $ args) st.

Definition valid_funDef (sigma : Env) (fs : funSpec) (fd : funDef) : Prop :=
  forall (args : list nat) st',
    (pre fs) args ->
    build_total_map (funArgs fd) args 0 =[ funBody fd ]=> st' ->
    (post fs) (aeval st' (funRet fd)) args.

Definition valid_Env (sigma : Env) : Prop :=
  forall f fd,
    funDefs f = Some fd ->
    valid_funDef sigma (funSpecs f) fd.

Theorem valid_Env_refine {sigma : Env} :
  forall (c : com) (st st' : state),
    valid_Env sigma ->
    @Safe {| funSpecs := @funSpecs sigma; funDefs := empty |} c st ->
    st =[ c ]=> st' ->
    @ceval {| funSpecs := @funSpecs sigma; funDefs := empty |} c st st'.
Proof.
  induction 3; intros; try (solve [econstructor; eauto]).
  - inversion X; subst; try congruence; econstructor; eauto.
  - inversion X; subst; try congruence; econstructor; eauto.
  - inversion X; subst; eapply E_IfFalse; eauto; congruence.
  - inversion X; subst; try congruence; econstructor; eauto.
  - inversion X; subst; try congruence.
    + simpl in *; rewrite apply_empty in H4; discriminate.
    + eapply (E_CallSpec (env := {| funSpecs := @funSpecs sigma; funDefs := empty |}));
        simpl in *; eauto.
      eapply H; eauto.
Qed.
