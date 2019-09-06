(** * Imp: Simple Imperative Programs *)

(* Adapted from the Software Foundations series:
   https://softwarefoundations.cis.upenn.edu/ *)

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

Require Import
        Coq.Bool.Bool
        Coq.Strings.String
        Coq.Lists.List.

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

Definition funName := string.

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CCall (x : string) (f : funName) (args : list aexp)
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

Structure funSig : Type :=
  { arity : nat }.

Structure funSpec : Type :=
  { pre : list nat -> Prop;
    post : nat -> list nat -> Prop }.

Structure funDef : Type :=
  { funArgs : list string;
    funBody : com;
    funRet : aexp
  }.

Class Env : Type :=
  { funSigs : total_map funSig;
    funSpecs : total_map funSpec;
    funDefs : partial_map funDef
  }.

Reserved Notation "Sigma '|-' st '=[' c ']=>' st'"
                  (at level 40).

Inductive ceval (Sigma : Env) : com -> state -> state -> Type :=
  | E_Skip : forall st,
      Sigma |- st =[ SKIP ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      Sigma |- st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      Sigma |- st  =[ c1 ]=> st'  ->
      Sigma |- st' =[ c2 ]=> st'' ->
      Sigma |- st  =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      Sigma |- st =[ c1 ]=> st' ->
      Sigma |- st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      Sigma |- st =[ c2 ]=> st' ->
      Sigma |- st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      Sigma |- st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      Sigma |- st  =[ c ]=> st' ->
      Sigma |- st' =[ WHILE b DO c END ]=> st'' ->
      Sigma |- st  =[ WHILE b DO c END ]=> st''

  (* Evaluation of Function Calls *)
  | E_CallSpec : forall st args n x f,
      funDefs f = None ->
      (funSpecs f).(pre) (aseval st args) ->
      (funSpecs f).(post) n (aseval st args) ->
      Sigma |- st =[ x :::= f $ args ]=> (x !-> n ; st)

  | E_CallImpl : forall st st' args fd x f,
      funDefs f = Some fd ->
      Sigma |- build_total_map (funArgs fd) (aseval st args) 0 =[ funBody fd ]=> st' ->
      Sigma |- st =[ x :::= f $ args ]=> (x !-> aeval st' (funRet fd); st)

where "Sigma |- st =[ c ]=> st'" := (ceval Sigma c st st').

(* Well-formed expressions call functions with the right number of arguments. *)
Inductive WF_Com (Sigma : Env) : com -> Prop :=
| WF_Skip : WF_Com Sigma SKIP
| WF_Ass  : forall a1 x, WF_Com Sigma (x ::= a1)
| WF_Seq : forall c1 c2, WF_Com Sigma c1 -> WF_Com Sigma c2 -> WF_Com Sigma (c1 ;; c2)
| WF_If : forall b c1 c2,
    WF_Com Sigma c1 -> WF_Com Sigma c2 -> WF_Com Sigma (TEST b THEN c1 ELSE c2 FI)
| WF_While : forall b c,
    WF_Com Sigma c -> WF_Com Sigma (WHILE b DO c END)
| WF_Call : forall args x f,
    length args = (funSigs f).(arity) ->
    WF_Com Sigma (x :::= f $ args).

Inductive AppearsIn (f : funName) : com -> Prop :=
| AI_Seq_L : forall c1 c2, AppearsIn f c1 -> AppearsIn f (c1 ;; c2)
| AI_Seq_R : forall c1 c2, AppearsIn f c2 -> AppearsIn f (c1 ;; c2)
| AI_If_T : forall b c1 c2,
    AppearsIn f c1 -> AppearsIn f (TEST b THEN c1 ELSE c2 FI)
| AI_If_E : forall b c1 c2,
    AppearsIn f c2 -> AppearsIn f (TEST b THEN c1 ELSE c2 FI)
| AI_While : forall b c,
    AppearsIn f c -> AppearsIn f (WHILE b DO c END)
| AI_Call : forall args x,
    AppearsIn f (x :::= f $ args).

Section safe_Execution.

  (* Formalizing when it is safe to use function definitions.  Safe
     here means that the composite program doesn't introduce any new
     behaviors that fall outside the spec. *)

  (* A safe function definition is one that doesn't introduce any new
     behaviors outside those allowed by its specifiction. *)
  Definition safe_funDef (Sigma : Env)
             (fs : funSpec)
             (fd : funDef) : Prop :=
    forall (args : list nat) st',
      (pre fs) args ->
      Sigma |- build_total_map (funArgs fd) args 0 =[ funBody fd ]=> st' ->
      (post fs) (aeval st' (funRet fd)) args.

  (* An environment is safe if all of its function definitions are
     safe with respect to their specs.  *)
  Definition safe_Env (Sigma : Env) : Prop :=
    forall f fd,
      funDefs f = Some fd ->
      safe_funDef Sigma (funSpecs f) fd.

  (* A safe initial state is one that guarantees the program will not crash / get stuck *)
  CoInductive Safe (Sigma : Env) : com -> state -> Type :=
    | Safe_Skip : forall st,
      Safe Sigma SKIP st
  | Safe_Ass  : forall st x a,
      Safe Sigma (x ::= a) st
  | Safe_Seq : forall c1 c2 st,
      Safe Sigma c1 st ->
      (forall st', Sigma |- st =[ c1 ]=> st' -> Safe Sigma c2 st') ->
      Safe Sigma (c1 ;; c2) st
  | Safe_IfTrue : forall st b c1 c2,
      beval st b = true ->
      Safe Sigma c1 st ->
      Safe Sigma (TEST b THEN c1 ELSE c2 FI) st
  | Safe_IfFalse : forall st b c1 c2,
      beval st b = false ->
      Safe Sigma c2 st ->
      Safe Sigma (TEST b THEN c1 ELSE c2 FI) st
  | Safe_WhileFalse : forall b st c,
      beval st b = false ->
      Safe Sigma (WHILE b DO c END) st
  | Safe_WhileTrue : forall st b c,
      beval st b = true ->
      Safe Sigma c st ->
      (forall st', Sigma |- st =[ c ]=> st' -> Safe Sigma (WHILE b DO c END) st') ->
      Safe Sigma (WHILE b DO c END) st
  | Safe_CallDef :
      forall st args x f fd,
        funDefs f = Some fd ->
        Safe Sigma (funBody fd) (build_total_map (funArgs fd) (aseval st args) 0)->
        Safe Sigma (x :::= f $ args) st
  | Safe_CallSpec : forall st args x f,
      funDefs f = None ->
      (funSpecs f).(pre) (aseval st args) ->
      Safe Sigma (x :::= f $ args) st.

  (* Key Safety Theorem: executing a program in a safe environment and
  initial state will not produce any values that a 'pure'
  specification environment (i.e. one without any function
  definitions) would not. In other words, the composite program is a
  /refinement/ of the specification-only program. *)
  Theorem safe_Env_refine (Sigma : Env) :
    forall (c : com) (st st' : state),
      safe_Env Sigma ->
      Safe {|
          funSigs := funSigs;
          funSpecs := funSpecs;
          funDefs := empty |} c st ->
      Sigma |- st =[ c ]=> st' ->
      {| funSigs := funSigs;
         funSpecs := funSpecs;
         funDefs := empty |} |- st =[ c ]=> st'.
  Proof.
    induction 3; intros; try (solve [econstructor; eauto]).
    - inversion X; subst; try congruence; econstructor; eauto.
    - inversion X; subst; try congruence; econstructor; eauto.
    - inversion X; subst; eapply E_IfFalse; eauto; congruence.
    - inversion X; subst; try congruence; econstructor; eauto.
    - inversion X; subst; try congruence.
      + simpl in *; rewrite apply_empty in H4; discriminate.
      + eapply (E_CallSpec {| funSpecs := funSpecs; funDefs := empty |});
          simpl in *; eauto.
        eapply H; eauto.
  Qed.

  (* Next, we prove how to actually *build* a Safe Environment from
  set of function definitions. *)

  Local Hint Constructors ceval.
  Local Hint Constructors AppearsIn.

  (* Some standard weakening and strengthing lemmas for evaluation. *)

  Lemma eval_Env_Weaken
    : forall (Sigma : Env)
             (f : funName)
             (c : com),
      ~ AppearsIn f c ->
      (forall f' fd', funDefs f' = Some fd' ->
                      ~ AppearsIn f (funBody fd')) ->
      forall st st' fd,
        Sigma |- st =[ c ]=> st' ->
                             {| funSigs := funSigs;
                                funSpecs := funSpecs;
                                funDefs := f |-> fd; funDefs |} |- st =[ c ]=> st'.
  Proof.
    induction 3; simpl; intros; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - eapply E_IfFalse; eauto.
    - econstructor; eauto.
    - econstructor; eauto; simpl in *.
      unfold update, t_update; find_if_inside; subst; eauto.
      destruct H; eauto.
    - eapply E_CallImpl; simpl; eauto.
      unfold update, t_update; find_if_inside; eauto.
      destruct H; subst; eauto.
  Qed.

  Lemma eval_Env_Strengthen
    : forall (Sigma : Env)
             (f : funName)
             (c : com),
      ~ AppearsIn f c ->
      (forall f' fd', funDefs f' = Some fd' ->
                      ~ AppearsIn f (funBody fd')) ->
      forall st st' fd,
        {| funSigs := funSigs;
           funSpecs := funSpecs;
           funDefs := f |-> fd; funDefs |} |- st =[ c ]=> st' ->
                                                          Sigma |- st =[ c ]=> st'.
  Proof.
    induction 3; simpl; intros; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - eapply E_IfFalse; eauto.
    - econstructor; eauto.
    - econstructor; eauto; simpl in *.
      unfold update, t_update in *; find_if_inside; subst; eauto;
        discriminate.
    - eapply E_CallImpl; simpl in *; eauto.
      + eapply update_inv in e; destruct e as [[? ?] | [? ?]];
          subst; eauto.
        destruct H; eauto.
      + unfold update, t_update in *; find_if_inside; eauto.
        destruct H; subst; eauto.
  Qed.

  Lemma safe_Env_Extend
    : forall (Sigma : Env)
             (f : funName)
             (fd : funDef),
      safe_Env Sigma ->
      funDefs f = None ->
      (forall f' fd', funDefs f' = Some fd' ->
                      ~ AppearsIn f (funBody fd'))
      -> ~ AppearsIn f (funBody fd)
      -> safe_funDef Sigma (funSpecs f) fd
      -> safe_Env {| funSigs := funSigs;
                     funSpecs := funSpecs;
                     funDefs := f |-> fd; funDefs |}.
  Proof.
    unfold safe_Env; simpl; intros.
    unfold update, t_update in H4; find_if_inside; subst.
    - injections.
      unfold safe_funDef; intros; eapply H3;
        eauto using eval_Env_Strengthen.
    - unfold safe_funDef; intros.
      eapply H; eauto using eval_Env_Strengthen.
  Qed.

  (* Building an environment from a list of function definitions. *)

  Definition build_funSigs
             (names : list funName)
             (Sigs : list funSig)
    := fold_right (fun ffd Sigma'  =>
                                t_update Sigma' (fst ffd) (snd ffd))
                             (t_empty {| arity := 0 |})
                             (combine names Sigs).

  Definition build_funSpecs
             (names : list funName)
             (Specs : list funSpec)
    := fold_right (fun ffd Sigma'  =>
                     t_update Sigma' (fst ffd) (snd ffd))
                  (t_empty {| pre := fun _ => True;
                              post := fun _ _ => False |})
                  (combine names Specs).

  Definition build_funDefs
             (names : list funName)
             (Defs : list funDef)
  := fold_right (fun ffd Sigma' => update Sigma' (fst ffd) (snd ffd))
                empty (combine names Defs).

  Definition build_Env
             (names : list funName)
             (Sigs : list funSig)
             (Specs : list funSpec)
             (Defs : list funDef) :
    Env :=
    {| funSigs := build_funSigs names Sigs;
       funSpecs := build_funSpecs names Specs;
       funDefs := build_funDefs names Defs |}.

  Fixpoint build_safe_Env'
           (Sigs : total_map funSig)
           (Specs : total_map funSpec)
           (names : list funName)
           (Defs : list funDef)
    : Prop :=
    match names, Defs with
    | f :: names', fd :: Defs' =>
      Forall (fun fd' => ~ AppearsIn f (funBody fd')) Defs' /\
      ~ AppearsIn f (funBody fd) /\
      safe_funDef
        {| funSigs := Sigs;
           funSpecs := Specs;
           funDefs := fold_right (fun ffd Sigma' => update Sigma' (fst ffd) (snd ffd))
                                 empty (combine names Defs) |}
        (Specs f) fd /\
      (build_safe_Env' Sigs Specs names' Defs')
    | _, _ => True
    end.

  (* [build_safe_Env] defines a sufficient condition for the
  environment built [build_env] to be safe. *)
  Definition build_safe_Env
             (names : list funName)
             (Sigs : list funSig)
             (Specs : list funSpec)
             (Defs : list funDef)
    : Prop :=
    build_safe_Env' (build_funSigs names Sigs)
                    (build_funSpecs names Specs)
                    names Defs.

  Lemma build_safe_Env_is_safe'
    : forall (names : list funName)
             (Defs : list funDef)
             (funSpecs' : total_map funSpec)
             (funSigs' : total_map funSig),
      NoDup names ->
      length names = length Defs ->
      build_safe_Env' funSigs' funSpecs' names Defs ->
      safe_Env
        {|
          funSigs := funSigs';
          funSpecs := funSpecs';
          funDefs := fold_right
                       (fun (ffd : string * funDef) (Sigma' : partial_map funDef) => fst ffd |-> snd ffd; Sigma') empty
                       (combine names Defs) |}.
  Proof.
    induction names; simpl; intros.
    - unfold safe_Env; unfold build_Env; simpl; intros;
        compute in H1; discriminate.
    - destruct Defs; simpl in *;
        try discriminate; injections; split_and.
      inversion H; subst.
      unfold safe_Env in *.
      simpl; intros ? ? e; eapply update_inv in e;
        destruct e as [ [? ?] | [? ?] ]; subst; eauto.
      specialize (IHnames _ _ _ H8 H2 H4 _ _ H6).
      unfold safe_funDef in *; intros.
      eapply IHnames; eauto.
      eapply eval_Env_Strengthen; eauto.
      + generalize Defs H1 H0 H6; clear; induction names; simpl; intros.
        * compute in H6; discriminate.
        * destruct Defs; simpl in *; try discriminate.
          apply update_inv in H6; destruct H6 as [ [? ?] | [? ?] ]; subst;
            inversion H0; subst; eauto.
      + generalize Defs H1 H0; clear; induction names; simpl; intros.
        * compute in H; discriminate.
        * destruct Defs; simpl in *; try discriminate.
          apply update_inv in H; destruct H as [ [? ?] | [? ?] ]; subst;
            inversion H0; subst; eauto.
  Qed.

  (* Thankfully, [build_safe_Env] does guarantee safety! *)
  Corollary build_safe_Env_is_safe
    : forall (names : list funName)
             (Sigs : list funSig)
             (Specs : list funSpec)
             (Defs : list funDef),
      NoDup names ->
      length names = length Defs ->
      build_safe_Env names Sigs Specs Defs ->
      safe_Env (build_Env names Sigs Specs Defs).
  Proof.
    intros; eapply build_safe_Env_is_safe'; eauto.
  Qed.

  (* We can combining this [build_safe_Env_is_safe] with
  [safe_Env_refine], to show that if [build_safe_Env] holds, it is
  safe to execute the composite program built by 'linking' in the
  enviroment built by [build_Env]. *)
  Corollary build_safe_Env_refine :
    forall (c : com) (st st' : state)
           (names : list funName)
           (Sigs : list funSig)
           (Specs : list funSpec)
           (Defs : list funDef),
      NoDup names ->
      length names = length Defs ->
      build_safe_Env names Sigs Specs Defs ->
      Safe {|
          funSigs := build_funSigs names Sigs;
          funSpecs := build_funSpecs names Specs;
          funDefs := empty |} c st ->
      (build_Env names Sigs Specs Defs) |- st =[ c ]=> st' ->
              {| funSigs := build_funSigs names Sigs;
                 funSpecs := build_funSpecs names Specs;
                 funDefs := empty |} |- st =[ c ]=> st'.
  Proof.
    intros.
    eapply safe_Env_refine in X0; simpl in X0;
      eauto using build_safe_Env_is_safe.
  Qed.

End safe_Execution.

Section productive_Execution.

  (* Formalizing when it is productive to use function definitions.
     Productive here means that the function definition doesn't rule
     out some behavior allowed by the spec, i.e. the composite program
     still "produces" that behavior.

     Note: I (Ben) am not in love with this terminology, anyone who reads
     this should feel free to suggest another. Living? NotDead? UnDead?
     *)

  (* A productive function definition is one that produces at least
     one behavior allowed by its specifiction. *)
  Definition productive_funDef (Sigma : Env)
             (fs : funSpec)
             (fd : funDef) : Prop :=
    forall (args : list nat),
      (pre fs) args ->
      exists (st' : state)
             (exe : Sigma |- build_total_map (funArgs fd) args 0 =[ funBody fd ]=> st'),
        (post fs) (aeval st' (funRet fd)) args.

  (* An environment is productive if all of its function definitions are
     productive with respect to their specs.  *)
  Definition productive_Env (Sigma : Env) : Prop :=
    forall f fd,
      funDefs f = Some fd ->
      productive_funDef Sigma (funSpecs f) fd.

  (* A productive initial state is one that ensures the program
  *always* produces the specified final state *)

  (*CoInductive Productive (Sigma : Env) : com -> state -> state -> Type :=
    | Productive_Skip : forall st,
        Productive Sigma SKIP st st
    | Productive_Ass  : forall st x a,
        Productive Sigma (x ::= a) st (x !-> (aeval st a) ; st)
    | Productive_Seq : forall c1 c2 st st'',
        (forall st', Sigma |- st =[ c1 ]=> st' -> Productive Sigma c2 st' st'') ->
        Productive Sigma (c1 ;; c2) st st''
    | Productive_IfTrue : forall st st' b c1 c2,
        beval st b = true ->
        Productive Sigma c1 st st' ->
        Productive Sigma (TEST b THEN c1 ELSE c2 FI) st st'
    | Productive_IfFalse : forall st b c1 c2 st',
        beval st b = false ->
        Productive Sigma c2 st st' ->
        Productive Sigma (TEST b THEN c1 ELSE c2 FI) st st'
    | Productive_WhileFalse : forall b st c,
        beval st b = false ->
        Productive Sigma (WHILE b DO c END) st st
    | Productive_WhileTrue : forall st b c st'',
        beval st b = true ->
        (forall st', Sigma |- st =[ c ]=> st' ->
                     Productive Sigma (WHILE b DO c END) st' st'') ->
        Productive Sigma (WHILE b DO c END) st st''
    | Productive_CallDef :
        forall st st' args x f fd,
          funDefs f = Some fd ->
          Productive Sigma (funBody fd) (build_total_map (funArgs fd) (aseval st args) 0) st'
          -> Productive Sigma (x :::= f $ args) st (x !-> aeval st' (funRet fd); st)
    | Productive_CallSpec : forall st args x f n,
        funDefs f = None ->
        (funSpecs f).(pre) (aseval st args) ->
        (funSpecs f).(post) n (aseval st args) ->
        Productive Sigma (x :::= f $ args) st (x !-> n ; st). *)

  (* Key Productivity Theorem: executing a program in a productive
  environment and productive initial state will produce some value that a
  'pure' specification environment (i.e. one without any function
  definitions) would have. *)

  (*Theorem productive_Env_produces (Sigma : Env) :
    forall (c : com) (st st' : state),
      productive_Env Sigma ->
      Productive {|
          funSigs := funSigs;
          funSpecs := funSpecs;
          funDefs := empty |} c st ->
      { st'' : state & ((Sigma |- st =[ c ]=> st'') *
      ({| funSigs := funSigs;
          funSpecs := funSpecs;
          funDefs := empty |} |- st =[ c ]=> st''))%type}.
  Proof.
    induction c; intros st Prod_Sig Safe_Sig;
      try (solve [eexists _; split; econstructor; eauto]).
    - admit.
    - inversion Safe_Sig; subst; clear Safe_Sig.
      destruct (IHc1 _ Prod_Sig X) as [st' [? ?] ].
      specialize (X0 _ c0).
      destruct (IHc2 _ Prod_Sig X0) as [st'' [? ?] ].
      exists st''; split; econstructor; eauto.
    - inversion Safe_Sig; subst; clear Safe_Sig.
      + destruct (IHc1 _ Prod_Sig X) as [st' [? ?] ].
        exists st'; split; econstructor; eauto.
      + destruct (IHc2 _ Prod_Sig X) as [st' [? ?] ].
        exists st'; split; eapply E_IfFalse; eauto.
    - inversion Safe_Sig; subst; clear Safe_Sig.
      + exists st; split; econstructor; eauto.
      + destruct (IHc _ Prod_Sig X) as [st' [? ?] ].
        eapply X0 in c1.
        destruct (IHc _ Prod_Sig c1) as [st' [? ?] ].

      inversion X; subst; try congruence; econstructor; eauto.
    - inversion X; subst; try congruence; econstructor; eauto.
    - inversion X; subst; eapply E_IfFalse; eauto; congruence.
    - inversion X; subst; try congruence; econstructor; eauto.
    - inversion X; subst; try congruence.
      + simpl in *; rewrite apply_empty in H4; discriminate.
      + eapply (E_CallSpec {| funSpecs := @funSpecs Sigma; funDefs := empty |});
          simpl in *; eauto.
        eapply H; eauto.
  Qed. *)

End productive_Execution.
