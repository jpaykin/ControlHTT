Require Import List String Arith Reals Program.Equality.
Add LoadPath "..".
Require Import mymatrices syntax context substitution typing properties.
Set Implicit Arguments.

Open Scope R_scope.

Definition P := Mat ([[6742 * /10000000, 428 * /10000000],
                      [428* /10000000, 24651* /10000000]]).
Definition Ac := Mat ([[499 * /1000, -5 * /100],
                       [1 * /100, 1]]).
Definition Cc := Mat ([[56448 * /100, 0]]).
Definition Bc := Mat ([[1],[0]]). 
Definition Dc := Mat ([[-1280]]).
Definition xc := Mat ([[0],[0]]).
Definition yc := Binop Max (Binop Min (Binop Minus (Var "y") (Var "yd")) 
                                      (Mat [[1]])) 
                           (Mat [[-1]]).
Definition u := Binop Plus (Binop Multiply (Var "Cc") (Var "x"))
                           (Binop Multiply (Var "Dc") (Var "yc")).
Definition xc' := Binop Plus (Binop Multiply (Var "Ac") (Var "x"))
                             (Binop Multiply (Var "Bc") (Var "yc")).

Definition Eps M := Binop bLe 
                          (Binop Multiply (Unop Transpose M)
                                (Binop Multiply (Var "P") M))
                          (Mat [[1]]).
Definition PEps M := Id Bool (Boolean true) (Eps M).
Definition I := And (PEps (Var "x")) (PEps (Var "z")).

  Definition I''' := And (PEps (Var "x")) (PEps xc).
  Definition I'''' := And (PEps xc) (PEps xc).
  Definition J1 := And (PEps (Var "w")) (PEps (Var "z")).
  Definition J2 := And (PEps (Var "x")) (PEps (Var "w")).
  Definition J := And (PEps (Var "z")) (PEps (Var "z")).
  Definition J3 := And (PEps (Var "x")) (PEps (Var "x")).
  Definition J4 := And (PEps xc) (PEps (Var "z")).


Definition PI := Id Bool (Boolean true)
                         (Binop bLe (Binop Times (Var "yc") (Var "yc"))
                                    (Mat [[1]])).
Definition PI' := Id Bool (Boolean true)
                          (Binop bLe (Binop Times yc yc) (Mat [[1]])).

Definition loop :=
  Receive "yd" (By 1 1) (Ref 3%nat) ;;
  Bind "yc" (By 1 1) yc (
  Annotation PI ;;
  Bind "u" (By 1 1) u (
  Send (By 1 1) (Var "u") (Ref 1%nat) ;;
  IntroTerm xc')).

Definition u' := Binop Plus (Binop Multiply (Var "Cc") (Var "x"))
                            (Binop Multiply (Var "Dc") yc).
Definition xc'' := Binop Plus (Binop Multiply (Var "Ac") (Var "x"))
                              (Binop Multiply (Var "Bc") yc).
Definition loop' :=
  Receive "yd" (By 1 1) (Ref 3%nat) ;;
  Annotation PI' ;;
  Send (By 1 1) u' (Ref 1%nat) ;;
  IntroTerm xc''.

Definition prog :=
  Bind "P" (By 2 2) P (
  Bind "Ac" (By 2 2) Ac (
  Bind "Cc" (By 1 2) Cc (
  Bind "Bc" (By 2 1) Bc (
  Bind "Dc" (By 1 1) Dc (
  Receive "y" (By 1 1) (Ref 2%nat) ;;
  Loop "z" I xc (By 2 1) "x" (Boolean true) "x" (
    loop
  );; TT
))))).

Definition EpsP M := Binop bLe (Binop Multiply (Unop Transpose M)
    (Binop Multiply P M)) (Mat [[1]]).
Definition PEpsP M := Id Bool (Boolean true) (EpsP M).
Definition I' := And (PEpsP (Var "x")) (PEpsP (Var "z")).

Definition prog' :=
  Receive "y" (By 1 1) (Ref 2%nat) ;;
  Loop "z" I' xc (By 2 1) "x" (Boolean true) "x" (
    Receive "yd" (By 1 1) (Ref 3%nat) ;;
    Annotation PI' ;;
    Send (By 1 1) (Binop Plus (Binop Multiply Cc (Var "x"))
                              (Binop Multiply Dc yc)) (Ref 1%nat)  ;;
    IntroTerm (Binop Plus (Binop Multiply Ac (Var "x"))
                          (Binop Multiply Bc yc))) ;;
  TT.


Lemma check_PEps : forall VC x pfP pfx,
      wf_var_context VC ->
      get "P" VC pfP = By 2 2 ->
      get x VC pfx = By 2 1 ->
      check_prop VC init_mem_context (PEps (Var x)) (PEps (Var x)).
Proof.
  intros.
  step. apply ciCompBinop with 1%nat 1%nat; auto.
  apply ciMultiply with 2%nat; auto.
    step. ciVar x (By 2 1) pfx.
  apply ciMultiply with 2%nat; auto.
    ciVar "P" (By 2 2) pfP. ciVar x (By 2 1) pfx.
Qed.

Definition VC1 : var_context := List.nil.
Definition VC2 := ("P",By 2 2)::VC1.
Definition VC3 := ("Ac",By 2 2)::VC2.
Definition VC4 := ("Cc",By 1 2)::VC3.
Definition VC5 := ("Bc",By 2 1)::VC4.
Definition VC6 := ("Dc",By 1 1)::VC5.
Definition VC7 := ("y",By 1 1)::VC6.
Definition VC14 := ("z",By 2 1)::VC7.

Unset Implicit Arguments.
Definition goodVC1 VC := wf_var_context VC.
Definition goodVC2 VC pf2 :=
  get "P" VC pf2 = By 2 2 /\ goodVC1 VC.
Definition goodVC3 VC pf2 pf3 :=
  get "Ac" VC pf3 = By 2 2 /\ goodVC2 VC pf2.
Definition goodVC4 VC pf2 pf3 pf4 :=
  get "Cc" VC pf4 = By 1 2 /\ goodVC3 VC pf2 pf3.
Definition goodVC5 VC pf2 pf3 pf4 pf5 :=
  get "Bc" VC pf5 = By 2 1 /\ goodVC4 VC pf2 pf3 pf4.
Definition goodVC6 VC pf2 pf3 pf4 pf5 pf6 :=
  get "Dc" VC pf6 = By 1 1 /\ goodVC5 VC pf2 pf3 pf4 pf5.
Definition goodVC7 VC pf2 pf3 pf4 pf5 pf6 pf7:=
  get "y" VC pf7 = By 1 1 /\ goodVC6 VC pf2 pf3 pf4 pf5 pf6.
Definition goodVC14 VC pf2 pf3 pf4 pf5 pf6 pf7 pf14 :=
  get "z" VC pf14 = By 2 1 /\ goodVC7 VC pf2 pf3 pf4 pf5 pf6 pf7.
Set Implicit Arguments.


Definition P1 := Top.
Definition P2 := And P1 (Id (By 2 2) (Var "P") P).
Definition P3 := And P2 (Id (By 2 2) (Var "Ac") Ac).
Definition P4 := And P3 (Id (By 1 2) (Var "Cc") Cc).
Definition P5 := And P4 (Id (By 2 1) (Var "Bc") Bc).
Definition P6 := And P5 (Id (By 1 1) (Var "Dc") Dc).
Definition P7 := P6.
Definition P14 := And P7 (And J4 (Id Bool (Boolean true) (Boolean false))).

Definition P14' := P7 / "w" \
                       (And (And (PEps xc) (PEps (Var "z")))
                            (Id Bool (Boolean true) (Boolean false))).
Definition Q14 := And P14' (Id Unit TT TT).
Definition Q7 := Exists "z" (By 2 1) Q14.
Definition Q6 := Exists "y" (By 1 1) Q7.
Definition Q5 := Exists "Dc" (By 1 1) Q6.
Definition Q4 := Exists "Bc" (By 2 1) Q5.
Definition Q3 := Exists "Cc" (By 1 2) Q4.
Definition Q2 := Exists "Ac" (By 2 2) Q3.
Definition Q1 := Exists "P" (By 2 2) Q2.

Hint Extern 2 (check_intro_term _ _ _ _) => constructor; auto.
Hint Extern 2 (check_type _ _ _) => constructor; auto.


Lemma wf_VC2 : wf_var_context VC2. constructor; auto. Qed.
Hint Resolve wf_VC2.
Lemma wf_VC3 : wf_var_context VC3. constructor; auto. Qed.
Hint Resolve wf_VC3.
Lemma wf_VC4 : wf_var_context VC4. constructor; auto. Qed.
Hint Resolve wf_VC4.
Lemma wf_VC5 : wf_var_context VC5. constructor; auto. Qed.
Hint Resolve wf_VC5.
Lemma wf_VC6 : wf_var_context VC6. constructor; auto. Qed.
Hint Resolve wf_VC6.
Lemma wf_VC7 : wf_var_context VC7. constructor; auto. Qed.
Hint Resolve wf_VC7.
Lemma wf_VC14 : wf_var_context VC14. constructor; auto. Qed.
Hint Resolve wf_VC14.

Lemma check_prop_P2 : forall VC pf2,
      goodVC2 VC pf2 ->
      check_prop VC init_mem_context P2 P2.
  destruct 1.
  constructor; auto. constructor; auto.
  apply ciElimTerm with (Var "P") (By 2 2); auto.
    apply ieVar with pf2; auto.
Qed.

Lemma check_prop_P3 : forall VC pf2 pf3,
      goodVC3 VC pf2 pf3 ->
      check_prop VC init_mem_context P3 P3.
  intros until pf3; intro H.
  destruct H as [H3 H]; destruct H as [H2 H1].
  constructor; auto.
  apply check_prop_P2 with pf2. split; auto.
  constructor; auto.
  apply ciElimTerm with (Var "Ac") (By 2 2); auto.
    apply ieVar with pf3; auto.
Qed.
Lemma check_prop_P4 : forall VC pf2 pf3 pf4,
      goodVC4 VC pf2 pf3 pf4 ->
      check_prop VC init_mem_context P4 P4.
  intros VC pf2 pf3 pf4 H.
  assert (H' : goodVC3 VC pf2 pf3). destruct H; auto.
  destruct H as [H4 H]; destruct H as [H3 H]; destruct H as [H2 H1].
  constructor; auto.
  apply check_prop_P3 with pf2 pf3; destruct H'; auto. step.
  step.
  apply ciElimTerm with (Var "Cc") (By 1 2); auto.
    apply ieVar with pf4; auto.        
Qed.
Lemma check_prop_P5 : forall VC pf2 pf3 pf4 pf5,
      goodVC5 VC pf2 pf3 pf4 pf5 ->
      check_prop VC init_mem_context P5 P5.
  intros until pf5; intro H.
  assert (H' : goodVC4 VC pf2 pf3 pf4). destruct H; auto.
  destruct H as [H5 [H4 [H3 [H2 H]]]].
  constructor; auto.
  apply check_prop_P4 with pf2 pf3 pf4; auto.
  constructor; auto.
    apply ciElimTerm with (Var "Bc") (By 2 1); auto.
    apply ieVar with pf5; auto.
Qed.
Lemma check_prop_P6 : forall VC pf2 pf3 pf4 pf5 pf6,
      goodVC6 VC pf2 pf3 pf4 pf5 pf6->
      check_prop VC init_mem_context P6 P6.
  intros until pf6; intro H.
  assert (H' : goodVC5 VC pf2 pf3 pf4 pf5). destruct H; auto.
  destruct H as [H6 [H5 [H4 [H3 [H2 H1]]]]].
  constructor; auto.
  apply check_prop_P5 with pf2 pf3 pf4 pf5; auto.
  constructor; auto.
    apply ciElimTerm with (Var "Dc") (By 1 1); auto.
    apply ieVar with pf6; auto.
Qed.

Lemma check_prop_P7 : forall VC pf2 pf3 pf4 pf5 pf6 pf7,
      goodVC7 VC pf2 pf3 pf4 pf5 pf6 pf7->
      check_prop VC init_mem_context P7 P7.
  intros. unfold P7.
  apply check_prop_P6 with pf2 pf3 pf4 pf5 pf6.
  destruct H; auto.
Qed.


Lemma check_prop_J4 : forall VC pf2 pf3 pf4 pf5 pf6 pf7 pf14,
      goodVC14 VC pf2 pf3 pf4 pf5 pf6 pf7 pf14 ->
      check_prop VC init_mem_context J4 J4.
  intros.
  destruct H as [H14 [H7 [H6 [H5 [H4 [H3 [H2 H1]]]]]]].
  constructor; auto.    
    constructor; auto. apply ciCompBinop with 1%nat 1%nat; auto.
    apply ciMultiply with 2%nat; auto.
    apply ciMultiply with 2%nat; auto.
    apply ciElimTerm with (Var "P") (By 2 2); auto.
      apply ieVar with pf2; auto.
    constructor; auto. apply ciCompBinop with 1%nat 1%nat; auto.
    apply ciMultiply with 2%nat; auto.
    constructor; auto. apply ciElimTerm with (Var "z") (By 2 1); auto.
      apply ieVar with pf14; auto.
    apply ciMultiply with 2%nat; auto.
    apply ciElimTerm with (Var "P") (By 2 2); auto.
      apply ieVar with pf2; auto.
    apply ciElimTerm with (Var "z") (By 2 1); auto.
      apply ieVar with pf14; auto.
Qed.

Lemma check_prop_P14' : forall VC pf2 pf3 pf4 pf5 pf6 pf7 pf14,
      goodVC14 VC pf2 pf3 pf4 pf5 pf6 pf7 pf14 ->
      check_prop VC init_mem_context P14' P14'.
  intros until pf14; intro H.
  assert (H' : goodVC7 VC pf2 pf3 pf4 pf5 pf6 pf7). destruct H; auto.
  destruct H as [H14 [H7 [H6 [H5 [H4 [H3 [H2 H1]]]]]]].
  constructor; auto.
  step.
  apply check_prop_subst; simpl; auto.
    apply check_prop_HC_weakening; auto.
    apply check_prop_P7 with pf2 pf3 pf4 pf5 pf6 pf7; auto.
    destruct 1 as [K | [K | K]]; auto; inversion K.
  apply check_prop_subst; simpl; auto.
    apply check_prop_HC_weakening; auto.
    step. apply check_prop_J4 with pf2 pf3 pf4 pf5 pf6 pf7 pf14; auto.
  repeat split; auto.
  destruct 1 as [K | [K | K]]; auto; inversion K.
Qed.

Lemma check_prop_Q7 : forall VC pf2 pf3 pf4 pf5 pf6,
      goodVC6 VC pf2 pf3 pf4 pf5 pf6 ->
      check_prop VC init_mem_context Q7 Q7.
  intros until pf6; intro H.
  destruct H as [H6 [H5 [H4 [H3 [H2 H1]]]]].
  constructor; auto.
  constructor; auto. unfold P14'.
  constructor; auto. simpl.
  constructor; auto. constructor; auto.
Ltac const := constructor; auto.
  const. const. const. const. const. 
  apply ciElimTerm with (Var "P") (By 2 2); auto.
    apply ieVar with (InTail _ _ pf2); auto.
    rewrite <- get_neq with _ _ _ _ pf2 _; auto. inversion 1.
  const. 
  apply ciElimTerm with (Var "Ac") (By 2 2); auto.
    apply ieVar with (InTail _ _ pf3); auto.
    rewrite <- get_neq with _ _ _ _ pf3 _; auto. inversion 1.
  const.
  apply ciElimTerm with (Var "Cc") (By 1 2); auto.
    apply ieVar with (InTail _ _ pf4); auto.
    rewrite <- get_neq with _ _ _ _ pf4 _; auto. inversion 1.
  const.
  apply ciElimTerm with (Var "Bc") (By 2 1); auto.
    apply ieVar with (InTail _ _ pf5); auto.
    rewrite <- get_neq with _ _ _ _ pf5 _; auto. inversion 1.
  const.
  apply ciElimTerm with (Var "Dc") (By 1 1); auto.
    apply ieVar with (InTail _ _ pf6); auto.
    rewrite <- get_neq with _ _ _ _ pf6 _; auto. inversion 1.
  const. const. constructor; auto. 
  apply ciCompBinop with 1%nat 1%nat; auto.
    apply ciMultiply with 2%nat; auto. apply ciMultiply with 2%nat; auto.
    apply ciElimTerm with (Var "P") (By 2 2); auto.
      apply ieVar with (InTail _ _ pf2); auto.
      rewrite <- get_neq with _ _ _ _ pf2 _; auto. inversion 1.
  const. 
  apply ciCompBinop with 1%nat 1%nat; auto.
    apply ciMultiply with 2%nat; auto. 
      const. apply ciElimTerm with (Var "z") (By 2 1); auto.
      apply ieVar with (InHead _ _ _); auto.
    apply ciMultiply with 2%nat; auto.
    apply ciElimTerm with (Var "P") (By 2 2); auto.
      apply ieVar with (InTail _ _ pf2); auto.
      rewrite <- get_neq with _ _ _ _ pf2 _; auto. inversion 1.
    apply ciElimTerm with (Var "z") (By 2 1); auto.
      apply ieVar with (InHead _ _ _); auto.
Qed.  

Ltac intro_subst_eq := eapply hsElimShape; auto.
Ltac intro_subst_neq := apply hsElim; apply hsVarNeq; auto; inversion 1.
Ltac solve_hereditary_subst :=
  repeat match goal with
  | [ |- _ ] => intro_subst_eq; fail 
  | [ |- _ ] => intro_subst_neq; fail
  | [ |- _ ] => constructor; auto
  end.

Definition VC8 := ("x",By 2 1)::VC7.
Definition VC9 := ("yd",By 1 1)::VC8.
Definition VC10 := ("yc",By 1 1)::VC9.
Definition VC11 := VC10.
Definition VC12 := ("u",By 1 1)::VC11.
Definition VC13 := VC12.

Lemma wf_VC8 : wf_var_context VC8. constructor; auto. Qed.
Hint Resolve wf_VC8.
Lemma wf_VC9 : wf_var_context VC9. constructor; auto. Qed.
Hint Resolve wf_VC9.
Lemma wf_VC10 : wf_var_context VC10. constructor; auto. Qed.
Hint Resolve wf_VC10.
Lemma wf_VC11 : wf_var_context VC11. auto. Qed.
Hint Resolve wf_VC11.
Lemma wf_VC12 : wf_var_context VC12. constructor; auto. Qed.
Hint Resolve wf_VC12.

Unset Implicit Arguments.
Definition goodVC8 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 :=
  get "x" VC pf8 = By 2 1 /\ goodVC7 VC pf2 pf3 pf4 pf5 pf6 pf7.
Definition goodVC9 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 :=
  get "yd" VC pf9 = By 1 1 /\ goodVC8 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8.
Definition goodVC10 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 :=
  get "yc" VC pf10 = By 1 1 /\ goodVC9 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9.
Definition goodVC12 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf12 :=
  get "u" VC pf12 = By 1 1 /\ goodVC10 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10.
Set Implicit Arguments.
          

Definition P8 := And (And (HId init mem) J3)
                      (Id Bool (Boolean true) (Boolean true)).
Definition P9 := P8.
Definition P10 := And P9 (Id (By 1 1) (Var "yc") yc).
Definition P11 := P10 /"z"\ PI.
Definition P11' := P10 /"z"\ PI'.
Definition P12 := And P11 (Id (By 1 1) (Var "u") u).
Definition P12' := And P11' (Id (By 1 1) (Var "u") u).
Definition P13 := P12.

Definition Q13 := And P12 (Id (By 2 1) (aux_expand_fun (By 2 1) (Var "z")) xc').
Definition Q12 := Q13.
Definition Q11 := Exists "u" (By 1 1) Q12.
Definition Q10 := Q11.
Definition Q9 := Exists "yc" (By 1 1) Q10.
Definition Q8 := Exists "yd" (By 1 1) Q9.

Lemma check_prop_P8 : forall VC pf2 pf3 pf4 pf5 pf6 pf7 pf8,
      goodVC8 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 ->
      check_prop VC init_mem_context P8 P8.
Proof.
  intros until pf8. 
  destruct 1 as [H8 [H7 [H6 [H5 [H4 [H3 [H2 H1]]]]]]].
  step. step. step. step. step. step. simpl. right. auto.
  (*check_prop J3*)
  step. step. apply ciCompBinop with 1%nat 1%nat; auto.
  apply ciMultiply with 2%nat; auto.
  step. 
  ciVar "x" (By 2 1) pf8.
  apply ciMultiply with 2%nat; auto.
  ciVar "P" (By 2 2) pf2.
  ciVar "x" (By 2 1) pf8.
  step.
  apply ciCompBinop with 1%nat 1%nat; auto.
  apply ciMultiply with 2%nat; auto.
  step. ciVar "x" (By 2 1) pf8.
  apply ciMultiply with 2%nat; auto.
  ciVar "P" (By 2 2) pf2. ciVar "x" (By 2 1) pf8.
Qed.
Lemma check_prop_P9 : forall VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9,
      goodVC9 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 ->
      check_prop VC init_mem_context P9 P9.
Proof.
  intros. 
  apply check_prop_P8 with pf2 pf3 pf4 pf5 pf6 pf7 pf8; auto.
  destruct H; auto.
Qed.
Lemma check_prop_P10 : forall VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10,
      goodVC10 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 ->
      check_prop VC init_mem_context P10 P10.
Proof.
  intros until pf10.
  destruct 1 as [H10 [H9 [H8 [H7 [H6 [H5 [H4 [H3 [H2 H1]]]]]]]]].
  step. apply check_prop_P9 with pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9; auto.
    repeat (split; auto).
  step. ciVar "yc" (By 1 1) pf10.
  step. step. step. ciVar "y" (By 1 1) pf7. ciVar "yd" (By 1 1) pf9.
Qed.
Lemma check_prop_P11 : forall VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10,
      goodVC10 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 ->
      check_prop VC init_mem_context P11 P11.
Proof.
  intros until pf10.
  destruct 1 as  [H10 [H9 [H8 [H7 [H6 [H5 [H4 [H3 [H2 H1]]]]]]]]].
  step. step; apply check_prop_subst; simpl; auto.
  (*P10*) apply check_prop_HC_weakening.
    apply check_prop_P10 with pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10; auto.
      repeat (split; auto).
    destruct 1 as [H | [H | H]]; auto; inversion H.
  (*PI*) step. apply ciCompBinop with 1%nat 1%nat; auto.
    step; ciVar "yc" (By 1 1) pf10.
Qed. 
Lemma check_prop_P11' : forall VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10,
      goodVC10 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 ->
      check_prop VC init_mem_context P11' P11'.
Proof.
  intros until pf10.
  destruct 1 as  [H10 [H9 [H8 [H7 [H6 [H5 [H4 [H3 [H2 H1]]]]]]]]].
  step. step; apply check_prop_subst; simpl; auto.
  (*P10*) apply check_prop_HC_weakening.
    apply check_prop_P10 with pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10; auto.
      repeat (split; auto).
    intro H. destruct H as [H | [H | H]]; auto; inversion H.
  (*PI'*) step. apply ciCompBinop with 1%nat 1%nat; auto.
    do 3 step; (step; [ciVar "y" (By 1 1) pf7 | ciVar "yd" (By 1 1) pf9]).
Qed. 
Lemma check_prop_P12 : forall VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf12,
      goodVC12 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf12 ->
      check_prop VC init_mem_context P12 P12.
Proof.
  intros until pf12.
  destruct 1 as [H12 [H10 [H9 [H8 [H7 [H6 [H5 [H4 [H3 [H2 H1]]]]]]]]]].
  step. apply check_prop_P11 with pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10; auto.
    repeat (split; auto).
  step. ciVar "u" (By 1 1) pf12.
  step. apply ciMultiply with 2%nat; auto.
  ciVar "Cc" (By 1 2) pf4. ciVar "x" (By 2 1) pf8.
  apply ciMultiply with 1%nat; auto.
  ciVar "Dc" (By 1 1) pf6. ciVar "yc" (By 1 1) pf10.
Qed.
Lemma check_prop_P12' : forall VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf12,
      goodVC12 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf12 ->
      check_prop VC init_mem_context P12' P12'.
Proof.
  intros until pf12.
  destruct 1 as [H12 [H10 [H9 [H8 [H7 [H6 [H5 [H4 [H3 [H2 H1]]]]]]]]]].
  step. apply check_prop_P11' with pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10; auto.
    repeat (split; auto).
  step. ciVar "u" (By 1 1) pf12.
  step. apply ciMultiply with 2%nat; auto.
  ciVar "Cc" (By 1 2) pf4. ciVar "x" (By 2 1) pf8.
  apply ciMultiply with 1%nat; auto.
  ciVar "Dc" (By 1 1) pf6. ciVar "yc" (By 1 1) pf10.
Qed.

Lemma check_prop_Q13 : forall VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf12 pf14,
      goodVC12 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf12 ->
      get "z" VC pf14 = By 2 1 ->
      check_prop VC init_mem_context Q13 Q13.
Proof.
  intros until pf14.
  destruct 1 as [H12 [H10 [H9 [H8 [H7 [H6 [H5 [H4 [H3 [H2 H1]]]]]]]]]].
  step.
  (*P13*) apply check_prop_P12 with pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf12.
    repeat (split; auto).
  step. ciVar "z" (By 2 1) pf14.
  step. apply ciMultiply with 2%nat; auto.
    ciVar "Ac" (By 2 2) pf3. ciVar "x" (By 2 1) pf8.
  apply ciMultiply with 1%nat; auto.
    ciVar "Bc" (By 2 1) pf5. ciVar "yc" (By 1 1) pf10.
Qed.

Lemma check_prop_Q11 : forall VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf14,
      goodVC10 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 ->
      get "z" VC pf14 = By 2 1 ->
      check_prop VC init_mem_context Q11 Q11.
Proof.
  intros until pf14.
  destruct 1 as [H10 [H9 [H8 [H7 [H6 [H5 [H4 [H3 [H2 H1]]]]]]]]].
  step. 
  apply check_prop_Q13 with (InTail "u" (By 1 1) pf2) (InTail "u" (By 1 1) pf3)
    (InTail "u" (By 1 1) pf4) (InTail "u" (By 1 1) pf5) (InTail "u" (By 1 1) pf6)
    (InTail "u" (By 1 1) pf7) (InTail "u" (By 1 1) pf8) (InTail "u" (By 1 1) pf9)
    (InTail "u" (By 1 1) pf10) (InHead "u" (By 1 1) VC)
    (InTail "u" (By 1 1) pf14).
    repeat (split; auto);
      try match goal with 
      | [ |- get _ _ (InTail _ _ ?pf) = _ ] =>
        rewrite <- get_neq with _ _ _ _ pf _; auto; inversion 1
      end.
      step.
    rewrite <- get_neq with _ _ _ _ pf14 _; auto; inversion 1.
Qed.

Lemma check_prop_Q9 : forall VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf14,
      goodVC9 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 ->
      get "z" VC pf14 = By 2 1 ->
      check_prop VC init_mem_context Q9 Q9.
Proof.
  intros until pf14.
  destruct 1 as [H9 [H8 [H7 [H6 [H5 [H4 [H3 [H2 H1]]]]]]]].
  step. apply check_prop_Q11 with 
    (InTail "yc" (By 1 1) pf2) (InTail "yc" (By 1 1) pf3)
    (InTail "yc" (By 1 1) pf4) (InTail "yc" (By 1 1) pf5) 
    (InTail "yc" (By 1 1) pf6) (InTail "yc" (By 1 1) pf7) 
    (InTail "yc" (By 1 1) pf8) (InTail "yc" (By 1 1) pf9)
    (InHead "yc" (By 1 1) VC) (InTail "yc" (By 1 1) pf14).
    repeat (split; auto);
      try match goal with
      | [ |- get _ _ (InTail _ _ ?pf) = _ ] =>
        rewrite <- get_neq with _ _ _ _ pf _; auto; inversion 1
      end.
      step.
    rewrite <- get_neq with _ _ _ _ pf14 _; auto; inversion 1.
Qed.

Lemma check_prop_Q8 : forall VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf14,
      goodVC8 VC pf2 pf3 pf4 pf5 pf6 pf7 pf8 ->
      get "z" VC pf14 = By 2 1 ->
      check_prop VC init_mem_context Q8 Q8.
Proof.
  intros until pf14.
  destruct 1 as [H8 [H7 [H6 [H5 [H4 [H3 [H2 H1]]]]]]].
  step. apply check_prop_Q9 with 
    (InTail "yd" (By 1 1) pf2) (InTail "yd" (By 1 1) pf3)
    (InTail "yd" (By 1 1) pf4) (InTail "yd" (By 1 1) pf5) 
    (InTail "yd" (By 1 1) pf6) (InTail "yd" (By 1 1) pf7) 
    (InTail "yd" (By 1 1) pf8)
    (InHead "yd" (By 1 1) VC) (InTail "yd" (By 1 1) pf14).
    repeat (split; auto);
      try match goal with
      | [ |- get _ _ (InTail _ _ ?pf) = _ ] =>
        rewrite <- get_neq with _ _ _ _ pf _; auto; inversion 1
      end.
      step.
    rewrite <- get_neq with _ _ _ _ pf14 _; auto; inversion 1.
Qed.

Lemma check_prop_I : forall VC pfP pfx pfz,
      wf_var_context VC ->
      get "P" VC pfP = By 2 2 ->
      get "x" VC pfx = By 2 1 ->
      get "z" VC pfz = By 2 1 ->
      check_prop VC init_mem_context I I.
Proof.
  intros. step.
  apply check_PEps with pfP pfx; auto.
  apply check_PEps with pfP pfz; auto.
Qed.

Lemma check_prop_PI : forall VC pfyc,
      wf_var_context VC -> 
      get "yc" VC pfyc = By 1 1 ->
      check_prop VC init_mem_context PI PI.
Proof.
  intros. step.
  apply ciCompBinop with 1%nat 1%nat; auto.
  step; ciVar "yc" (By 1 1) pfyc.
Qed.


Hypothesis seq_P7_I : sequent VC7 init_mem_context P7 I''''.

Hypothesis sequent_Q8_I : sequent (("z",By 2 1)::VC8) init_mem_context Q8 I.

Hypothesis sequent_P10_PI : sequent (("yc",By 1 1)::VC9) init_mem_context P10 PI.

Ltac n_in_var_context :=
  repeat match goal with 
  | [ |- ~ in_var_context _ _ ] => inversion_clear 1
  | [ H : in_var_context _ _ |- False ] => inversion_clear H
  end.

Lemma check_loop :
      check_postcondition VC8 P8 loop "z" (By 2 1) I loop'.
  assert (pf2  : in_var_context "P" VC8). do 6 step; apply InHead.
  assert (pf2z : in_var_context "P" (("z",By 2 1)::VC8)). step; auto.
  assert (pf2yd: in_var_context "P" VC9). step; auto.
  assert (pf2yc: in_var_context "P" VC10). step; auto.
  assert (pf2u : in_var_context "P" VC12). step; auto.
  assert (pf3  : in_var_context "Ac" VC8). do 5 step; apply InHead.
  assert (pf3z : in_var_context "Ac" (("z",By 2 1)::VC8)). step; auto.
  assert (pf3yd: in_var_context "Ac" VC9). step; auto.
  assert (pf3yc: in_var_context "Ac" VC11). step; auto.
  assert (pf3u : in_var_context "Ac" VC12). step; auto.
  assert (pf4  : in_var_context "Cc" VC8). do 4 step; apply InHead.
  assert (pf4z : in_var_context "Cc" (("z",By 2 1)::VC8)). step; auto.
  assert (pf4yd: in_var_context "Cc" VC9). step; auto.
  assert (pf4yc: in_var_context "Cc" VC10). step; auto.
  assert (pf4u : in_var_context "Cc" VC12). step; auto.
  assert (pf5  : in_var_context "Bc" VC8). do 3 step; apply InHead.
  assert (pf5z : in_var_context "Bc" (("z",By 2 1)::VC8)). step; auto.
  assert (pf5yd: in_var_context "Bc" VC9). step; auto.
  assert (pf5yc: in_var_context "Bc" VC10). step; auto.
  assert (pf5u : in_var_context "Bc" VC12). step; auto.
  assert (pf6  : in_var_context "Dc" VC8). do 2 step; apply InHead.
  assert (pf6z : in_var_context "Dc" (("z",By 2 1)::VC8)). step; auto.
  assert (pf6yd: in_var_context "Dc" VC9). step; auto.
  assert (pf6yc: in_var_context "Dc" VC10). step; auto.
  assert (pf6u : in_var_context "Dc" VC12). step; auto.
  assert (pf7  : in_var_context "y" VC8). step; apply InHead. 
  assert (pf7z : in_var_context "y" (("z",By 2 1)::VC8)). step; auto.
  assert (pf7yd: in_var_context "y" VC9). step; auto.
  assert (pf7yc: in_var_context "y" VC10). step; auto.
  assert (pf7u : in_var_context "y" VC12). step; auto.
  assert (pf8  : in_var_context "x" VC8). apply InHead.
  assert (pf8z : in_var_context "x" (("z",By 2 1)::VC8)). step; auto.
  assert (pf8yd: in_var_context "x" VC9). step; auto.
  assert (pf8yc: in_var_context "x" VC10). step; auto.
  assert (pf8u : in_var_context "x" VC12). step; auto.
  assert (pfz  : in_var_context "z" (("z",By 2 1)::VC8)). apply InHead.
  assert (pf9yd: in_var_context "yd" VC9). apply InHead.
  assert (pf10yd: in_var_context "yd" VC10). step; auto.
  assert (pf12yd: in_var_context "yd" VC12). step; auto.
  assert (pf10yc: in_var_context "yc" VC10). apply InHead.
  assert (pf12yc: in_var_context "yc" VC12). step; auto.
  assert (pf12u : in_var_context "u" VC12). apply InHead.
  apply cpConsequent with Q8; auto.
  (*check_prop P8*) apply check_prop_P8 with pf2 pf3 pf4 pf5 pf6 pf7 pf8;
    auto. repeat (split; auto); step.
  (*check_prop I I*) 
    apply check_prop_I with pf2z pf8z pfz; auto.
  (* infer P8 loop Q8 *)
    apply ipReceive; auto.
    (*check_prop P8*) apply check_prop_P8 with pf2 pf3 pf4 pf5 pf6 pf7 pf8;
      auto. repeat (split; auto); step.
    apply bind_typing with yc 
         (Annotation PI ;;
          Send (By 1 1) u (Ref 1%nat) ;;
          xc'); auto.
    (*check_prop P8*) 
      apply check_prop_P8 with pf2yd pf3yd pf4yd pf5yd pf6yd pf7yd pf8yd; auto.
      repeat (split; auto); step.
    (*check_yc*) step. step. step. 
      ciVar "y" (By 1 1) (InTail "yd" (By 1 1) pf7).
      ciVar "yd" (By 1 1) (InHead "yd" (By 1 1) VC8); auto.
    (*~in_var_ctx*) n_in_var_context.
    (*aux_reduce*) solve_hereditary_subst. 
    apply ipAnnotation with "z"; auto.
    (*check_prop*) step.
      (*check_prop_P8*) 
        apply check_prop_P8 with pf2yc pf3yc pf4yc pf5yc pf6yc pf7yc pf8yc;
        auto. repeat (split; auto); step.
      step. ciVar "yc" (By 1 1) pf10yc.
      step. step. step. 
      ciVar "y" (By 1 1) pf7yc. ciVar "yd" (By 1 1) pf10yd.
    (*check_prop PI*) apply check_prop_PI with pf10yc; auto.
    (*P10 => PI*) apply sequent_P10_PI.
    apply bind_typing with (M' := u) 
          (E' := Send (By 1 1) (Var "u") (Ref 1);; xc');
      auto.
    (*check_prop*) step. step.
       apply check_prop_subst; simpl; auto. step.
       apply check_prop_HC_weakening; [ | 
         intro H; destruct H as [H | [H | H]]; auto; inversion H].
      apply check_prop_P8 with pf2yc pf3yc pf4yc pf5yc pf6yc pf7yc pf8yc;
        auto. repeat (split; auto); step.
      step. ciVar "yc" (By 1 1) pf10yc.
      step. step. step. 
      ciVar "y" (By 1 1) pf7yc. ciVar "yd" (By 1 1) pf10yd.
      apply check_prop_subst; simpl; auto. step. apply ciCompBinop with 1%nat 1%nat; auto.
      step; ciVar "yc" (By 1 1) pf10yc.
    (*check u*)
      step. apply ciMultiply with 2%nat; auto.
      ciVar "Cc" (By 1 2) pf4yc. ciVar "x" (By 2 1) pf8yc.
      apply ciMultiply with 1%nat; auto.
      ciVar "Dc" (By 1 1) pf6yc. ciVar "yc" (By 1 1) pf10yc.
    (*~in_var_context*) n_in_var_context.
    (*aux_reduce*) solve_hereditary_subst. 
    apply ipSend; auto.
    (*check_prop*) 
        apply check_prop_P12 with pf2u pf3u pf4u pf5u pf6u pf7u pf8u 
                                  pf12yd pf12yc pf12u; auto.
        repeat (split; auto); step.
    (*check_intro_term*)
      ciVar "u" (By 1 1) pf12u.
    apply ipIntroTerm; auto. 
    (*check_prop*) 
      apply check_prop_P12 with pf2u pf3u pf4u pf5u pf6u pf7u pf8u 
                                pf12yd pf12yc pf12u; auto.
        repeat (split; auto); step.
    (*check_intro_term*) step. apply ciMultiply with 2%nat; auto.
      ciVar "Ac" (By 2 2) pf3u.
      ciVar "x" (By 2 1) pf8u.
      apply ciMultiply with 1%nat; auto.
      ciVar "Bc" (By 2 1) pf5u.
      ciVar "yc" (By 1 1) pf12yc.

  (*Q8 ==> I*) apply sequent_Q8_I.
Qed.


Lemma seq_J1_J2_I : forall VC pf2 pf3 pf4 pf5 pf6 pf7 pf14 pfx pfw,
      goodVC14 VC pf2 pf3 pf4 pf5 pf6 pf7 pf14 ->
      get "x" VC pfx = By 2 1 ->
      get "w" VC pfw = By 2 1 ->
      sequent VC init_mem_context (J1 /"w"\ J2) I.
Proof.
  intros until pfw; destruct 1 as [H14 [H7 [H6 [H5 [H4 [H3 [H2 H1]]]]]]].
  intros.
  assert (~ List.In "w" init_mem_context).
    simpl. destruct 1 as [i | [i | i]]; auto; inversion i. 
  apply sExistsHeapElim; auto; simpl.
  (*wf*) step. apply check_prop_I with pf2 pfx pf14; auto.
  apply sAnd2; auto.
  (*wf*) step. apply check_prop_HC_weakening; [idtac | auto].
    step. 
      step; [apply check_PEps with pf2 pfw | apply check_PEps with pf2 pf14]; auto.
      step; [apply check_PEps with pf2 pfx | apply check_PEps with pf2 pfw]; auto.
  (*PEps (Var "x")*) apply sAnd1; auto.
    (*wf*) step. apply check_prop_HC_weakening; auto. apply check_PEps with pf2 pfx; auto.
    apply sWeak1; auto.
    (*wf*) step. apply check_prop_HC_weakening; auto. step.
      apply check_PEps with pf2 pfx; auto. apply check_PEps with pf2 pfw; auto.
    (*wf*) step. apply check_prop_HC_weakening; auto.
      apply check_PEps with pf2 pfx; auto.
    apply sAnd1; auto.
    (*wf*) step. apply check_prop_HC_weakening; auto.
      apply check_PEps with pf2 pfx; auto.
    apply sEq; auto.
    (*wf*) step. apply check_prop_HC_weakening; auto.
      apply check_PEps with pf2 pfw; auto.
  (*PEps (Var "z")*) apply sAnd1; auto.
    (*wf*) step. apply check_prop_HC_weakening; auto.
      apply check_PEps with pf2 pf14; auto.
    apply sAnd1; auto.
    (*wf*) step. apply check_prop_HC_weakening; auto. step.
      apply check_PEps with pf2 pfx; auto. 
      apply check_PEps with pf2 pfw; auto.
    (*wf*) step. apply check_prop_HC_weakening; auto. 
      apply check_PEps with pf2 pf14; auto. 
    apply sWeak1; auto.
    (*wf*) step. step; apply check_prop_HC_weakening; auto.
      step.
      apply check_PEps with pf2 pfx; auto.
      apply check_PEps with pf2 pfw; auto.
      apply check_prop_HC_weakening; auto.
      apply check_PEps with pf2 pf14; auto.
    (*wf*) step. apply check_prop_HC_weakening; auto.
      apply check_PEps with pf2 pf14; auto.
    apply sEq; auto.
    (*wf*) step. apply check_prop_HC_weakening; auto. step.
      apply check_PEps with pf2 pfx; auto.
      apply check_PEps with pf2 pfw; auto.
Qed.

Lemma seq_I_J : sequent (("x",By 2 1)::("z",By 2 1)::VC7)
      init_mem_context I J.
  assert (pfP : in_var_context "P" (("x",By 2 1)::("z",By 2 1)::VC7)).
    do 7 apply InTail; apply InHead.
  assert (pfz : in_var_context "z" (("x",By 2 1)::("z",By 2 1)::VC7)).
    apply InTail; apply InHead.
  assert (wf_prop_context (("x",By 2 1)::("z",By 2 1)::VC7) init_mem_context J).
    do 2 step; apply check_PEps with pfP pfz; auto.
  apply sAnd1; auto.
  apply sWeak1; auto.
  (*wf PEps*) step. apply check_PEps with pfP pfz; auto. 
  apply sAnd2; auto.
  (*wf PEps*) step. apply check_PEps with pfP pfz; auto.
Qed.

Theorem type_prog : infer_postcondition VC1 P1 prog "w" Unit Q1 prog'.
  apply bind_typing with P (Receive "y" (By 1 1) (Ref 2%nat) ;;
                            Loop "z" I xc (By 2 1) "x" (Boolean true) "x" 
                             (Receive "yd" (By 1 1) (Ref 3%nat);;
                              Annotation PI' ;;
           Send (By 1 1) (Binop Plus (Binop Multiply Cc (Var "x")) 
                                     (Binop Multiply Dc yc)) (Ref 1%nat);;
           Binop Plus (Binop Multiply Ac (Var "x")) (Binop Multiply Bc yc));;
                            TT); auto.
    inversion 1.
    (*aux_reduce*) step. step. step. inversion 1. step; try (inversion 1).
      (*prop*) do 4 step. do 3 step; inversion 1. step.
        (*P*) apply hsElimShape with (getShape (By 2 2)); auto.
        do 2 step; inversion 1.
        step. do 2 step; inversion 1. step.
        (*P*) apply hsElimShape with (getShape (By 2 2)); auto.
        do 2 step; inversion 1.
      (*xc*) step.
      (*loop'*) step. inversion 1. step.
        (*PI'*) step. step. do 6 step; inversion 1.
        step. 
        (*u'*) step. step. step. do 2 step; inversion 1.
          step. step. step. step. do 3 step; inversion 1.
        (*xc''*) step. step. step. step. do 2 step; inversion 1.
          step. step. step. step. do 3 step; inversion 1.
  apply bind_typing with Ac (Receive "y" (By 1 1) (Ref 2);;
                             Loop "z" I xc (By 2 1) "x" (Boolean true) "x"
                                (Receive "yd" (By 1 1) (Ref 3%nat);;
                                 Annotation PI';;
       Send (By 1 1) (Binop Plus (Binop Multiply Cc (Var "x"))
                                      (Binop Multiply Dc yc)) (Ref 1%nat);;
       Binop Plus (Binop Multiply (Var "Ac") (Var "x")) (Binop Multiply Bc yc));;
                             TT); auto.
    (*check_prop*) apply check_prop_P2 with (InHead "P" (By 2 2) VC1); auto.
      repeat (split; auto). step.
    (*in_var_context*) n_in_var_context.
    (*aux_reduce*) do 3 step. inversion 1. step; try (inversion 1).
      (*I*) do 7 step; inversion 1.
      (*xc*) step.
      step. inversion 1. step.
      (*PI'*) do 8 step; inversion 1.
      step.
      (*u*) step.
        do 3 step; inversion 1.
        do 6 step; inversion 1.
      (*xc*) do 2 step.
        step. apply hsElimShape with (getShape (By 2 2)); auto.
          do 2 step; inversion 1.
        do 6 step; inversion 1.
  apply bind_typing with Cc (Receive "y" (By 1 1) (Ref 2%nat);;
                             Loop "z" I xc (By 2 1) "x" (Boolean true) "x"
                                (Receive  "yd" (By 1 1) (Ref 3%nat);;
                                Annotation PI';;
        Send (By 1 1) (Binop Plus (Binop Multiply (Var "Cc") (Var "x"))
                                  (Binop Multiply Dc yc)) (Ref 1%nat);;
       Binop Plus (Binop Multiply (Var "Ac")(Var "x")) (Binop Multiply Bc yc));;
                             TT); auto.
    (*check_prop*) 
      assert (pf2 : in_var_context "P" VC3). apply InTail; apply InHead.
      assert (pf3 : in_var_context "Ac" VC3). apply InHead.
      apply check_prop_P3 with pf2 pf3; repeat split; auto; step. 
    (*in_var_context*) n_in_var_context.
    (*aux_reduce*) solve_hereditary_subst; inversion 1.
  apply bind_typing with Bc (Receive "y" (By 1 1) (Ref 2%nat);;
                             Loop "z" I xc (By 2 1) "x" (Boolean true) "x"
                               (Receive "yd" (By 1 1) (Ref 3%nat);;
                                Annotation PI';;
        Send (By 1 1) (Binop Plus (Binop Multiply (Var "Cc") (Var "x"))
                                  (Binop Multiply Dc yc)) (Ref 1%nat);;
                                xc'');; TT); auto.
    (*check_prop*) 
      assert (pf2 : in_var_context "P" VC4). do 2 apply InTail; apply InHead.
      assert (pf3 : in_var_context "Ac" VC4). do 1 apply InTail; apply InHead.
      assert (pf4 : in_var_context "Cc" VC4). apply InHead.
      apply check_prop_P4 with pf2 pf3 pf4. repeat split; auto. step.
    (*n_in_var_context*) n_in_var_context.
    (*aux_reduce*) solve_hereditary_subst; inversion 1.
  apply bind_typing with Dc (Receive "y" (By 1 1) (Ref 2%nat);;
                             Loop "z" I xc (By 2 1) "x" (Boolean true) "x"
                               (Receive "yd" (By 1 1) (Ref 3%nat);;
                                Annotation PI';;
                                Send (By 1 1) u' (Ref 1%nat);;
                                xc'');; TT); auto.
    (*check_prop*) 
      assert (pf2 : in_var_context "P"  VC5). do 3 apply InTail; apply InHead.
      assert (pf3 : in_var_context "Ac" VC5). do 2 apply InTail; apply InHead.
      assert (pf4 : in_var_context "Cc" VC5). do 1 apply InTail; apply InHead.
      assert (pf5 : in_var_context "Bc" VC5). do 0 apply InTail; apply InHead.
      apply check_prop_P5 with pf2 pf3 pf4 pf5; auto. repeat split; auto. step.
    (*n_in_var_context*) n_in_var_context.
    (*aux_reduce*) solve_hereditary_subst; inversion 1.
  apply ipReceive; auto.
    (*check_prop*) 
      assert (pf2 : in_var_context "P"  VC6). do 4 apply InTail; apply InHead.
      assert (pf3 : in_var_context "Ac" VC6). do 3 apply InTail; apply InHead.
      assert (pf4 : in_var_context "Cc" VC6). do 2 apply InTail; apply InHead.
      assert (pf5 : in_var_context "Bc" VC6). do 1 apply InTail; apply InHead.
      assert (pf6 : in_var_context "Dc" VC6). do 0 apply InTail; apply InHead.
      apply check_prop_P6 with pf2 pf3 pf4 pf5 pf6. repeat split; auto. step.
  apply ipLoop with I''' I'''' J J1 J2 J3 J4 (Boolean true); auto.
    (*~ x in context*) n_in_var_context.
    (*~ z in context*) n_in_var_context.
    (*~ w in context*) n_in_var_context.
    (*check_prop*) 
      assert (pf2 : in_var_context "P"  VC7). do 5 apply InTail; apply InHead.
      assert (pf3 : in_var_context "Ac" VC7). do 4 apply InTail; apply InHead.
      assert (pf4 : in_var_context "Cc" VC7). do 3 apply InTail; apply InHead.
      assert (pf5 : in_var_context "Bc" VC7). do 2 apply InTail; apply InHead.
      assert (pf6 : in_var_context "Dc" VC7). do 1 apply InTail; apply InHead.
      assert (pf7 : in_var_context "y"  VC7). do 0 apply InTail; apply InHead.
      apply check_prop_P7 with pf2 pf3 pf4 pf5 pf6 pf7. repeat split; auto. step.
    (*check_prop_I*) 
      assert (pf2 : in_var_context "P"  (("x",By 2 1)::VC14)). do 7 apply InTail; apply InHead.
      assert (pf3 : in_var_context "Ac" (("x",By 2 1)::VC14)). do 6 apply InTail; apply InHead.
      assert (pf4 : in_var_context "Cc" (("x",By 2 1)::VC14)). do 5 apply InTail; apply InHead.
      assert (pf5 : in_var_context "Bc" (("x",By 2 1)::VC14)). do 4 apply InTail; apply InHead.
      assert (pf6 : in_var_context "Dc" (("x",By 2 1)::VC14)). do 3 apply InTail; apply InHead.
      assert (pf7 : in_var_context "y"  (("x",By 2 1)::VC14)). do 2 apply InTail; apply InHead.
      assert (pf8 : in_var_context "x"  (("x",By 2 1)::VC14)). apply InHead.
      assert (pf14 : in_var_context "z" (("x",By 2 1)::VC14)). do 1 apply InTail; apply InHead.
      apply check_prop_I with pf2 pf8 pf14; auto.
    (*[mem/init]I = I'''*) solve_hereditary_subst.
    (*[xc/x]I'''=I''''*) solve_hereditary_subst.
    (*P7 ==> I''''*) apply seq_P7_I.
    (*[w/x]I = J1*) solve_hereditary_subst.
    (*[w/z]I = J2*) solve_hereditary_subst.
    (*J1 /\ J2 ==> I*) 
      set (VC := (("x",By 2 1)::("z",By 2 1)::("w",By 2 1)::VC7)). 
      assert (pf2 : in_var_context "P"  VC). do 8 apply InTail; apply InHead.
      assert (pf3 : in_var_context "Ac" VC). do 7 apply InTail; apply InHead.
      assert (pf4 : in_var_context "Cc" VC). do 6 apply InTail; apply InHead.
      assert (pf5 : in_var_context "Bc" VC). do 5 apply InTail; apply InHead.
      assert (pf6 : in_var_context "Dc" VC). do 4 apply InTail; apply InHead.
      assert (pf7 : in_var_context "y"  VC). do 3 apply InTail; apply InHead.
      assert (pf14 : in_var_context "z" VC). do 1 apply InTail; apply InHead.
      assert (pfx : in_var_context "x"  VC). apply InHead.
      assert (pfw : in_var_context "w"  VC). do 2 apply InTail; apply InHead.
      apply seq_J1_J2_I with pf2 pf3 pf4 pf5 pf6 pf7 pf14 pfx pfw; auto.
        repeat split; auto. step.
    (*[mem/init]I = J*) solve_hereditary_subst.
    (*I ==> J*) apply seq_I_J.
    (*[x/z]I = J3*) solve_hereditary_subst.
    (*check loop*) apply check_loop.
    (*[xc/x]I = J4*) solve_hereditary_subst.
  apply ipIntroTerm; auto.
    (*check_prop*)
      assert (pf2 : in_var_context "P"  VC14). do 6 apply InTail; apply InHead.
      assert (pf3 : in_var_context "Ac" VC14). do 5 apply InTail; apply InHead.
      assert (pf4 : in_var_context "Cc" VC14). do 4 apply InTail; apply InHead.
      assert (pf5 : in_var_context "Bc" VC14). do 3 apply InTail; apply InHead.
      assert (pf6 : in_var_context "Dc" VC14). do 2 apply InTail; apply InHead.
      assert (pf7 : in_var_context "y"  VC14). do 1 apply InTail; apply InHead.
      assert (pf14 : in_var_context "z" VC14). do 0 apply InTail; apply InHead.
      apply check_prop_P14' with pf2 pf3 pf4 pf5 pf6 pf7 pf14. repeat split; auto. step.
Qed.
                                


