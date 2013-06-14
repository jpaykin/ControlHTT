Require Import List String.
Require Import mymatrices syntax context.
Set Implicit Arguments.

Inductive shape : Set :=
| sUnit | sNat | sBool | sMatrix
| sDiamond : shape -> shape.

Definition shape_dec : forall (s1 s2 : shape), {s1 = s2} + {s1 <> s2}.
  decide equality.
Defined.

Inductive shape_le : shape -> shape -> Prop :=
| sId : forall (s : shape), shape_le s s
| sDiamondLe : forall s s', shape_le s s' -> shape_le s (sDiamond s').
Hint Constructors shape_le.

Definition shape_le_dec : forall s1 s2, {shape_le s1 s2} + {~ shape_le s1 s2}.
Proof.
  induction s1; induction s2; 
  try (left; auto; fail); try (right; inversion 1; fail);
  repeat match goal with
  | [ IH : {shape_le _ _} + {~ shape_le _ _} |- _ ] => destruct IH
  end;
  try (left; auto; fail); try (right; inversion 1; auto; fail).
  destruct (shape_dec s1 s2);
  try (right; inversion 1; auto; fail).
  rewrite e; auto.
Defined. 

Fixpoint getShape (A : type) : shape :=
  match A with
  | Unit => sUnit
  | Nat => sNat
  | Bool => sBool
  | Matrix _ _ => sMatrix
  | Computation P x A Q => sDiamond (getShape A)
  end.

Fixpoint getType (S : shape) : type :=
  match S with
  | sUnit => Unit
  | sNat => Nat
  | sBool => Bool
  | sMatrix => Matrix 0 0
  | sDiamond S' => Computation Top "" (getType S') Top
  end.
Hint Unfold getShape getType.

Lemma type_shape_inverse : forall S, getShape (getType S) = S.
Proof.
  induction S; simpl; auto.
  rewrite IHS; auto.
Qed.

Inductive type_hereditary_subst : intro_term -> var -> shape -> type -> type -> Prop :=
| hsUnit : forall M x S, type_hereditary_subst M x S Unit Unit
| hsBool : forall M x S, type_hereditary_subst M x S Bool Bool
| hsNat  : forall M x S, type_hereditary_subst M x S Nat Nat
| hsMatrix : forall M x S m n, type_hereditary_subst M x S (Matrix m n) (Matrix m n)
| hsComputationEq : forall M x S P P' A A' Q,
  proposition_hereditary_subst M x S P P' ->
  type_hereditary_subst M x S A A' ->
  type_hereditary_subst M x S (Computation P x A Q) (Computation P' x A' Q)
| hsComputationNeq : forall M x y S P P' A A' Q Q',
  x <> y ->
  proposition_hereditary_subst M x S P P' ->
  type_hereditary_subst M x S A A' ->
  proposition_hereditary_subst M x S Q Q' ->
  type_hereditary_subst M x S (Computation P y A Q) (Computation P' y A' Q')

with proposition_hereditary_subst : intro_term -> var -> shape -> proposition -> proposition -> Prop :=
(* Propositions *)
| hsId : forall M x S A A' N1 N1' N2 N2',
  type_hereditary_subst M x S A A' ->
  intro_term_hereditary_subst M x S N1 N1' ->
  intro_term_hereditary_subst M x S N2 N2' ->
  proposition_hereditary_subst M x S (Id A N1 N2) (Id A' N1' N2')
| hsHId : forall M x S h1 h1' h2 h2',
  heap_hereditary_subst M x S h1 h1' ->
  heap_hereditary_subst M x S h2 h2' ->
  proposition_hereditary_subst M x S (HId h1 h2) (HId h1' h2')
| hsIndom : forall M x S h h' N N',
  heap_hereditary_subst M x S h h' ->
  intro_term_hereditary_subst M x S N N' ->
  proposition_hereditary_subst M x S (Indom h N) (Indom h' N')
| hsTop : forall M x S, proposition_hereditary_subst M x S Top Top
| hsBottom : forall M x S, proposition_hereditary_subst M x S Bottom Bottom
| hsAnd : forall M x S P P' Q Q',
  proposition_hereditary_subst M x S P P' ->
  proposition_hereditary_subst M x S Q Q' ->
  proposition_hereditary_subst M x S (And P Q) (And P' Q')
| hsOr : forall M x S P P' Q Q',
  proposition_hereditary_subst M x S P P' ->
  proposition_hereditary_subst M x S Q Q' ->
  proposition_hereditary_subst M x S (Or P Q) (Or P' Q')
| hsImplies : forall M x S P P' Q Q',
  proposition_hereditary_subst M x S P P' ->
  proposition_hereditary_subst M x S Q Q' ->
  proposition_hereditary_subst M x S (Implies P Q) (Implies P' Q')
| hsNot : forall M x S P P',
  proposition_hereditary_subst M x S P P' ->
  proposition_hereditary_subst M x S (Not P) (Not P')
| hsExistsEq : forall M x S A A' P,
  type_hereditary_subst M x S A A' -> 
  proposition_hereditary_subst M x S (Exists x A P) (Exists x A' P)
| hsExistsNeq : forall M x S y A A' P P', x <> y ->
  type_hereditary_subst M x S A A' -> 
  proposition_hereditary_subst M x S P P' ->
  proposition_hereditary_subst M x S (Exists y A P) (Exists y A' P')
| hsForAllEq :  forall M x S A A' P, 
  type_hereditary_subst M x S A A' -> 
  proposition_hereditary_subst M x S (ForAll x A P) (ForAll x A' P)
| hsForAllNeq :  forall M x S y A A' P P', x <> y ->
  type_hereditary_subst M x S A A' -> 
  proposition_hereditary_subst M x S P P' ->
  proposition_hereditary_subst M x S (ForAll y A P) (ForAll y A' P')
| hsExistsHeap : forall M x S y P P', 
  proposition_hereditary_subst M x S P P' ->
  proposition_hereditary_subst M x S (ExistsHeap y P) (ExistsHeap y P')
| hsForAllHeap : forall M x S y P P', 
  proposition_hereditary_subst M x S P P' ->
  proposition_hereditary_subst M x S (ForAllHeap y P) (ForAllHeap y P')

with heap_hereditary_subst : intro_term -> var -> shape -> heap -> heap -> Prop :=
| hsHVar : forall M x S y, (*x <> y ->*)
  heap_hereditary_subst M x S (HVar y) (HVar y)
| hsHEmpty : forall M x S, heap_hereditary_subst M x S HEmpty HEmpty
| hsHUpdate : forall M x S h h' N1 N1' N2 N2' A A',
  heap_hereditary_subst M x S h h' ->
  intro_term_hereditary_subst M x S N1 N1' ->
  intro_term_hereditary_subst M x S N2 N2' ->
  type_hereditary_subst M x S A A' ->
  heap_hereditary_subst M x S (HUpdate h N1 N2 A) (HUpdate h' N1' N2' A')

with elim_term_hereditary_subst : intro_term -> var -> shape -> elim_term -> elim_term + (intro_term * shape) -> Prop :=
| hsVarEq : forall M x S, elim_term_hereditary_subst M x S (Var x) (inr (M,S))
| hsVarNeq : forall M x S y, x<>y -> elim_term_hereditary_subst M x S (Var y) (inl (Var y))

with intro_term_hereditary_subst : intro_term -> var -> shape -> intro_term -> intro_term -> Prop :=
| hsElim : forall M x S K K',
  elim_term_hereditary_subst M x S K (inl K') ->
  intro_term_hereditary_subst M x S K K'
| hsElimShape : forall M x S K N' S',
  elim_term_hereditary_subst M x S K (inr (N',S')) ->
  intro_term_hereditary_subst M x S K N'
| hsTT : forall M x S,
  intro_term_hereditary_subst M x S TT TT
| hsBoolean : forall M x S b,
  intro_term_hereditary_subst M x S (Boolean b) (Boolean b)
| hsRef : forall M x S n,
  intro_term_hereditary_subst M x S (Ref n) (Ref n)
| hsDia : forall M x S E E',
  computation_hereditary_subst M x S E E' ->
  intro_term_hereditary_subst M x S (Dia E) (Dia E')
| hsMat : forall M x S m n (N : numMatrix m n),
  intro_term_hereditary_subst M x S (Mat N) (Mat N)
| hsUnop : forall M x S u N N',
  intro_term_hereditary_subst M x S N N' ->
  intro_term_hereditary_subst M x S (Unop u N) (Unop u N')
| hsBinop : forall M x S b N1 N1' N2 N2',
  intro_term_hereditary_subst M x S N1 N1' ->
  intro_term_hereditary_subst M x S N2 N2' ->
  intro_term_hereditary_subst M x S (Binop b N1 N2) (Binop b N1' N2')
| hsSelect : forall M x S N1 N1' N2 N2',
  intro_term_hereditary_subst M x S N1 N1' ->
  intro_term_hereditary_subst M x S N2 N2' ->
  intro_term_hereditary_subst M x S (Select N1 N2) (Select N1' N2')

with computation_hereditary_subst : intro_term -> var -> shape -> computation -> computation -> Prop :=
| hsIntro : forall M x S N N',
  intro_term_hereditary_subst M x S N N' ->
  computation_hereditary_subst M x S N N'
| hsLetDiaElimEq : forall M x S K E K',
  elim_term_hereditary_subst M x S K (inl K') ->
  computation_hereditary_subst M x S
    (Let dia x <- K in E) (Let dia x <- K' in E)
| hsLetDiaElimNeq : forall M x S y K E K' E', x <> y ->
  elim_term_hereditary_subst M x S K (inl K') ->
  computation_hereditary_subst M x S E E' ->
  computation_hereditary_subst M x S 
    (Let dia y <- K in E) (Let dia y <- K' in E')
| hsLetDiaIntroEq : forall M x S K E F S' F', 
  elim_term_hereditary_subst M x S K (inr (Dia F, sDiamond S')) ->
(*  computation_hereditary_subst M x S E E' ->*)
  shape_le (sDiamond S') S ->
  monadic_subst F x S' E F' ->
  computation_hereditary_subst M x S (Let dia x <- K in E) F'
| hsLetDiaIntroNeq : forall M x S y K E F S' E' F', x <> y ->
  elim_term_hereditary_subst M x S K (inr (Dia F, sDiamond S')) ->
  computation_hereditary_subst M x S E E' ->
  shape_le (sDiamond S') S ->
  monadic_subst F y S' E' F' ->
  computation_hereditary_subst M x S (Let dia y <- K in E) F'
| hsAllocEq : forall M x S N A E N' A',
  intro_term_hereditary_subst M x S N N' ->
  type_hereditary_subst M x S A A' ->
  computation_hereditary_subst M x S (Alloc x N A;; E) (Alloc x N' A';; E)
| hsAllocNeq : forall M x S y N A E N' A' E', x <> y ->
  intro_term_hereditary_subst M x S N N' ->
  type_hereditary_subst M x S A A' ->
  computation_hereditary_subst M x S E E' ->
  computation_hereditary_subst M x S (Alloc y N A;; E) (Alloc y N' A';; E')
| hsDeallocEq : forall M x S N A E N' A',
  intro_term_hereditary_subst M x S N N' ->
  type_hereditary_subst M x S A A' ->
  computation_hereditary_subst M x S (Dealloc x N A;; E) (Dealloc x N' A';; E)
| hsDealloc : forall M x S y N A E N' A' E', x <> y -> 
  intro_term_hereditary_subst M x S N N' ->
  type_hereditary_subst M x S A A' ->
  computation_hereditary_subst M x S E E' -> 
  computation_hereditary_subst M x S (Dealloc y N A;; E) (Dealloc y N' A';; E')
| hsLookupEq : forall M x S N A E N' A',
  intro_term_hereditary_subst M x S N N' ->
  type_hereditary_subst M x S A A' ->
  computation_hereditary_subst M x S (Lookup x N A;; E) (Lookup x N' A';; E)
| hsLookup : forall M x S y N A E N' A' E', x <> y ->
  intro_term_hereditary_subst M x S N N' ->
  type_hereditary_subst M x S A A' ->
  computation_hereditary_subst M x S E E' ->
  computation_hereditary_subst M x S (Lookup y N A;; E) (Lookup y N' A';; E')
| hsMutate : forall M x S N1 N2 A E N1' N2' A' E',
  intro_term_hereditary_subst M x S N1 N1' ->
  intro_term_hereditary_subst M x S N2 N2' ->
  type_hereditary_subst M x S A A' ->
  computation_hereditary_subst M x S E E' ->
  computation_hereditary_subst M x S (Mutate N1 N2 A;;E) (Mutate N1' N2' A';;E')
| hsIfEq : forall M x S N A E1 E2 F N' A' E1' E2',
  intro_term_hereditary_subst M x S N N' ->
  type_hereditary_subst M x S A A' ->
  computation_hereditary_subst M x S E1 E1' ->
  computation_hereditary_subst M x S E2 E2' ->
  computation_hereditary_subst M x S (If x N A E1 E2;;F) (If x N' A' E1' E2';;F)
| hsIfNeq : forall M x S y N A E1 E2 F N' A' E1' E2' F', x <> y -> 
  intro_term_hereditary_subst M x S N N' ->
  type_hereditary_subst M x S A A' ->
  computation_hereditary_subst M x S E1 E1' ->
  computation_hereditary_subst M x S E2 E2' ->
  computation_hereditary_subst M x S F F' ->
  computation_hereditary_subst M x S (If y N A E1 E2;;F) (If y N' A' E1' E2';;F')
| hsLoop_xyzNeq : forall M x S y I N1 A z N2 E F I' N1' A' N2' E' F', 
  x <> y -> x <> z -> 
  proposition_hereditary_subst M x S I I' ->
  intro_term_hereditary_subst M x S N1 N1' ->
  type_hereditary_subst M x S A A' ->
  intro_term_hereditary_subst M x S N2 N2' ->
  computation_hereditary_subst M x S E E' ->
  computation_hereditary_subst M x S F F' ->
  computation_hereditary_subst M x S (Loop y I N1 A z N2 z E;; F)
                                     (Loop y I' N1' A' z N2' z E';; F')
| hsLoop_xyNeq : forall M x S y I N1 A N2 E F N1' A' F', 
  x <> y ->
  intro_term_hereditary_subst M x S N1 N1' ->
  type_hereditary_subst M x S A A' ->
  computation_hereditary_subst M x S F F' ->
  computation_hereditary_subst M x S (Loop y I N1 A x N2 x E;; F)
                                     (Loop y I N1' A' x N2 x E;; F')
| hsLoop_xzNeq : forall M x S I N1 A z N2 E F N1' A' N2' E', 
  x <> z -> 
  intro_term_hereditary_subst M x S N1 N1' ->
  type_hereditary_subst M x S A A' ->
  intro_term_hereditary_subst M x S N2 N2' ->
  computation_hereditary_subst M x S E E' ->
  computation_hereditary_subst M x S (Loop x I N1 A z N2 z E;; F)
                                     (Loop x I N1' A' z N2' z E';; F)
| hsLoopEq : forall M x S I N1 A N2 E F N1' A', 
  intro_term_hereditary_subst M x S N1 N1' ->
  type_hereditary_subst M x S A A' ->
  computation_hereditary_subst M x S (Loop x I N1 A x N2 x E;; F)
                                     (Loop x I N1' A' x N2 x E;; F)
| hsAnnotation : forall M x S P E P' E',
  proposition_hereditary_subst M x S P P' ->
  computation_hereditary_subst M x S E E' ->
  computation_hereditary_subst M x S (Annotation P;; E) (Annotation P';; E')
| hsSend : forall M x S A N1 N2 E A' N1' N2' E',
  type_hereditary_subst M x S A A' ->
  intro_term_hereditary_subst M x S N1 N1' ->
  intro_term_hereditary_subst M x S N2 N2' ->
  computation_hereditary_subst M x S E E' ->
  computation_hereditary_subst M x S (Send A N1 N2;; E) (Send A' N1' N2';; E')
| hsReceiveEq : forall M x S A N E A' N',
  type_hereditary_subst M x S A A' ->
  intro_term_hereditary_subst M x S N N' ->
  computation_hereditary_subst M x S (Receive x A N;; E) (Receive x A' N';; E)
| hsReceiveNeq : forall M x S y A N E A' N' E', x <> y ->
  type_hereditary_subst M x S A A' ->
  intro_term_hereditary_subst M x S N N' ->
  computation_hereditary_subst M x S E E' ->
  computation_hereditary_subst M x S (Receive y A N;; E) (Receive y A' N';; E')

with monadic_subst : computation -> var -> shape -> computation -> computation -> Prop :=
| msIntro : forall (M:intro_term) x S F F',
  computation_hereditary_subst M x S F F' ->
  monadic_subst M x S F F'
| msLetDia : forall y K E x S F F', 
  monadic_subst E x S F F' ->
  monadic_subst (Let dia y <- K in E) x S F (Let dia y <- K in F')
| msSeq : forall c E x S F F',
  monadic_subst E x S F F' -> 
  monadic_subst (Seq c E) x S F (Seq c F')
.
Hint Constructors type_hereditary_subst
                  proposition_hereditary_subst 
                  heap_hereditary_subst
                  elim_term_hereditary_subst
                  intro_term_hereditary_subst
                  computation_hereditary_subst
                  monadic_subst.


Scheme type_subst_mut := Induction for type_hereditary_subst Sort Prop 
with proposition_subst_mut := Induction for proposition_hereditary_subst Sort Prop
with heap_subst_mut := Induction for heap_hereditary_subst Sort Prop
with elim_subst_mut := Induction for elim_term_hereditary_subst Sort Prop
with intro_subst_mut := Induction for intro_term_hereditary_subst Sort Prop
with computation_subst_mut := Induction for computation_hereditary_subst Sort Prop
with monadic_mut := Induction for monadic_subst Sort Prop.


Lemma shape_descent : forall M x S K N' S', 
      elim_term_hereditary_subst M x S K (inr (N',S')) ->
      shape_le S' S.
Proof.
  induction K; intros.
  (*Var*) inversion H. auto.
  (*Cast*) inversion H.
Qed. 

(* Normal Substitution for Heap Variables *)

Fixpoint prop_subst (x : heap_var) (h : heap) (P : proposition) :=
  match P with
  | Id A M1 M2 => Id (type_subst x h A) M1 M2
  | HId h1 h2 => HId (heap_subst x h h1) (heap_subst x h h2)
  | Indom h' M => Indom (heap_subst x h h') M
  | And P1 P2 => And (prop_subst x h P1) (prop_subst x h P2)
  | Or P1 P2 => Or (prop_subst x h P1) (prop_subst x h P2)
  | Implies P1 P2 => Implies (prop_subst x h P1) (prop_subst x h P2)
  | Not P' => Not (prop_subst x h P')
  | Exists y A P' => Exists y (type_subst x h A) (prop_subst x h P')
  | ForAll y A P' => ForAll y (type_subst x h A) (prop_subst x h P')
  | ExistsHeap y P' => if var_dec x y then ExistsHeap y P' else
    ExistsHeap y (prop_subst x h P')
  | ForAllHeap y P' => if var_dec x y then ForAllHeap y P' else
    ForAllHeap y (prop_subst x h P') 
  | _ => P
  end

with heap_subst (x : heap_var) (h h' : heap) :=
  match h' with
  | HVar y => if var_dec x y then h else (HVar y)
  | HEmpty => HEmpty
  | HUpdate h'' M N A => HUpdate (heap_subst x h h'') M N (type_subst x h A)
  end
 
with type_subst (x : heap_var) (h : heap) (A : type) :=
  match A with
  | Computation P1 y A' P2 => Computation (prop_subst x h P1) y (type_subst x h A') (prop_subst x h P2)
  | _ => A
  end.


Lemma prop_subst_id : forall P x, 
      prop_subst x (HVar x) P = P.
Proof. About proposition_mut.
  apply (proposition_mut
    (fun A : type => forall x, type_subst x (HVar x) A = A)
    (fun P : proposition => forall x, prop_subst x (HVar x) P = P)
    (fun h : heap => forall x, heap_subst x (HVar x) h = h)
    (fun K : elim_term => True)
    (fun M : intro_term => True)
    (fun E : computation => True)
    (fun c : command => True)); intros; simpl; auto.
  rewrite H. rewrite H1. rewrite H0. reflexivity.
  rewrite H; reflexivity.
  rewrite H, H0; reflexivity.
  rewrite H; reflexivity.
  rewrite H, H0; reflexivity.
  rewrite H, H0; reflexivity.
  rewrite H, H0; reflexivity.
  rewrite H; reflexivity.
  rewrite H, H0; reflexivity.
  rewrite H, H0; reflexivity.
  rewrite H; auto. destruct (var_dec x h); reflexivity.
  rewrite H; auto. destruct (var_dec x h); reflexivity.
  destruct (var_dec x h); auto. rewrite e; reflexivity.
  rewrite H, H2; reflexivity.
Qed.  

Lemma type_subst_id : forall x A,
      type_subst x (HVar x) A = A.
  induction A; simpl; auto.
  do 2 rewrite prop_subst_id; auto. rewrite IHA; auto.
Qed.