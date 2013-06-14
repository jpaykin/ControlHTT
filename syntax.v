Require Import List Bool Reals String.
Require Import matrices mymatrices.
Set Implicit Arguments.

Open Scope string.
Open Scope list.

Definition var := string.
Definition heap_var := string.
Definition var_dec := string_dec.
Definition heap_var_dec := string_dec.

Inductive num_binop := Plus | Times | Minus | Divide | Min | Max.
Inductive bool_binop := bAnd | bOr.
Inductive comp_binop := bEq | bNeq | bLe.
Inductive unop :=
| Transpose | Inverse | Neg | BNot.
Inductive binop :=
| Multiply (* matrix multiplication *)
| NumBinop : num_binop -> binop
| BoolBinop : bool_binop -> binop
| CompBinop : comp_binop -> binop.

Coercion NumBinop : num_binop >-> binop.
Coercion BoolBinop : bool_binop >-> binop.
Coercion CompBinop : comp_binop >-> binop.

(* idx min max m n : return the index into a min x max-sized
   matrix stored in the heap. *)
Definition idx (M N m n : nat) := m * N + n.

Inductive type :=
| Unit | Nat | Bool
| Matrix : nat -> nat -> type
| Computation : proposition -> var -> type -> proposition -> type 

with proposition :=
| Id : type -> intro_term -> intro_term -> proposition 
| HId : heap -> heap -> proposition
| Indom : heap -> intro_term -> proposition
| Top | Bottom 
| And : proposition -> proposition -> proposition
| Or : proposition -> proposition -> proposition
| Implies : proposition -> proposition -> proposition
| Not : proposition -> proposition

| Exists : var -> type -> proposition -> proposition
| ForAll : var -> type -> proposition -> proposition
| ExistsHeap : heap_var -> proposition -> proposition
| ForAllHeap : heap_var -> proposition -> proposition

with heap :=
| HVar : heap_var -> heap | HEmpty 
| HUpdate : heap -> intro_term -> intro_term -> type -> heap

with elim_term :=
| Var : var -> elim_term | Cast : intro_term -> type -> elim_term

with intro_term :=
| ElimTerm : elim_term -> intro_term
| TT
| Boolean : bool -> intro_term
| Ref : nat -> intro_term
| Dia : computation -> intro_term
| Mat : forall m n, numMatrix m n -> intro_term
| Unop : unop -> intro_term -> intro_term
| Binop : binop -> intro_term -> intro_term -> intro_term
| Select : intro_term -> intro_term -> intro_term (* indexing into matrix *)

with computation :=
| IntroTerm : intro_term -> computation
| LetDia : var -> elim_term -> computation -> computation
| Seq : command -> computation -> computation

with command :=
| Annotation : proposition -> command
(* Allocate x M A:
   - if M:A is an mxn matrix, allocate m*n contiguous memory locations storing
     the data in M in the heap; return the pointer to the data in M
   - if M:A is a Nat or Bool, allocate a single memory location 
   *)
| Alloc : var -> intro_term -> type -> command
(* Dealloc x M A :
   - if A is an mxn matrix, deallocates the entire m*n block in memory
     referenced by M.
   - if A is Nat, Bool or Unit, deallocates the single element in memory
     location M
*)
| Dealloc : var -> intro_term -> type -> command
(* Lookup x M A :
   - if A is an m x n matrix, selects the m x n matrix stored
     in the heap at memory location M. NOTE: M CAN be an offset.
     ex: to select the 2nd row from a 3x3 numerical matrix,
         DerefMatrix x (idx 3 3 2 1) (NumericalMatrix 1 3)
   - if A is a Nat, Bool or Unit, selects the data at location M which 
     must be of type A
*)
| Lookup : var -> intro_term -> type -> command
| Mutate : intro_term -> intro_term -> type -> command
| If : var -> intro_term -> type -> computation -> computation -> command
| Loop : var -> proposition -> intro_term -> type -> var -> intro_term -> var -> computation -> command
| Send : type -> intro_term -> intro_term -> command
| Receive : var -> type -> intro_term -> command.


Scheme type_mut := Induction for type Sort Set
with proposition_mut := Induction for proposition Sort Set
with heap_mut := Induction for heap Sort Set
with elim_mut := Induction for elim_term Sort Set
with intro_mut := Induction for intro_term Sort Set
with computation_mut := Induction for computation Sort Set
with command_mut := Induction for command Sort Set.

Ltac type_discriminate := right; discriminate.
Ltac type_destruct := intro t2; destruct t2; auto; try type_discriminate.
Ltac type_injection := right; injection; auto; fail.
Ltac rewrite_vars :=
  repeat match goal with
  | [ H : ?v = ?v0 |- _ ] => rewrite H in *; clear H
  end; auto.

(* Seleq-related definitions *)
Definition seleq (A : type) (h : heap) (M N : intro_term)(x:heap_var) : proposition :=
  ExistsHeap x (HId h (HUpdate (HVar x) M N A)).
Definition seleq_ (A : type) (h : heap) (M : intro_term) (x:heap_var)(y:var) :=
  Exists y A (seleq A h M (ElimTerm (Var y)) x).

(* Coercions *)
Coercion ElimTerm : elim_term >-> intro_term.
Coercion Mat : numMatrix >-> intro_term.
Coercion IntroTerm : intro_term >-> computation.

(* Type Notation *)
Notation "{[ P ]} x ; A {[ Q ]}" := (Computation P x A Q) (at level 40).
Check ({[ Id _ TT TT ]} "hi" ; Unit {[Id _ TT TT]}).

(* Computation Notation *)
Notation "'Let' 'dia' x <- k 'in' e" := (LetDia x k e) (at level 40).
Notation "c ;; e" := (Seq c e) (at level 30, right associativity).

Definition maybeNumBinopDenote (b : num_binop) 
           : forall m n, numMatrix m n -> forall m' n', numMatrix m' n' -> option (numMatrix m n) :=
  match b with
  | Plus => maybeNumPlus
  | Times => maybeNumTimes
  | Minus => maybeNumMinus
  | Divide => maybeNumDiv
  | Min => maybeNumMin
  | Max => maybeNumMax
  end.

Definition boolBinopDenote (b : bool_binop) (b1 b2:bool) : bool :=
  match b with
  | bAnd => andb b1 b2
  | bOr => orb b1 b2
  end.

Definition maybeNatBinopDenote (b : num_binop) (n1 n2 : nat) : option nat :=
  match b with 
  | Plus => Some (n1+n2)
  | Times => Some (n1*n2)
  | Minus => Some (n1-n2)
  | Divide => None
  | Min => Some (min n1 n2)
  | Max => Some (max n1 n2)
  end.

Definition maybeNumCompBinopDenote (b : comp_binop)
           : forall m n, numMatrix m n -> forall m' n', numMatrix m' n' -> option bool :=
  match b with
  | bEq => maybe_numEqb
  | bNeq => maybe_numNeqb
  | bLe => maybe_numLeb
  end.

Fixpoint normalize (M : intro_term) : intro_term :=
  match M with
  | Unop Transpose M' => let M'' := normalize M' in
    match M'' with
    | Mat _ _ N => Mat (transpose N)
    | _ => Unop Transpose M''
    end
  | Unop Inverse M' => let M'' := normalize M' in Unop Inverse M''
  | Unop BNot M' => let M'' := normalize M' in 
    match M'' with
    | Boolean b => Boolean (negb b)
    | _ => Unop BNot M''
    end
  | Unop Neg M' => let M'' := normalize M' in 
    match M'' with
    | Mat _ _ N => Mat (numNeg N)
    | _ => Unop Neg M''
    end
  | Binop Multiply M1 M2 => 
    let M1' := normalize M1 in 
    let M2' := normalize M2 in
    match M1', M2' with
    | Mat m n N1, Mat n' p N2 =>
      match maybeNumProd N1 N2 with
      | Some N => Mat N
      | None => Binop Multiply (Mat N1) (Mat N2)
      end
    | _, _ => Binop Multiply M1' M2'
    end
  | Binop (NumBinop b) M1 M2 =>
    let M1' := normalize M1 in
    let M2' := normalize M2 in
    match M1', M2' with
    | Mat _ _ N1, Mat _ _ N2 =>
      match maybeNumBinopDenote b N1 N2 with
      | Some N => Mat N
      | None => Binop b (Mat N1) (Mat N2)
      end
    | Ref n1, Ref n2 => 
      match maybeNatBinopDenote b n1 n2 with
      | Some n => Ref n
      | None => Binop b (Ref n1) (Ref n2)
      end
    | _, _ => Binop b M1' M2'
    end
  | Binop (BoolBinop b) M1 M2 =>
    let M1' := normalize M1 in
    let M2' := normalize M2 in
    match M1', M2' with
    | Boolean b1, Boolean b2 =>
      Boolean (boolBinopDenote b b1 b2)
    | _, _ => Binop b M1' M2'
    end
  | Binop (CompBinop b) M1 M2 =>
    let M1' := normalize M1 in
    let M2' := normalize M2 in
    match M1', M2' with
    | Mat _ _ N1, Mat _ _ N2 =>
      match maybeNumCompBinopDenote b N1 N2 with
      | Some b => Boolean b
      | None => Binop b (Mat N1) (Mat N2)
      end
    | _, _ => Binop b M1' M2'
    end 
  | Select M N => 
    let M' := normalize M in
    let N' := normalize N in
    Select M' N'
  | _ => M
  end.
  

(* free variables *)
Fixpoint free_in_proposition x P :=
  match P with
  | Id A M1 M2 => free_in_type x A || free_in_intro_term x M1 || free_in_intro_term x M2
  | HId h1 h2 => free_in_heap x h1 || free_in_heap x h2
  | Indom h M => free_in_intro_term x M
  | Top => false
  | Bottom => false
  | And P1 P2 => free_in_proposition x P1 || free_in_proposition x P2
  | Or P1 P2 => free_in_proposition x P1 || free_in_proposition x P2
  | Implies P1 P2 => free_in_proposition x P1 || free_in_proposition x P2
  | Not P' => free_in_proposition x P'
  | Exists y A P' => if var_dec x y then false else (free_in_type x A || free_in_proposition x P')
  | ForAll y A P' => if var_dec x y then false else (free_in_type x A || free_in_proposition x P')
  | ExistsHeap h P' => free_in_proposition x P'
  | ForAllHeap h P' => free_in_proposition x P'
  end
with free_in_type x A :=
  match A with
  | Computation P y B Q => free_in_proposition x P || free_in_type x B ||
    (if var_dec x y then false else free_in_proposition x Q)
  | _ => false
  end
with free_in_heap x H :=
  match H with
  | HUpdate H' M N A => free_in_heap x H' || free_in_intro_term x M
                     || free_in_intro_term x N || free_in_type x A
  | _ => false
  end
with free_in_elim_term x K :=
  match K with
  | Var y => if var_dec x y then true else false
  | Cast M A => free_in_intro_term x M || free_in_type x A
  end
with free_in_intro_term x M :=
  match M with
  | ElimTerm K => free_in_elim_term x K
  | TT => false
  | Boolean _ => false
  | Ref _ => false
  | Dia E => free_in_computation x E
  | Mat _ _ _ => false
  | Unop _ M' => free_in_intro_term x M'
  | Binop _ M1 M2 => free_in_intro_term x M1 || free_in_intro_term x M2
  | Select M1 M2 => free_in_intro_term x M1 || free_in_intro_term x M2
  end
with free_in_computation x E :=
  match E with
  | IntroTerm M => free_in_intro_term x M
  | LetDia y K E' => free_in_elim_term x K || (if var_dec x y then false else free_in_computation x E')
  | Seq (Annotation P) E' => free_in_proposition x P || free_in_computation x E'
  | Seq (Alloc x' M A) E' => free_in_intro_term x M || free_in_type x A ||
    if var_dec x x' then false else free_in_computation x E'
  | Seq (Dealloc x' M A) E' => free_in_intro_term x M || free_in_type x A ||
    if var_dec x x' then false else free_in_computation x E'
  | Seq (Lookup x' M A) E' => free_in_intro_term x M || free_in_type x A ||
    if var_dec x x' then false else free_in_computation x E'
  | Seq (Mutate M N A) E' => 
    free_in_intro_term x M || free_in_intro_term x N || free_in_type x A || 
    free_in_computation x E'
  | Seq (Send A M N) E' =>
    free_in_type x A || free_in_intro_term x M || free_in_intro_term x N || 
    free_in_computation x E'
  | Seq (Receive x' A N) E' => free_in_type x A || free_in_intro_term x N ||
    if var_dec x x' then false else free_in_computation x E'
  | Seq (If x' M A E1 E2) E' => free_in_intro_term x M || free_in_type x A ||
    free_in_computation x E1 || free_in_computation x E2 ||
    if var_dec x x' then false else free_in_computation x E'
  | Seq (Loop x' P M A z1 N z2 E) E' => 
    free_in_intro_term x M || free_in_type x A ||
    (if var_dec x z1 then false else
     if var_dec x x' then false else
     free_in_proposition x P) ||
    (if var_dec x z1 then false else free_in_intro_term x N) ||
    (if var_dec x z2 then false else free_in_computation x E) ||
    (if var_dec x x' then false else free_in_computation x E')
  end.

Fixpoint heap_free_in_proposition x P :=
  match P with
  | Id A M1 M2 => heap_free_in_type x A || heap_free_in_intro_term x M1 || heap_free_in_intro_term x M2
  | HId h1 h2 => heap_free_in_heap x h1 || heap_free_in_heap x h2
  | Indom h M => heap_free_in_heap x h || heap_free_in_intro_term x M
  | Top => false
  | Bottom => false
  | And P1 P2 => heap_free_in_proposition x P1 || heap_free_in_proposition x P2
  | Or P1 P2 => heap_free_in_proposition x P1 || heap_free_in_proposition x P2
  | Implies P1 P2 => heap_free_in_proposition x P1 || heap_free_in_proposition x P2
  | Not P' => heap_free_in_proposition x P'
  | Exists y A P' => heap_free_in_type x A || heap_free_in_proposition x P'
  | ForAll y A P' => heap_free_in_type x A || heap_free_in_proposition x P'
  | ExistsHeap h P' => if heap_var_dec x h then false else heap_free_in_proposition x P'
  | ForAllHeap h P' => if heap_var_dec x h then false else heap_free_in_proposition x P'
  end
with heap_free_in_type x A :=
  match A with
  | Computation P y B Q => heap_free_in_proposition x P || heap_free_in_type x B
    || heap_free_in_proposition x Q
  | _ => false
  end
with heap_free_in_heap x H :=
  match H with
  | HUpdate H' M N A => heap_free_in_heap x H' || heap_free_in_intro_term x M
                     || heap_free_in_intro_term x N || heap_free_in_type x A
  | HVar h => if heap_var_dec x h then true else false
  | HEmpty => false
  end
with heap_free_in_elim_term x K :=
  match K with
  | Var y => false
  | Cast M A => heap_free_in_intro_term x M || heap_free_in_type x A
  end
with heap_free_in_intro_term x M :=
  match M with
  | ElimTerm K => heap_free_in_elim_term x K
  | TT => false
  | Boolean _ => false
  | Ref _ => false
  | Dia E => heap_free_in_computation x E
  | Mat _ _ _ => false
  | Unop _ M' => heap_free_in_intro_term x M'
  | Binop _ M1 M2 => heap_free_in_intro_term x M1 || heap_free_in_intro_term x M2
  | Select M1 M2 => heap_free_in_intro_term x M1 || heap_free_in_intro_term x M2
  end
with heap_free_in_computation x E :=
  match E with
  | IntroTerm M => heap_free_in_intro_term x M
  | LetDia y K E' => heap_free_in_elim_term x K || heap_free_in_computation x E'
  | Seq c E' => heap_free_in_command x c || heap_free_in_computation x E'
  end
with heap_free_in_command x c :=
  match c with
  | Annotation P => heap_free_in_proposition x P
  | Alloc y M A => heap_free_in_intro_term x M || heap_free_in_type x A
  | Dealloc y M A => heap_free_in_intro_term x M || heap_free_in_type x A
  | Lookup y M A => heap_free_in_intro_term x M || heap_free_in_type x A
  | Mutate M N A => heap_free_in_intro_term x M || heap_free_in_intro_term x N || heap_free_in_type x A
  | Send A M N => heap_free_in_type x A || heap_free_in_intro_term x M || heap_free_in_intro_term x N
  | Receive y A N => heap_free_in_type x A || heap_free_in_intro_term x N
  | If y M A E1 E2 => heap_free_in_intro_term x M || heap_free_in_type x A 
     || heap_free_in_computation x E1 || heap_free_in_computation x E2
  | Loop y P M A z1 N z2 E => heap_free_in_proposition x P || heap_free_in_intro_term x M 
    || heap_free_in_type x A || heap_free_in_intro_term x N || heap_free_in_computation x E
  end.  

