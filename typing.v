Require Import List String Arith.
Require Import mymatrices syntax context substitution.
Set Implicit Arguments.

Fixpoint aux_expand_fun (A : type) (N : intro_term) : intro_term :=
  match N with
  | ElimTerm K =>
    match A with
    | Matrix _ _ | Nat | Bool => ElimTerm K
    | Unit => TT
    | Computation P x A' Q => 
      let M := aux_expand_fun A' (Var x) in
      Dia (Let dia x <- K in M)
    end
  | _ => N
  end.

Inductive aux_reduce : 
          (*input*) type -> intro_term -> var -> computation ->
          (*output*) computation -> Prop :=
| arElim : forall A K x E, aux_reduce A (ElimTerm K) x E (Let dia x <- K in E)
| arDia : forall A F x E E',
  monadic_subst F x (getShape A) E E' ->
  aux_reduce A (Dia F) x E E'
.


(* mem and init heaps are heap variables but are used continuously as heaps *)
Definition mem := HVar "mem".
Definition init := HVar "init". 
Definition mem_context : heap_context := "mem"::nil.
Definition init_mem_context : heap_context := "init"::"mem"::nil.
Definition mem_init_context : heap_context := "mem"::"init"::nil.

(* This sequencing operator on propositions asserts that there is
   some heap in P which is the initial heap in Q *)
Definition seq_prop (P Q : proposition)(h : heap_var) : proposition :=
           ExistsHeap h (And (prop_subst "mem" (HVar h) P)
                             (prop_subst "init" (HVar h) Q)).
Notation "P / h \ Q" := (seq_prop P Q h) (at level 40).
Check (Top /"x"\ Bottom).

(* Strongest postcondition for select commands *)
Inductive sp : (*input*) command -> 
               (*output*) proposition -> Prop :=
| spAlloc   : forall x A M P, 
              P = And (HId mem (HUpdate init (Var x) M A))
                      (Not (Indom init (Var x))) ->
              sp (Alloc x M A) P
| spDealloc:  forall x A M P y,
              P = And (HId init (HUpdate mem (Var x) M A))
                 (And (Not (Indom mem (Var x)))
                      (seleq A init M (aux_expand_fun A (Var x)) y)) ->
              sp (Dealloc x M A) P
| spLookup : forall x A M P y,
              P = And (HId mem init)
                      (seleq A mem M (aux_expand_fun A (Var x)) y) ->
              sp (Lookup x M A) P
| dpMutate  : forall A M N P,
              P = HId (HVar "mem") (HUpdate (HVar "init") M N A) ->
              sp (Mutate M N A) P
.
Hint Constructors sp.

Definition sp_alloc x M A : proposition := And (HId mem (HUpdate init (Var x) M A))
                                               (Not (Indom init (Var x))).
Lemma sp_sp_alloc : forall x A M, sp (Alloc x M A) (sp_alloc x M A).
  intros; auto.
Qed.
Definition sp_lookup x M A y := And (HId mem init)
                                    (seleq A mem M (aux_expand_fun A (Var x)) y).
Lemma sp_sp_lookup : forall x M A y, sp (Lookup x M A) (sp_lookup x M A y).
  intros; eapply spLookup; reflexivity.
Qed.
Definition sp_dealloc x M A y := And (HId init (HUpdate mem (Var x) M A))
                                (And (Not (Indom mem (Var x)))
                                     (seleq A init M (aux_expand_fun A (Var x)) y)).
Lemma sp_sp_dealloc : forall x M A y, sp (Dealloc x M A) (sp_dealloc x M A y).
  intros; eapply spDealloc; reflexivity.
Qed.
Definition sp_mutate M N A := HId mem (HUpdate init M N A).
Lemma sp_sp_mutate : forall M N A, sp (Mutate M N A) (sp_mutate M N A).
  intros; auto.
Qed.

Section typing.

  (* Coercion from propositions to singleton prop contexts *)
  Definition singletonProp (P : proposition) : prop_context := P::nil.
  Coercion singletonProp : proposition >-> prop_context.

(* A variable context is well-formed if all the types in the context
   are canonical *)

Inductive wf_var_context : var_context -> Prop :=
| wfNil  : wf_var_context nil
| wfCons : forall x A VC,
           wf_var_context VC ->
           check_type VC A A -> (*A is canonical*) 
           wf_var_context ((x,A)::VC)
| wfTail : forall x y A B VC,
           wf_var_context ((x,A)::VC) ->
           wf_var_context ((y,B)::VC) ->
           free_in_type y A = false ->
           wf_var_context ((x,A)::(y,B)::VC)
           

(* A proposition context is well_formed if all the propositions in the
   context are canonical *)
with wf_prop_context : var_context -> heap_context -> prop_context -> Prop :=
| wfpNil  : forall VC HC, 
            wf_var_context VC ->
            wf_prop_context VC HC nil
| wfpCons : forall P VC HC PC,
            wf_prop_context VC HC PC ->
            check_prop VC HC P P (* P is canonical *) ->
            wf_prop_context VC HC (P::PC)

with check_type :
     (*input*) var_context -> type ->
     (*output*) type -> Prop :=
| ctUnit   : forall VC, 
           wf_var_context VC ->
           check_type VC Unit Unit
| ctBool   : forall VC,
           wf_var_context VC ->
           check_type VC Bool Bool
| ctNat    : forall VC,
           wf_var_context VC ->
           check_type VC Nat Nat
| ctMatrix : forall m n VC,
           wf_var_context VC ->
           check_type VC (Matrix m n) (Matrix m n)
| ctComputation : forall P x A Q P' A' Q' VC,
           wf_var_context VC ->
           check_prop VC init_mem_context P P' ->
           check_type VC A A' ->
           check_prop ((x,A')::VC) init_mem_context Q Q' ->
           check_type VC (Computation P x A Q) (Computation P' x A' Q')

with check_prop :
     (*intput*) var_context -> heap_context -> proposition ->
     (*output*) proposition -> Prop :=
| cpHId        : forall h1 h2 h1' h2' VC HC,
                 wf_var_context VC ->
                 check_heap VC HC h1 h1' ->
                 check_heap VC HC h2 h2' ->
                 check_prop VC HC (HId h1 h2) (HId h1' h2')
| cpId         : forall A M N A' M' N' VC HC,
                 wf_var_context VC ->
                 check_type VC A A' ->
                 check_intro_term VC M A' M' ->
                 check_intro_term VC N A' N' ->
                 check_prop VC HC (Id A M N) (Id A' M' N')
| cpTop        : forall VC HC,
                 wf_var_context VC ->
                 check_prop VC HC Top Top
| cpBottom     : forall VC HC,
                 wf_var_context VC ->
                 check_prop VC HC Bottom Bottom
| cpAnd        : forall P Q P' Q' VC HC,
                 wf_var_context VC ->
                 check_prop VC HC P P' ->
                 check_prop VC HC Q Q' ->
                 check_prop VC HC (And P Q) (And P' Q')
| cpOr         : forall P Q P' Q' VC HC,
                 wf_var_context VC ->
                 check_prop VC HC P P' ->
                 check_prop VC HC Q Q' ->
                 check_prop VC HC (Or P Q) (Or P' Q')
| cpImplies    : forall P Q P' Q' VC HC,
                 wf_var_context VC ->
                 check_prop VC HC P P' ->
                 check_prop VC HC Q Q' ->
                 check_prop VC HC (Implies P Q) (Implies P' Q')
| cpNot        : forall P P' VC HC,
                 wf_var_context VC ->
                 check_prop VC HC P P' ->
                 check_prop VC HC (Not P) (Not P')
| cpIndom      : forall H H' M M' VC HC,
                 wf_var_context VC ->
                 check_intro_term VC M Nat M' ->
                 check_heap VC HC H H' ->
                 check_prop VC HC (Indom H M) (Indom H' M')
| cpForAll     : forall A P A' P' x VC HC,
                 wf_var_context VC ->
                 check_type VC A A' ->
                 check_prop ((x,A')::VC) HC P P' ->
                 check_prop VC HC (ForAll x A P) (ForAll x A' P')
| cpExists     : forall A P A' P' x VC HC,
                 wf_var_context VC ->
                 check_type VC A A' ->
                 check_prop ((x,A')::VC) HC P P' ->
                 check_prop VC HC (Exists x A P) (Exists x A' P')
| cpForAllHeap : forall P P' x VC HC,
                 wf_var_context VC ->
                 check_prop VC (x::HC) P P' ->
                 check_prop VC HC (ForAllHeap x P) (ForAllHeap x P')
| cpExistsHeap : forall P P' x VC HC,
                 wf_var_context VC ->
                 check_prop VC (x::HC) P P' ->
                 check_prop VC HC (ExistsHeap x P) (ExistsHeap x P')

with check_heap :
     (*input*) var_context -> heap_context -> heap ->
     (*output*) heap -> Prop :=
| chVar     : forall x VC HC,
              wf_var_context VC ->
              In x HC -> (*x is in the heap context*)
              check_heap VC HC (HVar x) (HVar x)
| chHEmpty  : forall VC HC,
              wf_var_context VC ->
              check_heap VC HC HEmpty HEmpty
| chHUpdate : forall A A' h h' M M' N N' VC HC,
              wf_var_context VC ->
              check_type VC A A' ->
              check_heap VC HC h h' ->
              check_intro_term VC M Nat M' ->
              check_intro_term VC N A' N' ->
              check_heap VC HC (HUpdate h M N A) (HUpdate h' M' N' A')

with check_intro_term :
     (*input*) var_context -> intro_term -> (*canonical*) type ->
     (*output*) intro_term -> Prop :=
| ciUnit     : forall VC,
               wf_var_context VC ->
               check_intro_term VC TT Unit TT
| ciBoolean  : forall VC b,
               wf_var_context VC ->
               check_intro_term VC (Boolean b) Bool (Boolean b)
| ciRef      : forall VC n,
               wf_var_context VC ->
               check_intro_term VC (Ref n) Nat (Ref n)
| ciMat      : forall m n (N : numMatrix m n) VC,
               wf_var_context VC ->
               check_intro_term VC (Mat N) (Matrix m n) (Mat N)
| ciTranspose: forall m n M M' VC,
               wf_var_context VC ->
               check_intro_term VC M (Matrix m n) M' ->
               check_intro_term VC (Unop Transpose M) (Matrix n m) (Unop Transpose M')
| ciInverse  : forall n M M' VC,
               wf_var_context VC ->
               check_intro_term VC M (Matrix n n) M' ->
               check_intro_term VC (Unop Inverse M) (Matrix n n) (Unop Inverse M')
| cibNot     : forall M M' VC,
               wf_var_context VC ->
               check_intro_term VC M Bool M' ->
               check_intro_term VC (Unop BNot M) Bool (Unop BNot M')
| ciNeg      : forall m n M M' VC,
               wf_var_context VC ->
               check_intro_term VC M (Matrix m n) M' ->
               check_intro_term VC (Unop Neg M) (Matrix m n) (Unop Neg M')
| ciMultiply : forall m n p M N M' N' VC,
               wf_var_context VC ->
               check_intro_term VC M (Matrix m n) M' ->
               check_intro_term VC N (Matrix n p) N' ->
               check_intro_term VC (Binop Multiply M N) (Matrix m p) (Binop Multiply M' N')
| ciNumBinop : forall (b : num_binop) m n M N M' N' VC,
               wf_var_context VC ->
               check_intro_term VC M (Matrix m n) M' ->
               check_intro_term VC N (Matrix m n) N' ->
               check_intro_term VC (Binop b M N) (Matrix m n) (Binop b M' N')
| ciNatBinop : forall (b : num_binop) M N M' N' VC,
               b <> Divide ->
               wf_var_context VC ->
               check_intro_term VC M Nat M' ->
               check_intro_term VC N Nat N' ->
               check_intro_term VC (Binop b M N) Nat (Binop b M' N')
| ciCompBinop: forall (b : comp_binop) m n M N M' N' VC,
               wf_var_context VC ->
               check_intro_term VC M (Matrix m n) M' ->
               check_intro_term VC N (Matrix m n) N' ->
               check_intro_term VC (Binop b M N) Bool (Binop b M' N')
| ciCompBinopBool : forall (b : comp_binop) M N M' N' VC,
               wf_var_context VC ->
               check_intro_term VC M Bool M' ->
               check_intro_term VC N Bool N' ->
               check_intro_term VC (Binop b M N) Bool (Binop b M' N')
| ciElimTerm : forall K M' A B N' VC,
               wf_var_context VC -> 
               check_type VC B B (* B must be canonical *) ->
               infer_elim_term VC K A M' ->
               A = B (* A must be syntactically equal to B *) ->
               aux_expand_fun A M' = N' ->
               check_intro_term VC K B N'
| ciDia      : forall E E' P x A Q VC,
               wf_var_context VC ->
               check_postcondition VC (And (HId init mem) P) E x A Q E' ->
               check_intro_term VC (Dia E) (Computation P x A Q) (Dia E')
| ciSelectNum: forall m n M N M' N' VC,
               wf_var_context VC ->
               check_intro_term VC M (Matrix m n) M' ->
               check_intro_term VC N Nat N' ->
               check_intro_term VC (Select M N) Nat (Select M' N')

with infer_elim_term :
     (*input*) var_context -> elim_term ->
     (*output*) type -> intro_term -> Prop :=
| ieVar   : forall x A VC (pf : in_var_context x VC),
            wf_var_context VC -> 
            get x VC pf = A ->
            (*check_type VC A A -> A is canonical because A is in 
              the well-founded var_context VC*)
            infer_elim_term VC (Var x) A (Var x)
| ieCast  : forall M M' A A' VC,
            wf_var_context VC ->
            check_type VC A A' ->
            check_intro_term VC M A' M' ->
            infer_elim_term VC (Cast M A) A' M'

with infer_postcondition : 
     (*input*) var_context -> proposition -> computation -> var -> type ->
     (*output*) proposition -> computation -> Prop :=
| ipIntroTerm : forall P M M' x A Q VC,
                wf_var_context VC ->
                check_type VC A A -> (*A is canonical*)
                check_prop VC init_mem_context P P -> (*P is canonical*)
                check_intro_term VC M A M' ->
                Q = And P (Id A (aux_expand_fun A (Var x)) M') ->
                infer_postcondition VC P M x A Q M'
| ipLetDia    : forall P x K N' E E' y (z:heap_var) B A Q R1 R2 O VC,
                wf_var_context VC ->
                check_type VC A A -> (*A is canonical*)
                check_type VC B B -> (*B is canonical*)
                check_prop VC init_mem_context P P -> (*P is canonical*)
                check_prop ((x,A)::VC) init_mem_context Q Q -> (*Q x is canonical*)
                infer_elim_term VC K (Computation R1 x A R2) N' ->
                sequent VC init_mem_context P R1 -> (*P==>R1*)
                infer_postcondition ((x,A)::VC) (seq_prop P R2 z) E y B Q E' ->
                aux_reduce A N' x E' O -> 
                infer_postcondition VC P (Let dia x <- K in E) y B (Exists x A Q) O
| ipAnnotation: forall VC P (I:proposition) E y B Q I' E' z,
                wf_var_context VC ->
                check_type VC B B -> (*B is canonical*)
                check_prop VC init_mem_context P P -> (*P is canonical*)
                check_prop VC init_mem_context I I' ->
                sequent VC init_mem_context P I' ->
                infer_postcondition VC (seq_prop P I' z) E y B Q E' ->
                infer_postcondition VC P (Annotation I;; E) y B Q (Annotation I';; E')
| ipAlloc     : forall P x A A' M M' E E' y (z:heap_var) B Q sp_alloc VC,
                wf_var_context VC ->
                check_type VC B B -> (*B is canonical*)
                check_prop VC init_mem_context P P -> (*P is canonical*)
                check_type VC A A' ->
                check_intro_term VC M A' M' ->
                sp (Alloc x M' A') sp_alloc -> (*strongest postcondition for command*)
                infer_postcondition ((x,Nat)::VC) (seq_prop P sp_alloc z) E y B Q E' ->
                infer_postcondition VC P (Alloc x M A;; E) y B (Exists x Nat Q) (Alloc x M' A';; E')
| ipDealloc   : forall P x M M' A A' E E' y z B Q sp_dealloc VC,
                wf_var_context VC ->
                check_type VC B B -> (*B is canonical*)
                check_prop VC init_mem_context P P -> (*P is canonical*)
                check_type VC A A' ->
                check_intro_term VC M A' M' ->
                sequent VC init_mem_context (prop_subst "mem" init P) (seleq_ A' init M' z x) (*P==>init is defined on M'*) ->
                sp (Dealloc x M' A') sp_dealloc ->
                infer_postcondition ((x,A')::VC) (seq_prop P sp_dealloc z) E y B Q E' ->
                infer_postcondition VC P (Dealloc x M A;; E) y B (Exists z A' Q) (Dealloc x M' A';; E')
| ipLookup    : forall P x M M' A A' E E' y z B Q sp_lookup VC h,
                wf_var_context VC ->
                check_type VC B B -> (*B is canonical*)
                check_prop VC init_mem_context P P -> (*P is canonical*)
                check_type VC A A' ->
                check_intro_term VC M Nat M' ->
                sequent VC init_mem_context P (seleq_ A' mem M' h x) -> (*P==>mem is defined on M'*)
                sp (Lookup x M' A') sp_lookup -> (*strongest postcondition for command*)
                infer_postcondition ((x,A')::VC) (seq_prop P sp_lookup h) E y B Q E' ->
                infer_postcondition VC P (Lookup x M A;; E) y B (Exists z A' Q) (Lookup x M' A';; E')
| ipMutate    : forall P x M M' A A' N N' E E' y z B Q sp_mutate VC,
                wf_var_context VC ->
                check_type VC B B -> (*B is canonical*)
                check_prop VC init_mem_context P P -> (*P is canonical*)
                check_type VC A A' ->
                check_intro_term VC M Nat M' ->
                check_intro_term VC N A' N' ->
                sequent VC init_mem_context P (seleq_ A' mem M' z x) -> (*P==>mem is defined on M'*)
                sp (Mutate M' N' A') sp_mutate ->
                infer_postcondition VC (seq_prop P sp_mutate z) E y B Q E' ->
                infer_postcondition VC P (Mutate M N A;; E) y B Q (Mutate M' N' A';; E')
| ipSend      : forall VC P A M N E y B Q A' M' N' E',
                wf_var_context VC ->
                check_type VC B B -> (*B is canonical*)
                check_prop VC init_mem_context P P -> (*P is canonical*)
                check_type VC A A' ->
                check_intro_term VC M A' M'->
                check_intro_term VC N Nat N' ->
                infer_postcondition VC P E y B Q E' ->
                infer_postcondition VC P (Send A M N ;; E) y B Q (Send A' M' N' ;; E')
| ipReceive   : forall VC P x A N E y B Q A' N' E',
                wf_var_context VC ->
                check_type VC B B -> (*B is canonical*)
                check_prop VC init_mem_context P P -> (*P is canonical*)
                check_type VC A A' ->
                check_intro_term VC N Nat N' ->
                infer_postcondition ((x,A')::VC) P E y B Q E' ->
                infer_postcondition VC P (Receive x A N ;; E) y B (Exists x A' Q) (Receive x A' N' ;; E')


| ipIf        : forall P x A A' M M' E1 E1' E2 E2' E E' y B Q P1 P2 VC,
                wf_var_context VC ->
                check_type VC B B -> (*B is canonical*)
                check_prop VC init_mem_context P P -> (*P is canonical*)
                check_type VC A A' ->
                check_intro_term VC M Bool M' ->
                (*if M'==true then E1=>E1'*)
                infer_postcondition VC (And P (Id Bool M' (Boolean true))) E1 x A' P1 E1' ->
                (*if M'==false then E2=>E2'*)
                infer_postcondition VC (And P (Id Bool M' (Boolean false))) E2 x A' P2 E2' ->
                infer_postcondition ((x,A')::VC) (Or P1 P2) E y B Q E' ->
                infer_postcondition VC P (If x M A E1 E2;; E) y B (Exists x A' Q) (If x M' A' E1' E2';; E')
| ipLoop      : forall P y I I' I''' I'''' J J1 J2 J3 J4 M M' A A' x N N' N'' F F' E E' z C Q VC,
                wf_var_context VC ->
                wf_var_context ((x,A')::(y,A')::VC) ->
                wf_var_context ((x,A')::(y,A')::(z,A')::VC) ->
(*                ~ in_var_context x VC ->
                ~ in_var_context y VC ->
                ~ in_var_context z VC ->*)
                check_type VC C C -> (*C is canonical*)
                check_prop VC init_mem_context P P -> (*P is canonical*)
                check_type VC A A' ->
                check_intro_term VC M A' M' ->
                check_intro_term ((x,A')::VC) N Bool N' ->
                check_prop ((x,A')::(y,A')::VC) init_mem_context I I' -> (*get canonical loop invariant*)
                (**)
                let I'' := prop_subst "init" mem I' in
                    proposition_hereditary_subst M' y (getShape A') I'' I''' ->
                    proposition_hereditary_subst M' x (getShape A') I''' I'''' ->
                (*I holds before and after every iteration*)
                sequent VC init_mem_context P I'''' ->
                (**)
                  proposition_hereditary_subst (Var z) x (getShape A') I' J1 ->
                  proposition_hereditary_subst (Var z) y (getShape A') I' J2 ->
                (*If I holds before iteration i and between iterations i & i+1 then it holds after iteration i+1*)
                sequent ((x,A')::(y,A')::(z,A')::VC) init_mem_context (seq_prop J1 J2 z) I' ->
                (**)
                  proposition_hereditary_subst (Var y) x (getShape A') (prop_subst "init" mem I') J ->
                (*I' holds if the loop is not taken*)
                sequent ((x,A')::(y,A')::VC) init_mem_context I' J ->
                (**)
                  proposition_hereditary_subst (Var x) y (getShape A') I' J3 ->
                (*Execute the body of the loop if the loop guard is satisfied*)
                check_postcondition ((x,A')::VC) 
                  (And (And (HId init mem) J3) (Id Bool N' (Boolean true)))
                  F y A' I' F' -> 
                (**)
                  proposition_hereditary_subst M' x (getShape A') I' J4 ->
                  intro_term_hereditary_subst (Var y) x (getShape Bool) N' N'' ->
                (*Execute the continuation of the loop is the loop guard is not satisfied*)
                infer_postcondition ((y,A')::VC) (seq_prop P (And J4 (Id Bool N'' (Boolean false))) z)
                  E z C Q E' ->
                infer_postcondition VC P (Loop y I M A x N x F;; E) z C (Exists y A' Q)
                                         (Loop y I' M' A' x N' x F';; E')
| ipStrengthenPre : forall VC (P P':proposition) E x A Q E',
                    infer_postcondition VC P E x A Q E' ->
                    sequent VC init_mem_context P' P ->
                    infer_postcondition VC P' E x A Q E'  


with check_postcondition : 
     (*input*) var_context -> proposition -> computation -> var -> type -> proposition ->
     (*output*) computation -> Prop :=
| cpConsequent : forall P Q R E E' x A VC,
                 wf_var_context VC -> 
                 check_type VC A A -> (* A is canonical *)
                 check_prop VC init_mem_context P P -> (*P is canonical*)
                 check_prop ((x,A)::VC) init_mem_context Q Q -> (*Q is canonical*)
                 infer_postcondition VC P E x A R E' -> (*R is the strongest postcondition*)
                 sequent ((x,A)::VC) init_mem_context R Q -> (*R ==> Q*)
                 check_postcondition VC P E x A Q E'

with sequent : 
     (*input*) var_context -> heap_context -> prop_context ->
     (*output*) prop_context -> Prop :=
| sEq           : forall P PC1 PC2 VC HC, 
                  wf_var_context VC ->
                  wf_prop_context VC HC PC1 ->
                  wf_prop_context VC HC PC2 ->
                  sequent VC HC (P::PC1) (P::PC2)
| sCut          : forall P PC1 PC2 VC HC,
                  wf_var_context VC ->
                  wf_prop_context VC HC PC1 ->
                  wf_prop_context VC HC PC2 ->
                  sequent VC HC PC1 (P::PC2) ->
                  sequent VC HC (P::PC1) PC2 ->
                  sequent VC HC PC1 PC2
| sSwap1        : forall VC HC P1 P2 PC1 PC2,
                  sequent VC HC (P1::P2::PC1) PC2 ->
                  sequent VC HC (P2::P1::PC1) PC2
| sSwap2        : forall VC HC P1 P2 PC1 PC2,
                  sequent VC HC PC1 (P1::P2::PC2) ->
                  sequent VC HC PC1 (P2::P1::PC2)
| sWeak1        : forall P PC1 PC2 VC HC,
                  wf_var_context VC ->
                  wf_prop_context VC HC PC1 ->
                  wf_prop_context VC HC PC2 ->
                  sequent VC HC PC1 PC2 ->
                  sequent VC HC (P::PC1) PC2
| sWeak2        : forall P PC1 PC2 VC HC,
                  wf_var_context VC ->
                  wf_prop_context VC HC PC1 ->
                  wf_prop_context VC HC PC2 ->
                  sequent VC HC PC1 PC2 ->
                  sequent VC HC PC1 (P::PC2) 
| sContraction1 : forall P PC1 PC2 VC HC,  wf_var_context VC ->
                  wf_prop_context VC HC PC1 ->
                  wf_prop_context VC HC PC2 ->
                  sequent VC HC (P::P::PC1) PC2 ->
                  sequent VC HC (P::PC1) PC2 
| sContraction2 : forall P PC1 PC2 VC HC,
                  wf_var_context VC ->
                  wf_prop_context VC HC PC1 ->
                  wf_prop_context VC HC PC2 ->
                  sequent VC HC PC1 (P::P::PC2) ->
                  sequent VC HC PC1 (P::PC2)

| sBottom   : forall PC1 PC2 VC HC,
              wf_var_context VC ->
              wf_prop_context VC HC PC1 ->
              wf_prop_context VC HC PC2 ->
              sequent VC HC (Bottom::PC1) PC2 
| sTop      : forall PC1 PC2 VC HC,
              wf_var_context VC ->
              wf_prop_context VC HC PC1 ->
              wf_prop_context VC HC PC2 ->
              sequent VC HC PC1 (Top::PC2)
| sAnd1     : forall P Q PC1 PC2 VC HC,
              wf_var_context VC ->
              wf_prop_context VC HC PC1 ->
              wf_prop_context VC HC PC2 ->
              sequent VC HC (P::Q::PC1) PC2 ->
              sequent VC HC (And P Q::PC1) PC2 
| sAnd2     : forall P Q PC1 PC2 VC HC,
              wf_var_context VC ->
              wf_prop_context VC HC PC1 ->
              wf_prop_context VC HC PC2 ->
              sequent VC HC PC1 (P::PC2) ->
              sequent VC HC PC1 (Q::PC2) ->
              sequent VC HC PC1 (And P Q::PC2)
| sOr1      : forall P Q PC1 PC2 VC HC,
              wf_var_context VC ->
              wf_prop_context VC HC PC1 ->
              wf_prop_context VC HC PC2 ->
              sequent VC HC (P::PC1) PC2 ->
              sequent VC HC (Q::PC1) PC2 ->
              sequent VC HC (Or P Q::PC1) PC2
| sOr2      : forall P Q PC1 PC2 VC HC,
              wf_var_context VC ->
              wf_prop_context VC HC PC1 ->
              wf_prop_context VC HC PC2 ->
              sequent VC HC PC1 (P::Q::PC2) ->
              sequent VC HC PC1 (Or P Q::PC2)
| sImplies1 : forall P Q PC1 PC2 VC HC,
              wf_var_context VC ->
              wf_prop_context VC HC PC1 ->
              wf_prop_context VC HC PC2 ->
              sequent VC HC PC1 (P::PC2) ->
              sequent VC HC (Q::PC1) PC2 ->
              sequent VC HC (Implies P Q::PC1) PC2 
| sImplies2 : forall P Q PC1 PC2 VC HC,
              wf_var_context VC ->
              wf_prop_context VC HC PC1 ->
              wf_prop_context VC HC PC2 ->
              sequent VC HC (P::PC1) (Q::PC2) ->
              sequent VC HC PC1 (Implies P Q::PC2)
| sNot1     : forall P PC1 PC2 VC HC,
              wf_var_context VC ->
              wf_prop_context VC HC PC1 ->
              wf_prop_context VC HC PC2 ->
              sequent VC HC PC1 (P::PC2) ->
              sequent VC HC (Not P::PC1) PC2
| sNot2     : forall P PC1 PC2 VC HC,
              wf_var_context VC ->
              wf_prop_context VC HC PC1 ->
              wf_prop_context VC HC PC2 ->
              sequent VC HC (P::PC1) PC2 ->
              sequent VC HC PC1 (Not P::PC2)

| sForAllElim      : forall x A P P' M PC1 PC2 VC HC,
                     wf_var_context VC ->
                     wf_prop_context VC HC PC1 ->
                     wf_prop_context VC HC PC2 ->
                     check_intro_term VC M A M (* M is any canonical intro term *) ->
                     proposition_hereditary_subst M x (getShape A) P P' ->
                     sequent VC HC (P'::ForAll x A P::PC1) PC2 ->
                     sequent VC HC (ForAll x A P::PC1) PC2
| sForAllIntro     : forall x A P PC1 PC2 VC HC,
                     wf_var_context VC ->
                     wf_prop_context VC HC PC1 ->
                     wf_prop_context VC HC PC2 ->
                     check_type VC A A ->
                     sequent ((x,A)::VC) HC PC1 (P::PC2) ->
                     sequent VC HC PC1 (ForAll x A P::PC2)
| sExistsElim      : forall x A P PC1 PC2 VC HC,
                     wf_var_context VC ->
                     wf_prop_context VC HC PC1 ->
                     wf_prop_context VC HC PC2 ->
                     check_type VC A A ->
                     sequent ((x,A)::VC) HC (P::PC1) PC2 ->
                     sequent VC HC (Exists x A P::PC1) PC2
| sExistsIntro     : forall x A P P' M PC1 PC2 VC HC,
                     wf_var_context VC ->
                     wf_prop_context VC HC PC1 ->
                     wf_prop_context VC HC PC2 ->
                     check_intro_term VC M A M (* M is any canonical intro term *) ->
                     proposition_hereditary_subst M x (getShape A) P P' ->
                     sequent VC HC PC1 (P'::Exists x A P::PC2) ->
                     sequent VC HC PC1 (Exists x A P::PC2)
| sForAllHeapElim  : forall x h P PC1 PC2 VC HC,
                     wf_var_context VC ->
                     wf_prop_context VC HC PC1 ->
                     wf_prop_context VC HC PC2 ->
                     check_heap VC HC h h (* h is any canonical heap *) ->
                     sequent VC HC (prop_subst x h P::ForAllHeap x P::PC1) PC2 ->
                     sequent VC HC (ForAllHeap x P::PC1) PC2
| sForAllHeapIntro : forall x P PC1 PC2 VC HC,
                     wf_var_context VC ->
                     wf_prop_context VC HC PC1 ->
                     wf_prop_context VC HC PC2 ->
                     sequent VC (x::HC) PC1 (P::PC2) ->
                     sequent VC HC PC1 (ForAllHeap x P::PC2)
| sExistsHeapElim : forall x P PC1 PC2 VC HC,
                     wf_var_context VC ->
                     wf_prop_context VC HC PC1 ->
                     wf_prop_context VC HC PC2 ->
                     sequent VC (x::HC) (P::PC1) PC2 ->
                     sequent VC HC (ExistsHeap x P::PC1) PC2 
| sExistsHeapIntro : forall h x P PC1 PC2 VC HC,
                     wf_var_context VC ->
                     wf_prop_context VC HC PC1 ->
                     wf_prop_context VC HC PC2 ->
                     check_heap VC HC h h (* h is any canonical heap *) ->
                     sequent VC HC PC1 (prop_subst x h P::ExistsHeap x P::PC2) ->
                     sequent VC HC PC1 (ExistsHeap x P::PC2)
  
(* type equality *)
| sIdEq     : forall A M PC1 PC2 VC HC,
              wf_var_context VC ->
              wf_prop_context VC HC PC1 ->
              wf_prop_context VC HC PC2 ->
              sequent VC HC PC1 (Id A M M::PC2)
| sIdSubst1 : forall A M N x Q Q1 Q2 PC1 PC2 VC HC,
              wf_var_context VC ->
              wf_prop_context VC HC PC1 ->
              wf_prop_context VC HC PC2 ->
              proposition_hereditary_subst N x (getShape A) Q Q1 ->
              proposition_hereditary_subst M x (getShape A) Q Q2 ->
              sequent VC HC (Id A M N::PC1) (Q1::PC2) ->
              sequent VC HC (Id A M N::PC1) (Q2::PC2)
| sIdSubst2 : forall A M N x Q Q1 Q2 PC1 PC2 VC HC, 
              wf_var_context VC ->
              wf_prop_context VC HC PC1 ->
              wf_prop_context VC HC PC2 ->
              proposition_hereditary_subst N x (getShape A) Q Q1 ->
              proposition_hereditary_subst M x (getShape A) Q Q2 ->
              sequent VC HC (Id A M N::PC1) (Q2::PC2) ->
              sequent VC HC (Id A M N::PC1) (Q1::PC2)

(* heaps *)
| sHIdEq           : forall H PC1 PC2 VC HC,
                     wf_var_context VC ->
                     wf_prop_context VC HC PC1 ->
                     wf_prop_context VC HC PC2 ->
                     sequent VC HC PC1 (HId H H::PC2)
| sHIdSubst1       : forall H1 H2 h q q1' q2' PC1 PC2 VC HC,
                     wf_var_context VC ->
                     wf_prop_context VC HC PC1 ->
                     wf_prop_context VC HC PC2 ->
                     prop_subst h H1 q = q1' ->
                     prop_subst h H2 q = q2' ->
                     sequent VC HC (HId H1 H2::PC1) (q1'::PC2) ->
                     sequent VC HC (HId H1 H2::PC1) (q2'::PC2)
| sHIdSubst2       : forall H1 H2 h q q1' q2' PC1 PC2 VC HC,
                     wf_var_context VC ->
                     wf_prop_context VC HC PC1 ->
                     wf_prop_context VC HC PC2 ->
                     prop_subst h H1 q = q1' ->
                     prop_subst h H2 q = q2' ->
                     sequent VC HC (HId H1 H2::PC1) (q2'::PC2) ->
                     sequent VC HC (HId H1 H2::PC1) (q1'::PC2)
| sHIdSubstIntro1  : forall H1 H2 h q q1' q2' PC1 PC2 VC HC,
                     wf_var_context VC ->
                     wf_prop_context VC HC PC1 ->
                     wf_prop_context VC HC PC2 ->
                     prop_subst h H1 q = q1' ->
                     prop_subst h H2 q = q2' ->
                     sequent VC HC (HId H1 H2::q1'::PC1) PC2 ->
                     sequent VC HC (HId H1 H2::q2'::PC1) PC2
| sHIdPermutation  : forall M1 N1 M2 N2 A B H PC1 PC2 VC HC,
                     wf_var_context VC ->
                     wf_prop_context VC HC PC1 ->
                     wf_prop_context VC HC PC2 ->
                     sequent VC HC PC1 (Id Nat M1 M2::HId (HUpdate (HUpdate H M1 N1 B) M2 N2 A)
                                                          (HUpdate (HUpdate H M2 N2 A) M1 N1 B)::PC2)
| sHIdUpdateCancel : forall H M N1 N2 A B PC1 PC2 VC HC,
                     wf_var_context VC ->
                     wf_prop_context VC HC PC1 ->
                     wf_prop_context VC HC PC2 ->
                     sequent VC HC PC1 (HId (HUpdate (HUpdate H M N1 B) M N2 A)
                                            (HUpdate H M N2 A)::PC2)
| sFunctionalHeap  : forall H1 H2 M N1 N2 A PC1 PC2 VC HC,
                     wf_var_context VC ->
                     wf_prop_context VC HC PC1 ->
                     wf_prop_context VC HC PC2 ->
                     sequent VC HC (HId (HUpdate H1 M N1 A) (HUpdate H2 M N2 A)::PC1)
                                   (Id A N1 N2::PC2)
| sEmptyHeap       : forall H M N A PC1 PC2 VC HC,
                     wf_var_context VC ->
                     wf_prop_context VC HC PC1 ->
                     wf_prop_context VC HC PC2 ->
                     sequent VC HC (HId HEmpty (HUpdate H M N A)::PC1) PC2
| sInDom           : forall H1 H2 M N A PC1 PC2 VC HC,
                     wf_var_context VC ->
                     wf_prop_context VC HC PC1 ->
                     wf_prop_context VC HC PC2 ->
                     sequent VC HC (HId H1 (HUpdate H2 M N A)::PC1) (Indom H1 M::PC2)

(*other*) 
| sId            : forall A M N PC1 PC2 VC HC,
                   wf_var_context VC ->
                   wf_prop_context VC HC PC1 ->
                   wf_prop_context VC HC PC2 ->
                   normalize M = normalize N ->
                   sequent VC HC PC1 (Id A M N::PC2)
.

Scheme mut_wf_var_context := Induction for wf_var_context Sort Prop
with mut_wf_prop_contrext := Induction for wf_prop_context Sort Prop
with mut_check_type := Induction for check_type Sort Prop
with mut_check_prop := Induction for check_prop Sort Prop
with mut_check_heap := Induction for check_heap Sort Prop
with mut_check_intro_term := Induction for check_intro_term Sort Prop 
with mut_infer_elim_term := Induction for infer_elim_term Sort Prop
with mut_infer_postcondition := Induction for infer_postcondition Sort Prop
with mut_check_postcondition := Induction for check_postcondition Sort Prop
with mut_sequent := Induction for sequent Sort Prop.

End typing.
Hint Constructors check_type check_prop check_heap check_intro_term infer_elim_term wf_var_context wf_prop_context.





            

        
