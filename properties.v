Require Import List String Arith Reals Program.Equality.
Require Import mymatrices syntax context substitution typing.
Set Implicit Arguments.

Hint Constructors sequent.

Definition By m n := Matrix m n.

(* General Tactics for variables and contexts *)
Ltac step := constructor; auto.
Ltac ciVar x A pf :=
  apply ciElimTerm with (Var x) A; auto;
  apply ieVar with pf; auto. 

Ltac rewrite_free :=
  repeat match goal with
  | [ H : context[free_in_proposition _ ?P = _] |- context[free_in_proposition _ ?P] ] =>
    rewrite H; auto
  | [ H : context[free_in_type _ ?A = _] |- context[free_in_type _ ?A] ] =>
    rewrite H; auto
  | [ H : context[free_in_heap _ ?h = _] |- context[free_in_heap _ ?h] ] =>
    rewrite H; auto
  | [ H : context[free_in_elim_term _ ?K = _] |- context[free_in_elim_term _ ?K] ] =>
    rewrite H; auto
  | [ H : context[free_in_intro_term _ ?M = _] |- context[free_in_intro_term _ ?M] ] =>
    rewrite H; auto
  | [ H : context[free_in_computation _ ?E = _] |- context[free_in_computation _ ?E] ] =>
    rewrite H; auto
  end.

Ltac destruct_var_dec :=
  match goal with
  | [ |- context[var_dec ?x ?x] ] => destruct (var_dec x x); [ idtac | absurd (x <> x); auto ]
  | [ H : ?x <> ?y |- context[var_dec ?x ?y] ] => 
    destruct (var_dec x y); [ absurd (x = y); auto | idtac ]
  | [ H : ?x <> ?y |- context[var_dec ?y ?x] ] =>
    destruct (var_dec y x); [ absurd (x = y); auto | idtac ]
  | [ H : ?x <> ?y, H' : context[var_dec ?x ?y] |- _ ] =>
    destruct (var_dec x y); [ absurd (x=y); auto | idtac ]
  | [ H : ?x <> ?y, H' : context[var_dec ?y ?x] |- _ ] =>
    destruct (var_dec y x); [ absurd (x=y); auto | idtac ]
  | [ H : ?x = ?y |- context[var_dec ?x ?y] ] =>
    destruct (var_dec x y); [ idtac | absurd (x <> y); auto ]
  | [ H : ?x = ?y |- context[var_dec ?y ?x] ] =>
    destruct (var_dec y x); [ idtac | absurd (x <> y); auto ]
  | [ H : ?x = ?y, H' : context[var_dec ?x ?y] |- _ ] =>
    destruct (var_dec x y); [ idtac | absurd (x <> y); auto ]
  | [ H : ?x = ?y, H' : context[var_dec ?y ?x] |- _ ] =>
    destruct (var_dec y x); [ idtac | absurd (x <> y); auto ]
  end.

Ltac destruct_var_dec_all :=
  match goal with
  | [ |- context[var_dec ?x ?y] ] => destruct (var_dec x y); simpl in *; auto
  | [ H : context[var_dec ?x ?y] |- _ ] => destruct (var_dec x y); simpl in *; auto
 end.

(* Reasoning about booleans *)

Ltac andb_false :=
  match goal with
  | [ |- context[(?P && false)%bool] ] => destruct P; simpl; auto
  end.
Ltac destruct_andb :=
  match goal with
  | [ |- context[(?P && _)%bool] ] => destruct P; simpl; auto
  end.
Ltac destruct_orb :=
  match goal with
  | [ |- (?P || _)%bool = _] => destruct P; auto; simpl in *; auto
  end.

Open Scope bool.
Lemma andb_false : forall b, b && false = false.
Proof. destruct b; auto. Qed.
Lemma orb_false : forall b, b || false = b.
Proof. destruct b; auto. Qed.
Lemma andb_true : forall b, b && true = b.
Proof. destruct b; auto. Qed.
Lemma orb_true : forall b, b || true = true.
Proof. destruct b; auto. Qed.

Ltac remove_bconst :=
  simpl; repeat match goal with 
  | [ |- context[_ && false] ] => rewrite andb_false; simpl; auto
  | [ |- context[_ && true ] ] => rewrite andb_true; simpl; auto
  | [ |- context[_ || false] ] => rewrite orb_false; simpl; auto
  | [ |- context[_ || true ] ] => rewrite orb_true; simpl; auto
  end; auto.

Lemma orb_assoc : forall b1 b2 b3,
      b1 || (b2 || b3) = (b1 || b2) || b3.
Proof. destruct b1; destruct b2; destruct b3; auto. Qed.

Lemma andb_distr : forall b1 b2 b3,
      b1 && (b2 || b3) = (b1 && b2) || (b1 && b3).
Proof. destruct b1; destruct b2; destruct b3; auto. Qed.

Lemma orb_comm : forall b1 b2, b1 || b2 = b2 || b1.
Proof. destruct b1; destruct b2; auto. Qed.

Definition var_eq x y := if var_dec x y then true else false.
Definition var_neq x y := if var_dec x y then false else true.
Hint Unfold var_eq.

Ltac split_orb :=
  repeat match goal with
  | [ H : ?P || _ = false |- _ ] => assert (P = false);
    match goal with
    | [ |- P = false ] => destruct P; simpl in *; auto
    | [ H' : P = false |- _ ] => rewrite H' in *; simpl in *
    end
  end.

(* Free variables in terms of the form (Var y) *)
Lemma not_free_in_var : forall A x y, x <> y -> free_in_intro_term x (aux_expand_fun A (Var y)) = false.
Proof.
  induction A; simpl; intros; auto;
    try (destruct (var_dec x y); auto; absurd (x=y); auto; fail).
  destruct (var_dec x y); auto. absurd (x=y); auto.
  destruct (var_dec x v); simpl; auto. 
Qed.

Lemma aux_free_in_subst : forall F x S E E',
      monadic_subst F x S E E' -> forall y,
      free_in_computation y F = false ->
      (if var_dec y x then false else free_in_computation y E) = false ->
      free_in_computation y E' = false.
Proof.
  apply (monadic_mut
    (fun M x S A A' (pf : type_hereditary_subst M x S A A') => forall y, 
     free_in_intro_term y M = false ->
     (if var_dec y x then false else free_in_type y A) = false ->
     free_in_type y A' = false)
    (fun M x S P P' (pf : proposition_hereditary_subst M x S P P') => forall y, 
     free_in_intro_term y M = false ->
     (if var_dec y x then false else free_in_proposition y P) = false ->
     free_in_proposition y P' = false)
    (fun M x S h h' (pf : heap_hereditary_subst M x S h h') => forall y, 
     free_in_intro_term y M = false ->
     (if var_dec y x then false else free_in_heap y h) = false ->
     free_in_heap y h' = false)
    (fun M x S K N  (pf : elim_term_hereditary_subst M x S K N) => forall y,
     free_in_intro_term y M = false ->
     (if var_dec y x then false else free_in_elim_term y K) = false ->
     match N with
     | inl K' => free_in_elim_term y K' = false
     | inr (N',_) => free_in_intro_term y N' = false
     end)
    (fun M x S N N' (pf : intro_term_hereditary_subst M x S N N') => forall y,
     free_in_intro_term y M = false ->
     (if var_dec y x then false else free_in_intro_term y N) = false ->
     free_in_intro_term y N' = false)
    (fun M x S E E' (pf : computation_hereditary_subst M x S E E') => forall y,
     free_in_intro_term y M = false ->
     (if var_dec y x then false else free_in_computation y E) = false ->
     free_in_computation y E' = false)
    (fun F x S E E' (pf : monadic_subst F x S E E') => forall y,
     free_in_computation y F = false ->
     (if var_dec y x then false else free_in_computation y E) = false ->
     free_in_computation y E' = false)); intros; auto;
    try (simpl in *; repeat destruct_var_dec_all; split_orb; rewrite_free; try destruct_var_dec; auto; fail).
  (*Var*) simpl in *. destruct (var_dec y0 y); auto.
    (*y0=y*) rewrite_vars. destruct_var_dec; auto.
  (*Hereditary LetDia Neq*) apply H1. 
    (*F*) dependent destruction e. simpl in *. auto.
    (*E*) simpl in *. destruct (var_dec y0 y); auto.
      (*y0<>y*) apply H0; auto. destruct (var_dec y0 x); auto. split_orb; auto.
  (*Seq*) destruct c; simpl in *; 
     split_orb; destruct_var_dec_all; rewrite_free; destruct_var_dec; auto.
Qed.

Lemma aux_free_in_subst_neq : forall F x S E E' y, x <> y ->
      monadic_subst F x S E E' -> 
      free_in_computation y F = false ->
      free_in_computation y E = false ->
      free_in_computation y E' = false.
Proof.
  intros. apply aux_free_in_subst with F x S E ; auto. destruct_var_dec; auto.
Qed.
    
Lemma aux_free_in_subst_eq : forall F x S E E',
      monadic_subst F x S E E' ->
      free_in_computation x F = false ->
      free_in_computation x E' = false.
Proof.
  intros. apply aux_free_in_subst with F x S E; auto. destruct_var_dec; auto.
Qed.

Lemma check_not_free : forall VC A A',
      check_type VC A A' ->
      forall y, ~ in_var_context y VC ->
      free_in_type y A' = false. 
  apply (mut_check_type
    (fun VC (pf : wf_var_context VC) => True)
    (fun VC HC PC (pf : wf_prop_context VC HC PC) => True)
    (fun VC A A' (pf : check_type VC A A') => 
     forall y, ~ in_var_context y VC -> free_in_type y A' = false)
    (fun VC HC P P' (pf : check_prop VC HC P P') =>
     forall y, ~ in_var_context y VC -> free_in_proposition y P' = false)
    (fun VC HC h h' (pf : check_heap VC HC h h') =>
     forall y, ~ in_var_context y VC -> free_in_heap y h' = false)
    (fun VC M A M' (pf : check_intro_term VC M A M') => 
     forall y, ~ in_var_context y VC -> free_in_intro_term y M' = false)
    (fun VC K A M (pf : infer_elim_term VC K A M) => 
     forall y, ~ in_var_context y VC -> free_in_intro_term y M = false)
    (fun VC P E y B Q E' (pf : infer_postcondition VC P E y B Q E') =>
     forall y, ~ in_var_context y VC -> free_in_computation y E' = false)
    (fun VC P E y B Q E' (pf : check_postcondition VC P E y B Q E') => 
     forall y, ~ in_var_context y VC -> free_in_computation y E' = false)
    (fun VC HC P Q (pf : sequent VC HC P Q) => True)); simpl; intros; auto;
    try (rewrite_free; fail).
  (*Computation*) destruct (var_dec y x); rewrite_free. inversion 1; auto.
  (*ForAll*) destruct (var_dec y x); auto; rewrite_free. inversion 1; auto.
  (*Exists*) destruct (var_dec y x); auto; rewrite_free. inversion 1; auto.
  (*ElimTerm*) rewrite <- e0; clear N' e0. rewrite <- e in *; clear B e.
    destruct A; destruct M'; auto; simpl; auto. simpl in *.
    destruct (var_dec y v); auto; simpl in *. 
    (*y=v*) rewrite_free.
    (*y<>v*) rewrite not_free_in_var; auto. rewrite_free.
  (*Var*) destruct (var_dec y x); auto. rewrite e0 in *; clear y e0.
    absurd (in_var_context x VC); auto.
  (*Conseq*) dependent destruction a; simpl in *.
    (*LetDia*) simpl. destruct (var_dec y0 x); rewrite_free. inversion 1; auto.
    (*MonadicSubst*) destruct (var_dec x y0); auto.
      (*x=y0*) rewrite <- e in *; clear y0 e.
        apply aux_free_in_subst_eq with F (getShape A) E0; auto.
      (*x<>y0*) apply aux_free_in_subst_neq with F x (getShape A) E0; auto.
        rewrite_free. inversion 1; auto.
  (*Alloc*) destruct (var_dec y0 x); auto; rewrite_free. inversion 1; auto.
  (*Dealloc*) destruct (var_dec y0 x); auto; rewrite_free. inversion 1; auto.
  (*Lookup*) destruct (var_dec y0 x); auto; rewrite_free. inversion 1; auto.
  (*Receive*) destruct (var_dec y0 x); auto; rewrite_free. inversion 1; auto.
  (*If*) destruct (var_dec y0 x); auto; rewrite_free. inversion 1; auto.
  (*Loop*) destruct (var_dec y0 x); auto.
    (*y0=x*) remove_bconst. rewrite e in *; clear y0 e.
      rewrite H4, H5; auto. remove_bconst.
      destruct (var_dec x y); auto.
      (*x<>y*) rewrite H12; auto. inversion 1; auto.
    (*y0<>x*) destruct (var_dec y0 y); auto.
      (*y0=y*) rewrite e in *; clear y0 e.
        rewrite_free; inversion 1; auto.
      (*y0<>y*) rewrite_free; inversion 1; auto. inversion H17; auto.
Qed.


Lemma aux_expand_double : forall A M,
      aux_expand_fun A (aux_expand_fun A M) = aux_expand_fun A M.
Proof.
  destruct A; destruct M; simpl in *; auto.
Qed.

Axiom check_intro_term_canon : forall VC M A M',
      check_intro_term VC M A M' ->
      check_intro_term VC M' A M'.

Axiom infer_postcondition_canon : forall VC P E y B Q E',
  infer_postcondition VC P E y B Q E' ->
  check_prop VC init_mem_context Q Q.

Axiom check_type_canon : forall VC A A',
      check_type VC A A' ->
      check_type VC A' A'.

Hint Extern 3 (check_type _ ?A ?A) => eapply check_type_canon; auto.


Lemma check_intro_term_wf : forall VC M A M',
      check_intro_term VC M A M' ->
      wf_var_context VC.
Proof.
  apply (mut_check_intro_term
    (fun VC (pf : wf_var_context VC) => True)
    (fun VC HC PC (pf : wf_prop_context VC HC PC) =>
     wf_var_context VC)
    (fun VC A A' (pf : check_type VC A A') =>
     wf_var_context VC)      
    (fun VC HC P P' (pf : check_prop VC HC P P') =>
     wf_var_context VC)
    (fun VC HC h h' (pf : check_heap VC HC h h') =>
     wf_var_context VC)
    (fun VC M A M' (pf : check_intro_term VC M A M') =>
     wf_var_context VC)
    (fun VC K A M (pf : infer_elim_term VC K A M) =>
     wf_var_context VC)
    (fun VC P E x A Q E' (pf : infer_postcondition VC P E x A Q E') =>
     wf_var_context VC)
    (fun VC P E x A Q E' (pf : check_postcondition VC P E x A Q E') =>
     wf_var_context VC)
    (fun VC HC P Q (pf : sequent VC HC P Q) =>
     wf_var_context VC)); intros; auto. 
Qed.

Lemma check_prop_wf : forall VC HC P P',
      check_prop VC HC P P' ->
      wf_var_context VC.
Proof.
  apply (mut_check_prop
    (fun VC (pf : wf_var_context VC) => True)
    (fun VC HC PC (pf : wf_prop_context VC HC PC) =>
     wf_var_context VC)
    (fun VC A A' (pf : check_type VC A A') =>
     wf_var_context VC)      
    (fun VC HC P P' (pf : check_prop VC HC P P') =>
     wf_var_context VC)
    (fun VC HC h h' (pf : check_heap VC HC h h') =>
     wf_var_context VC)
    (fun VC M A M' (pf : check_intro_term VC M A M') =>
     wf_var_context VC)
    (fun VC K A M (pf : infer_elim_term VC K A M) =>
     wf_var_context VC)
    (fun VC P E x A Q E' (pf : infer_postcondition VC P E x A Q E') =>
     wf_var_context VC)
    (fun VC P E x A Q E' (pf : check_postcondition VC P E x A Q E') =>
     wf_var_context VC)
    (fun VC HC P Q (pf : sequent VC HC P Q) =>
     wf_var_context VC)); intros; auto.
Qed.

Lemma infer_postcondition_wf : forall VC P E x A Q E',
      infer_postcondition VC P E x A Q E' ->
      wf_var_context VC.
Proof.
  apply (mut_infer_postcondition
    (fun VC (pf : wf_var_context VC) => True)
    (fun VC HC PC (pf : wf_prop_context VC HC PC) =>
     wf_var_context VC)
    (fun VC A A' (pf : check_type VC A A') =>
     wf_var_context VC)      
    (fun VC HC P P' (pf : check_prop VC HC P P') =>
     wf_var_context VC)
    (fun VC HC h h' (pf : check_heap VC HC h h') =>
     wf_var_context VC)
    (fun VC M A M' (pf : check_intro_term VC M A M') =>
     wf_var_context VC)
    (fun VC K A M (pf : infer_elim_term VC K A M) =>
     wf_var_context VC)
    (fun VC P E x A Q E' (pf : infer_postcondition VC P E x A Q E') =>
     wf_var_context VC)
    (fun VC P E x A Q E' (pf : check_postcondition VC P E x A Q E') =>
     wf_var_context VC)
    (fun VC HC P Q (pf : sequent VC HC P Q) =>
     wf_var_context VC)); intros; auto.
Qed.  

Lemma check_postcondition_wf : forall VC P E x A Q E',
      check_postcondition VC P E x A Q E' ->
      wf_var_context VC.
Proof.
  apply (mut_check_postcondition
    (fun VC (pf : wf_var_context VC) => True)
    (fun VC HC PC (pf : wf_prop_context VC HC PC) =>
     wf_var_context VC)
    (fun VC A A' (pf : check_type VC A A') =>
     wf_var_context VC)      
    (fun VC HC P P' (pf : check_prop VC HC P P') =>
     wf_var_context VC)
    (fun VC HC h h' (pf : check_heap VC HC h h') =>
     wf_var_context VC)
    (fun VC M A M' (pf : check_intro_term VC M A M') =>
     wf_var_context VC)
    (fun VC K A M (pf : infer_elim_term VC K A M) =>
     wf_var_context VC)
    (fun VC P E x A Q E' (pf : infer_postcondition VC P E x A Q E') =>
     wf_var_context VC)
    (fun VC P E x A Q E' (pf : check_postcondition VC P E x A Q E') =>
     wf_var_context VC)
    (fun VC HC P Q (pf : sequent VC HC P Q) =>
     wf_var_context VC)); intros; auto.
Qed.  


Lemma sequent_wf : forall VC HC PC1 PC2,
      sequent VC HC PC1 PC2 ->
      wf_var_context VC.
Proof.
  apply (mut_sequent
    (fun VC (pf : wf_var_context VC) => True)
    (fun VC HC PC (pf : wf_prop_context VC HC PC) =>
     wf_var_context VC)
    (fun VC A A' (pf : check_type VC A A') =>
     wf_var_context VC)      
    (fun VC HC P P' (pf : check_prop VC HC P P') =>
     wf_var_context VC)
    (fun VC HC h h' (pf : check_heap VC HC h h') =>
     wf_var_context VC)
    (fun VC M A M' (pf : check_intro_term VC M A M') =>
     wf_var_context VC)
    (fun VC K A M (pf : infer_elim_term VC K A M) =>
     wf_var_context VC)
    (fun VC P E x A Q E' (pf : infer_postcondition VC P E x A Q E') =>
     wf_var_context VC)
    (fun VC P E x A Q E' (pf : check_postcondition VC P E x A Q E') =>
     wf_var_context VC)
    (fun VC HC P Q (pf : sequent VC HC P Q) =>
     wf_var_context VC)); intros; auto.
Qed.  

(*Might need a more sophisticated idea for equivalence*)
Axiom wf_equiv : forall VC1 VC2,
      wf_var_context VC1 ->
      var_context_equiv VC1 VC2 ->
      wf_var_context VC2.

Lemma check_prop_equiv : forall VC1 VC2 HC P Q,
      var_context_equiv VC1 VC2 ->
      check_prop VC1 HC P Q ->
      check_prop VC2 HC P Q.
  intros VC1 VC2 HC P Q equiv checkP. 
  assert (wf : wf_var_context VC2). apply wf_equiv with VC1; auto.
    apply check_prop_wf with HC P Q; auto.
  revert VC2 equiv wf.
  apply (mut_check_prop
    (fun VC (pf : wf_var_context VC) => True)
    (fun VC HC PC (pf : wf_prop_context VC HC PC) =>
      forall VC', var_context_equiv VC VC' -> 
      wf_var_context VC' ->
      wf_prop_context VC' HC PC)
    (fun VC A A' (pf : check_type VC A A') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_type VC' A A')
    (fun VC HC P P' (pf : check_prop VC HC P P') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_prop VC' HC P P')
    (fun VC HC h h' (pf : check_heap VC HC h h') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_heap VC' HC h h')
    (fun VC M A M' (pf : check_intro_term VC M A M') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_intro_term VC' M A M') 
    (fun VC K A M (pf : infer_elim_term VC K A M) =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      infer_elim_term VC' K A M)
    (fun VC P E x A Q E' (pf : infer_postcondition VC P E x A Q E') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      infer_postcondition VC' P E x A Q E')
    (fun VC P E x A Q E' (pf : check_postcondition VC P E x A Q E') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_postcondition VC' P E x A Q E')
    (fun VC HC P Q (pf : sequent VC HC P Q) =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      sequent VC' HC P Q)); intros; auto.
  (*Multiply*) apply ciMultiply with n; auto.
  (*Comp Binop*) apply ciCompBinop with m n; auto.
  (*elim term*) apply ciElimTerm with M' A; auto.
  (*Select*) apply ciSelectNum with m n; auto.
  (*Var*) destruct H0. destruct H0 with x.
    apply ieVar with (H3 pf); auto.
    rewrite <- H2 with _ pf _; auto.
  (*return*) apply ipIntroTerm; auto.
  (*Let Dia*) apply ipLetDia with N' E' z R1 R2; auto.
  (*Annotation*) apply ipAnnotation with z; auto.
  (*Alloc*) apply ipAlloc with z sp_alloc; auto.
  (*Dealloc*) apply ipDealloc with sp_dealloc; auto.
  (*Lookup*) apply ipLookup with sp_lookup h; auto.
  (*Mutate*) apply ipMutate with x z sp_mutate; auto.
  (*Send*) apply ipSend; auto.
  (*Receive*) apply ipReceive; auto.
  (*If*) apply ipIf with P1 P2; auto.
  (*Loop*) destruct H13 as [D V]. Hint Unfold var_context_equiv.
    assert (wf_equiv_xy : wf_var_context ((x,A')::(y,A')::VC')).
      apply wf_equiv with ((x,A')::(y,A')::VC); auto.
    assert (wf_equiv_xyz : wf_var_context ((x,A')::(y,A')::(z,A')::VC')).
      apply wf_equiv with ((x,A')::(y,A')::(z,A')::VC); auto.
      apply equiv_cons; auto.
    apply ipLoop with I''' I'''' J J1 J2 J3 J4 N''; auto.
    (*I=>I'*) apply H7; auto. 
    (*J1 /\ J2 => I'*) apply H9; auto.
      (*equiv*) do 3 apply equiv_cons; auto.
    (*I' => J*) apply H10; auto. 
  (*Strengthen*) apply ipStrengthenPre with P0; auto.
  (*Consequent*) apply cpConsequent with R; auto.
  (*sCut*) apply sCut with P0; auto.
  (*forall*) apply sForAllElim with P' M; auto.
  (*exists*) apply sExistsIntro with P' M; auto.
  (*forall heap*) apply sForAllHeapElim with h; auto.
  (*exists heap*) apply sExistsHeapIntro with h; auto.
  (*id*) apply sIdSubst1 with x Q0 Q1; auto.
  (*id*) apply sIdSubst2 with x Q0 Q2; auto.
  (*hid*) apply sHIdSubst1 with h q q1'; auto.
  (*hid*) apply sHIdSubst2 with h q q2'; auto.
  (*hid*) apply sHIdSubstIntro1 with h q q1'; auto.
Qed.

Hint Resolve check_prop_equiv.

Lemma infer_postcondition_equiv : forall VC1 VC2 P E x A Q E',
      var_context_equiv VC1 VC2 ->
      infer_postcondition VC1 P E x A Q E' ->
      infer_postcondition VC2 P E x A Q E'.
  intros until E'; intros equiv infer1.
  assert (wf : wf_var_context VC2).
    apply wf_equiv with VC1; auto.
    eapply infer_postcondition_wf; eauto.
  revert VC2 equiv wf.
  apply (mut_infer_postcondition
    (fun VC (pf : wf_var_context VC) => True)
    (fun VC HC PC (pf : wf_prop_context VC HC PC) =>
      forall VC', var_context_equiv VC VC' -> 
      wf_var_context VC' ->
      wf_prop_context VC' HC PC)
    (fun VC A A' (pf : check_type VC A A') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_type VC' A A')
    (fun VC HC P P' (pf : check_prop VC HC P P') => True)
    (fun VC HC h h' (pf : check_heap VC HC h h') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_heap VC' HC h h')
    (fun VC M A M' (pf : check_intro_term VC M A M') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_intro_term VC' M A M') 
    (fun VC K A M (pf : infer_elim_term VC K A M) =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      infer_elim_term VC' K A M)
    (fun VC P E x A Q E' (pf : infer_postcondition VC P E x A Q E') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      infer_postcondition VC' P E x A Q E')
    (fun VC P E x A Q E' (pf : check_postcondition VC P E x A Q E') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_postcondition VC' P E x A Q E')
    (fun VC HC P Q (pf : sequent VC HC P Q) =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      sequent VC' HC P Q)); intros; eauto.
  (*Computation*) step; eauto.
    apply check_prop_equiv with ((x0,A')::VC); auto.
  (*HUpdate*) step.
  (*Var*) destruct H0. destruct H0 with x0.
    apply ieVar with (H3 pf); auto.
    rewrite <- H2 with _ pf _; auto.
  (*return*) apply ipIntroTerm; eauto.
  (*Let Dia*) apply ipLetDia with N' E'0 z R1 R2; eauto.
    apply check_prop_equiv with ((x0,A0)::VC); auto.
  (*Annotation*) apply ipAnnotation with z; eauto.
  (*Alloc*) apply ipAlloc with z sp_alloc; eauto.
  (*Dealloc*) apply ipDealloc with sp_dealloc; eauto.
  (*Lookup*) apply ipLookup with sp_lookup h; eauto.
  (*Mutate*) apply ipMutate with x0 z sp_mutate; eauto.
  (*Send*) apply ipSend; eauto.
  (*Receive*) apply ipReceive; eauto.
  (*If*) apply ipIf with P1 P2; eauto.
  (*Loop*) destruct H13 as [D V]. Hint Unfold var_context_equiv.
    assert (wf_equiv_xy : wf_var_context ((x0,A')::(y,A')::VC')).
      apply wf_equiv with ((x0,A')::(y,A')::VC); auto.
    assert (wf_equiv_xyz : wf_var_context ((x0,A')::(y,A')::(z,A')::VC')).
      apply wf_equiv with ((x0,A')::(y,A')::(z,A')::VC); auto.
      apply equiv_cons; auto.
    apply ipLoop with I''' I'''' J J1 J2 J3 J4 N''; eauto.
    (*intro term*) apply H6; auto.
    (*I=>I'*) apply check_prop_equiv with ((x0,A')::(y,A')::VC); auto.
    (*J1 /\ J2 => I'*) apply H9; auto.
      (*equiv*) do 3 apply equiv_cons; auto.
    (*I' => J*) apply H10; auto. 
    (*F*) apply H11; auto.
    (*E0*) apply H12; auto.
  (*Strengthen*) apply ipStrengthenPre with P0; eauto.
  (*Consequent*) apply cpConsequent with R; eauto.
    apply check_prop_equiv with ((x0,A0)::VC); auto.
  (*sCut*) apply sCut with P0; eauto.
  (*And*) apply sAnd2; auto.
  (*Or*) apply sOr1; auto.
  (*Implies*) apply sImplies1; auto.
  (*forall*) apply sForAllElim with P' M; auto.
  (*forall*) apply sForAllIntro; auto.
  (*exists*) apply sExistsElim; auto.
  (*exists*) apply sExistsIntro with P' M; auto.
  (*forall heap*) apply sForAllHeapElim with h; auto.
  (*exists heap*) apply sExistsHeapIntro with h; auto.
Qed.

Hint Resolve infer_postcondition_equiv.

Lemma check_intro_term_equiv : forall VC1 VC2 M A M',
      var_context_equiv VC1 VC2 ->
      check_intro_term VC1 M A M' ->
      check_intro_term VC2 M A M'.
  intros until M'; intros equiv infer1.
  assert (wf : wf_var_context VC2).
    apply wf_equiv with VC1; auto.
    apply check_intro_term_wf with M A M'; auto.
  revert VC2 equiv wf.
  apply (mut_check_intro_term
    (fun VC (pf : wf_var_context VC) => True)
    (fun VC HC PC (pf : wf_prop_context VC HC PC) =>
      forall VC', var_context_equiv VC VC' -> 
      wf_var_context VC' ->
      wf_prop_context VC' HC PC)
    (fun VC A A' (pf : check_type VC A A') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_type VC' A A')
    (fun VC HC P P' (pf : check_prop VC HC P P') => True)
    (fun VC HC h h' (pf : check_heap VC HC h h') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_heap VC' HC h h')
    (fun VC M A M' (pf : check_intro_term VC M A M') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_intro_term VC' M A M') 
    (fun VC K A M (pf : infer_elim_term VC K A M) =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      infer_elim_term VC' K A M)
    (fun VC P E x A Q E' (pf : infer_postcondition VC P E x A Q E') => True)
    (fun VC P E x A Q E' (pf : check_postcondition VC P E x A Q E') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_postcondition VC' P E x A Q E')
    (fun VC HC P Q (pf : sequent VC HC P Q) =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      sequent VC' HC P Q)); intros; eauto.
  (*Computation*) step; eauto.
    apply check_prop_equiv with ((x,A')::VC); auto.
  (*HUpdate*) step; eauto.
  (*Var*) destruct H0. destruct H0 with x.
    apply ieVar with (H3 pf); auto.
    rewrite <- H2 with _ pf _; auto.
  (*Consequent*) apply cpConsequent with R; eauto.
    apply check_prop_equiv with ((x,A0)::VC); auto.
  (*sCut*) apply sCut with P; auto.
  (*And*) apply sAnd2; auto.
  (*Or*) apply sOr1; auto.
  (*Implies*) apply sImplies1; auto.
  (*forall*) apply sForAllElim with P' M0; auto. 
  (*forall*) apply sForAllIntro; auto.
  (*exists*) apply sExistsElim; auto.
  (*exists*) apply sExistsIntro with P' M0; auto.
  (*forall heap*) apply sForAllHeapElim with h; auto.
  (*exists heap*) apply sExistsHeapIntro with h; auto.
Qed.

Hint Resolve check_intro_term_equiv.

Lemma sequent_equiv : forall VC1 VC2 HC PC1 PC2,
      var_context_equiv VC1 VC2 ->
      sequent VC1 HC PC1 PC2 ->
      sequent VC2 HC PC1 PC2.
Proof.
  intros until PC2; intros equiv infer1.
  assert (wf : wf_var_context VC2).
    apply wf_equiv with VC1; auto.
    apply sequent_wf with HC PC1 PC2; auto.
  revert VC2 equiv wf.
  apply (mut_sequent
    (fun VC (pf : wf_var_context VC) => True)
    (fun VC HC PC (pf : wf_prop_context VC HC PC) =>
      forall VC', var_context_equiv VC VC' -> 
      wf_var_context VC' ->
      wf_prop_context VC' HC PC)
    (fun VC A A' (pf : check_type VC A A') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_type VC' A A')
    (fun VC HC P P' (pf : check_prop VC HC P P') => True)
    (fun VC HC h h' (pf : check_heap VC HC h h') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_heap VC' HC h h')
    (fun VC M A M' (pf : check_intro_term VC M A M') => True)
    (fun VC K A M (pf : infer_elim_term VC K A M) =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      infer_elim_term VC' K A M)
    (fun VC P E x A Q E' (pf : infer_postcondition VC P E x A Q E') => True)
    (fun VC P E x A Q E' (pf : check_postcondition VC P E x A Q E') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_postcondition VC' P E x A Q E')
    (fun VC HC P Q (pf : sequent VC HC P Q) =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      sequent VC' HC P Q)); intros; auto.
  (*wf_prop_context*) step. apply check_prop_equiv with VC; auto.
  (*computation type*) step. 
    apply check_prop_equiv with VC; auto. apply check_prop_equiv with ((x,A')::VC); auto.
  (*hUpdate*) step; eauto. 
  (*Var*) destruct H0. destruct H0 with x. apply ieVar with (H3 pf); auto.
    rewrite <- H2 with _ pf _; auto.
  (*Cast*) apply ieCast; eauto. 
  (*Consequent*)
    apply cpConsequent with R; eauto.
    apply check_prop_equiv with ((x,A)::VC); auto.
  (*Cut*) apply sCut with P; auto.
  (*ForAll*) apply sForAllElim with P' M; eauto. 
  (*exists*) apply sExistsIntro with P' M; eauto. 
  (*forall heap*) apply sForAllHeapElim with h; auto.
  (*exists heap*) apply sExistsHeapIntro with h; auto.
  (*id*) apply sIdSubst1 with x Q Q1; auto.
  (*id*) apply sIdSubst2 with x Q Q2; auto.
  (*hid*) apply sHIdSubst1 with h q q1'; auto.
  (*hid*) apply sHIdSubst2 with h q q2'; auto.
  (*hid*) apply sHIdSubstIntro1 with h q q1'; auto.
Qed.

Hint Resolve sequent_equiv.

Lemma check_postcondition_equiv : forall VC1 VC2 P E x A Q E',
      var_context_equiv VC1 VC2 ->
      check_postcondition VC1 P E x A Q E' ->
      check_postcondition VC2 P E x A Q E'.
  intros until E'; intros equiv infer1.
  assert (wf : wf_var_context VC2).
    apply wf_equiv with VC1; auto.
    apply check_postcondition_wf with P E x A Q E'; auto.
  revert VC2 equiv wf.
  apply (mut_check_postcondition
    (fun VC (pf : wf_var_context VC) => True)
    (fun VC HC PC (pf : wf_prop_context VC HC PC) =>
      forall VC', var_context_equiv VC VC' -> 
      wf_var_context VC' ->
      wf_prop_context VC' HC PC)
    (fun VC A A' (pf : check_type VC A A') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_type VC' A A')
    (fun VC HC P P' (pf : check_prop VC HC P P') => True)
    (fun VC HC h h' (pf : check_heap VC HC h h') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_heap VC' HC h h')
    (fun VC M A M' (pf : check_intro_term VC M A M') => True)
    (fun VC K A M (pf : infer_elim_term VC K A M) =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      infer_elim_term VC' K A M)
    (fun VC P E x A Q E' (pf : infer_postcondition VC P E x A Q E') => True)
    (fun VC P E x A Q E' (pf : check_postcondition VC P E x A Q E') =>
      forall VC', var_context_equiv VC VC' ->
      wf_var_context VC' ->
      check_postcondition VC' P E x A Q E')
    (fun VC HC P Q (pf : sequent VC HC P Q) => True));
      intros; eauto.
  (*computation type*) step; eauto. 
    apply check_prop_equiv with ((x0,A')::VC); auto.
  (*HUpdate*) step; eauto. 
  (*Var*)  destruct H0. destruct H0 with x0. apply ieVar with (H3 pf); auto.
    rewrite <- H2 with _ pf _; auto.
  (*Consequent*)
    apply cpConsequent with R; eauto.
    apply check_prop_equiv with ((x0,A0)::VC); auto.
    apply sequent_equiv with ((x0,A0)::VC); auto.
Qed.

Hint Resolve check_postcondition_equiv.

Lemma equiv_eq : forall x A B VC1 VC2,
      var_context_equiv VC1 VC2 ->
      var_context_equiv ((x,A)::VC1) ((x,A)::(x,B)::VC2).
Proof.
  destruct 1 as [D V]; split.
  (*domain_equiv*) intro z; split; intros F.
    (*->*) destruct (var_dec z x).
      (*z=x*) rewrite e; apply InHead.
      (*z<>x*) dependent destruction F.
        absurd (x<>x); auto. do 2 apply InTail; apply D; auto.
    (*<-*) destruct (var_dec z x).
      (*z=x*) rewrite e; apply InHead.
      (*z<>x*) dependent destruction F.
        absurd (x<>x); auto. dependent destruction F.
        absurd (x<>x); auto. apply InTail; apply D; auto.
  (*vals_equiv*) intros z pf1 pf2; simpl. destruct (var_dec z x); auto.
Qed.

Lemma equiv_swap : forall x y A B VC1 VC2,
      var_context_equiv VC1 VC2 ->
      x <> y ->
      var_context_equiv ((x,A)::(y,B)::VC1) ((y,B)::(x,A)::VC2).
Proof.
  destruct 1 as [D V]; intros; split.
  (*domain_equiv*) intro z; split; intros F.
    (*->*) dependent destruction F; [
      (*z=x*) apply InTail; apply InHead; apply D |
      dependent destruction F; [
      (*z=y*) apply InHead; apply D |
      (*x<>y*) do 2 apply InTail; apply D; auto ] ].
    (*<-*) dependent destruction F; [
      (*z=x*) apply InTail; apply InHead; apply D |
      dependent destruction F; [
      (*z=y*) apply InHead; apply D |
      (*x<>y*) do 2 apply InTail; apply D; auto ] ].
  (*vals_equiv*) intros z pf1 pf2; simpl.
    destruct (var_dec z x); auto. destruct (var_dec z y); auto.
    absurd (x=y); auto. rewrite <- e; auto.
    destruct (var_dec z y); auto.
Qed.

Ltac check_prop_swap :=
  match goal with
  | [n : ?x <> ?y |- check_prop ((?x,?A)::(?y,?B)::?VC) _ _ _] =>
    apply check_prop_equiv with ((y,B)::(x,A)::VC); auto;
    try (apply equiv_swap; auto)
  | [n : ?y <> ?x |- check_prop ((?x,?A)::(?y,?B)::?VC) _ _ _] =>
    apply check_prop_equiv with ((y,B)::(x,A)::VC); auto;
    try (apply equiv_swap; auto)
  end.
Ltac ip_swap :=
  match goal with
  | [n : ?x <> ?y |- infer_postcondition ((?x,?A)::(?y,?B)::?VC) _ _ _ _ _ _] =>
    apply infer_postcondition_equiv with ((y,B)::(x,A)::VC); auto;
    try (apply equiv_swap; auto)
  | [n : ?y <> ?x |- infer_postcondition ((?x,?A)::(?y,?B)::?VC) _ _ _ _ _ _] =>
    apply infer_postcondition_equiv with ((y,B)::(x,A)::VC); auto;
    try (apply equiv_swap; auto)
  end.
Ltac check_prop_eq :=
  match goal with
  | [e : ?x = ?y |- check_prop ((?x,?A)::(?y,_)::?VC) _ _ _] =>
    rewrite <- e in *;
    apply check_prop_equiv with ((x,A)::VC); auto;
    try (apply equiv_eq; auto)
  | [e : ?y = ?x |- check_prop ((?x,?A)::(?y,_)::?VC) _ _ _] =>
    rewrite e in *;
    apply check_prop_equiv with ((x,A)::VC); auto;
    try (apply equiv_eq; auto)
  end.
Ltac ip_eq :=
  match goal with
  | [e : ?x = ?y |- infer_postcondition ((?x,?A)::(?y,_)::?VC) _ _ _ _ _ _] =>
    rewrite <- e in *;
    apply infer_postcondition_equiv with ((x,A)::VC); auto;
    try (apply equiv_eq; auto)
  | [e : ?y = ?x |- infer_postcondition ((?x,?A)::(?y,_)::?VC) _ _ _ _ _ _] =>
    rewrite e in *;
    apply infer_postcondition_equiv with ((x,A)::VC); auto;
    try (apply equiv_eq; auto)
  end.
Ltac in_head :=
  match goal with
  | [ H : ?z = ?x |- in_var_context ?z ((?x,_)::_) ] => rewrite H; apply InHead
  | [ H : ?x = ?z |- in_var_context ?z ((?x,_)::_) ] => rewrite H; apply InHead
  | [ |- in_var_context ?x ((?x,_)::_) ] => apply InHead
  end.
Ltac n_in_head :=
  match goal with
  | [_ : ?x <> ?y |- ~ in_var_context ?y ((?x,_)::_) ] =>
    inversion 1; intuition
  | [_ : ?y <> ?x |- ~ in_var_context ?y ((?x,_)::_) ] =>
    inversion 1; intuition
  | [_ : ?x <> ?y, H : in_var_context ?y ((?x,_)::_) |- False ] =>
    inversion H; intuition
  | [_ : ?y <> ?x, H : in_var_context ?y ((?x,_)::_) |- False ] =>
    inversion H; intuition
  end.
    
Hint Resolve equiv_refl.
Lemma check_prop_VC_weakening : forall VC HC P P',
      check_prop VC HC P P' ->
      forall x m n, ~ in_var_context x VC ->
      check_prop ((x,By m n)::VC) HC P P'.
Proof.  
  intros VC HC P P' checkP.
  apply (mut_check_prop
    (fun VC (pf : wf_var_context VC) => forall x m n,
      wf_var_context ((x,By m n)::VC))
    (fun VC HC PC (pf : wf_prop_context VC HC PC) => forall x m n,
      ~ in_var_context x VC ->
      wf_prop_context ((x,By m n)::VC) HC PC)
    (fun VC A A' (pf : check_type VC A A') => forall x m n,
      ~ in_var_context x VC ->
      check_type ((x,By m n)::VC) A A')
    (fun VC HC P P' (pf : check_prop VC HC P P') => forall x m n,
      ~ in_var_context x VC ->
      check_prop ((x,By m n)::VC) HC P P')
    (fun VC HC h h' (pf : check_heap VC HC h h') => forall x m n,
      ~ in_var_context x VC ->
      check_heap ((x,By m n)::VC) HC h h')
    (fun VC M A M' (pf : check_intro_term VC M A M') => forall x m n,
      ~ in_var_context x VC ->
      check_intro_term ((x,By m n)::VC) M A M')
    (fun VC K A M (pf : infer_elim_term VC K A M) => forall x m n,
      ~ in_var_context x VC ->
      infer_elim_term ((x,By m n)::VC) K A M)
    (fun VC P E y B Q E' (pf : infer_postcondition VC P E y B Q E') => 
      forall x m n,
      ~ in_var_context x VC ->
      infer_postcondition ((x,By m n)::VC) P E y B Q E')
    (fun VC P E y B Q E' (pf : check_postcondition VC P E y B Q E') => 
      forall x m n,
      ~ in_var_context x VC ->
      check_postcondition ((x,By m n)::VC) P E y B Q E')
    (fun VC HC P Q (pf : sequent VC HC P Q) => forall x m n,
      ~ in_var_context x VC ->
      sequent ((x,By m n)::VC) HC P Q));
    intros; auto.

  (*Computation Type*) rename x0 into y. step.
    destruct (var_dec x y).
    (*x=y*) check_prop_eq. 
    (*x<>y*) check_prop_swap. apply H2; auto; n_in_head.
  (*ForAll*) step. rename x0 into y. destruct (var_dec x y).
    (*x=y*) check_prop_eq. 
    (*x<>y*) check_prop_swap. apply H1; auto; n_in_head.
  (*Exists*) step. rename x0 into y. destruct (var_dec x y).
    (*x=y*) check_prop_eq.
    (*x<>y*) check_prop_swap. apply H1; auto; n_in_head.
  (*Multiply*) eauto. 
  (*CompBinop*) eauto.
  (*check elim term*) eauto.
  (*Select*) eauto. 
  (*Var*) rename x0 into y. destruct (var_dec x y).
    (*x=y*) absurd (in_var_context x VC0); auto. rewrite e0; auto.
    (*x<>y*) apply ieVar with (InTail y (By m n) pf); auto.
      rewrite <- get_neq with _ _ _ _ pf _; auto.
  (*Return*) step.
  (*LetDia*) rename x0 into x'. destruct (var_dec x x').
    (*x=x'*) rewrite <- e in *.
      assert (var_context_equiv ((x,A)::VC0) ((x,A)::(x,By m n)::VC0)).
        apply equiv_eq; auto.
      apply ipLetDia with N' E' z R1 R2; auto.
        apply check_prop_equiv with ((x,A)::VC0); auto.
        apply infer_postcondition_equiv with ((x,A)::VC0); auto.
    (*x<>x'*)
      assert (var_context_equiv ((x',By m n)::(x,A)::VC0)
                                ((x,A)::(x',By m n)::VC0)).
        apply equiv_swap; auto.
      assert (~ in_var_context x' ((x,A)::VC0)).
        n_in_head.
      apply ipLetDia with N' E' z R1 R2; auto.
        apply check_prop_equiv with ((x',By m n)::(x,A)::VC0); auto.
        apply infer_postcondition_equiv with ((x',By m n)::(x,A)::VC0); auto.
  (*Annotation*) apply ipAnnotation with z; auto.
  (*Alloc*) rename x0 into x'. apply ipAlloc with z sp_alloc; auto.
    (*infer*) destruct (var_dec x x').
      (*x'=x*) ip_eq.
      (*x<>x'*) ip_swap. apply H4; auto; n_in_head.
  (*Dealloc*) rename x0 into x'. apply ipDealloc with sp_dealloc; auto;
    destruct (var_dec x x').
    (*infer*) 
      (*x=x'*) ip_eq.
      (*x<>x'*) ip_swap. apply H5; auto; n_in_head.
  (*Lookup*) rename x0 into x'. apply ipLookup with sp_lookup h; auto;
    destruct (var_dec x x').
    (*infer*) 
      (*x=x'*) ip_eq.
      (*x<>x'*) ip_swap. apply H5; auto; n_in_head.
  (*Mutate*) apply ipMutate with x z sp_mutate; auto.
  (*Send*) step.
  (*Receive*) rename x0 into x'. apply ipReceive; auto; destruct (var_dec x x').
    (*infer*) 
      (*x=x'*) ip_eq. 
      (*x<>x'*) ip_swap. apply H4; auto; n_in_head.
  (*If*) apply ipIf with P1 P2; auto. destruct (var_dec x x0).
    (*x=x0*) ip_eq.
    (*x<>x0*) ip_swap. apply H6; auto; n_in_head.
  (*Loop*) rename x0 into x'. 
    apply ipLoop with I''' I'''' J J1 J2 J3 J4 N''; auto.
      (*wf_var_context*) destruct (var_dec y x'); auto.
        (*y=x'*) rewrite <- e in *; clear x' e.
          apply wf_equiv with ((x,A')::(y,A')::VC0); auto. 
          apply equiv_cons. apply equiv_eq; auto.
        (*y<>x'*) apply wf_equiv with ((x,A')::(x',By m n)::(y,A')::VC0); auto.
          destruct (var_dec x x').
        (*x=x'*) rewrite <- e in *; clear x' e.
          apply wf_equiv with ((x,A')::(y,A')::VC0); auto. apply equiv_eq; auto.
        (*x<>x'*) apply wf_equiv with ((x',By m n)::(x,A')::(y,A')::VC0); auto.
        (*equiv*) apply equiv_swap; auto.
        (*equiv*) apply equiv_cons. apply equiv_swap; auto.
      (*wf_var_context*) destruct (var_dec z x'); auto.
        (*z=x'*) rewrite <- e in *; clear x' e.
          apply wf_equiv with ((x,A')::(y,A')::(z,A')::VC0); auto.
          do 2 apply equiv_cons; apply equiv_eq; auto.
        (*z<>x'*) apply wf_equiv with ((x,A')::(y,A')::(x',By m n)::(z,A')::VC0); auto.
          destruct (var_dec y x').
        (*x'=z*) rewrite <- e in *; clear x' e.
          apply wf_equiv with ((x,A')::(y,A')::(z,A')::VC0); auto.
          apply equiv_cons; apply equiv_eq; auto.
        (*y<>x'*) apply wf_equiv with ((x,A')::(x',By m n)::(y,A')::(z,A')::VC0); auto.
          destruct (var_dec x x').
        (*x=x'*) rewrite <- e in *; clear x' e.
          apply wf_equiv with ((x,A')::(y,A')::(z,A')::VC0); auto.
          apply equiv_eq; auto.
        (*x<>x'*) apply wf_equiv with ((x',By m n)::(x,A')::(y,A')::(z,A')::VC0); auto.
          apply equiv_swap; auto.
        (*equiv*) apply equiv_cons; apply equiv_swap; auto.
        (*equiv*) do 2 apply equiv_cons; apply equiv_swap; auto.
      (*check_intro_term*) destruct (var_dec x x'); auto.
        (*x=x'*) rewrite_vars. apply check_intro_term_equiv with ((x',A')::VC0); auto. apply equiv_eq; auto.
        (*x<>x'*) apply check_intro_term_equiv with ((x',By m n)::(x,A')::VC0); auto.
          apply equiv_swap; auto. apply H6; auto; n_in_head.
      (*check_prop I I'*) destruct (var_dec y x'); auto.
        (*y=x'*) rewrite_vars. apply check_prop_equiv with ((x,A')::(x',A')::VC0); auto.
          apply equiv_cons; auto. apply equiv_eq; auto.
          (*wf_var_context*) 
        (*y<>x'*) apply check_prop_equiv with ((x,A')::(x',By m n)::(y,A')::VC0); auto.
          (*equiv*) apply equiv_cons; auto. apply equiv_swap; auto.
        destruct (var_dec x x'); auto.
        (*x=x'*) rewrite_vars. apply check_prop_equiv with ((x',A')::(y,A')::VC0); auto.
          apply equiv_eq; auto. 
        (*x<>x'*) apply check_prop_equiv with ((x',By m n)::(x,A')::(y,A')::VC0); auto.
          (*equiv*) apply equiv_swap; auto. 
        apply H7; auto.
        (*~ in_var_context*) inversion 1; auto. 
          inversion H17; auto.
    (*sequent*) destruct (var_dec z x'); auto.
      (*z=x'*) rewrite <- e in *; clear x' e.
        apply sequent_equiv with ((x,A')::(y,A')::(z,A')::VC0); auto.
        do 2 apply equiv_cons; apply equiv_eq; auto.
      (*z<>x'*) apply sequent_equiv with ((x,A')::(y,A')::(x',By m n)::(z,A')::VC0); auto.
        do 2 apply equiv_cons; apply equiv_swap; auto.
      destruct (var_dec y x').
      (*y=x'*) rewrite <- e in *; clear x' e.
        apply sequent_equiv with ((x,A')::(y,A')::(z,A')::VC0); auto.
        apply equiv_cons; apply equiv_eq; auto.
      (*y<>x'*) apply sequent_equiv with ((x,A')::(x',By m n)::(y, A')::(z,A')::VC0); auto.
        apply equiv_cons; apply equiv_swap; auto.
      destruct (var_dec x x').
      (*x=x'*) rewrite <- e in *; clear x' e.
        apply sequent_equiv with ((x,A')::(y,A')::(z,A')::VC0); auto.
        apply equiv_eq; auto.
      (*x<>x'*) apply sequent_equiv with ((x',By m n)::(x,A')::(y,A')::(z,A')::VC0); auto.
        apply equiv_swap; auto.
      apply H9; auto.
      (*~ in_var_context*) inversion 1; auto. inversion H17; auto. inversion H22; auto.
    (*sequent*) destruct (var_dec y x').
      (*y=x'*) rewrite <- e in *; clear x' e.
        apply sequent_equiv with ((x,A')::(y,A')::VC0); auto.
        apply equiv_cons; apply equiv_eq; auto.
      (*y<>x'*) apply sequent_equiv with ((x,A')::(x',By m n)::(y, A')::VC0); auto.
        apply equiv_cons; apply equiv_swap; auto.
      destruct (var_dec x x').
      (*x=x'*) rewrite <- e in *; clear x' e.
        apply sequent_equiv with ((x,A')::(y,A')::VC0); auto.
        apply equiv_eq; auto.
      (*x<>x'*) apply sequent_equiv with ((x',By m n)::(x,A')::(y,A')::VC0); auto.
        apply equiv_swap; auto.
      apply H10; auto.
      inversion 1; auto. inversion H17; auto.
    (*check_postcondition*) destruct (var_dec x x').
      (*x=x'*) rewrite <- e in *; clear x' e.
        apply check_postcondition_equiv with ((x,A')::VC0); auto.
        apply equiv_eq; auto.
      (*x<>x'*) apply check_postcondition_equiv with ((x',By m n)::(x,A')::VC0); auto.
        apply equiv_swap; auto.
      apply H11; auto. inversion 1; auto.
    (*infer_postcondition*) destruct (var_dec y x').
      (*y=x'*) rewrite <- e in *; clear x' e.
        apply infer_postcondition_equiv with ((y,A')::VC0); auto.
        apply equiv_eq; auto.
      (*y<>x'*) apply infer_postcondition_equiv with ((x',By m n)::(y,A')::VC0); auto.
        apply equiv_swap; auto.
      apply H12; auto. inversion 1; auto.
  (*Strengthen*) apply ipStrengthenPre with P0; auto.
  (*Check*) destruct (var_dec x x0).
    (*x=x0*) rewrite <- e in *; clear x0 e.
      apply cpConsequent with R; auto.
      (*check_prop*) apply check_prop_equiv with ((x,A)::VC0); auto.
        (*equiv*) apply equiv_eq; auto.
      (*sequent*) apply sequent_equiv with ((x,A)::VC0); auto.
        (*equiv*) apply equiv_eq; auto.
    (*x<>x0*) apply cpConsequent with R; auto.
      (*check_prop*) apply check_prop_equiv with ((x0,By m n)::(x,A)::VC0); auto.
        (*equiv*) apply equiv_swap; auto.
        apply H2; auto. inversion 1; auto.
      (*sequent*) apply sequent_equiv with ((x0,By m n)::(x,A)::VC0); auto.
        (*equiv*) apply equiv_swap; auto.
        apply H4; auto. inversion 1; auto.
  (*Cut*) apply sCut with P0; auto.
  (*ForAllElim*) apply sForAllElim with P'0 M; auto.
  (*ForAllIntro*) apply sForAllIntro; auto.
    destruct (var_dec x x0).
    (*x=x0*) rewrite <- e in *; clear e x0.
      apply sequent_equiv with ((x,A)::VC0); auto.
      (*equiv*) apply equiv_eq; auto.
    (*x<>x0*) apply sequent_equiv with ((x0,By m n)::(x,A)::VC0); auto.
      (*equiv*) apply equiv_swap; auto.
      apply H3; auto. inversion 1; auto.
  (*ExistsElim*) apply sExistsElim; auto.
    destruct (var_dec x x0).
    (*x=x0*) rewrite <- e in *; clear e x0.
      apply sequent_equiv with ((x,A)::VC0); auto.
      (*equiv*) apply equiv_eq; auto.
    (*x<>x0*) apply sequent_equiv with ((x0,By m n)::(x,A)::VC0); auto.
      (*equiv*) apply equiv_swap; auto.
      apply H3; auto. inversion 1; auto.
  (*ExistsIntro*) apply sExistsIntro with P'0 M; auto.
  (*ForAllHeap*) apply sForAllHeapElim with h; auto.
  (*ExistsHeap*) apply sExistsHeapIntro with h; auto.
  (*IdSubst1*) apply sIdSubst1 with x Q Q1; auto.
  (*IdSubst2*) apply sIdSubst2 with x Q Q2; auto.
  (*HIdSubst1*) apply sHIdSubst1 with h q q1'; auto.
  (*HIdSubst2*) apply sHIdSubst2 with h q q2'; auto.
  (*HIdSubstIntro*) apply sHIdSubstIntro1 with h q q1'; auto.
Qed.

Hint Resolve check_prop_VC_weakening.

Lemma check_intro_term_VC_weakening : forall VC x m n M M',
      check_intro_term VC M (By m n) M' ->
      ~ in_var_context x VC ->
      check_intro_term ((x,By m n)::VC) M (By m n) M'.
Proof.  
  intros VC x m n M M' checkM.
  apply (mut_check_intro_term
    (fun VC (pf : wf_var_context VC) => forall x m n,
      wf_var_context ((x,By m n)::VC))
    (fun VC HC PC (pf : wf_prop_context VC HC PC) => forall x m n,
      ~ in_var_context x VC ->
      wf_prop_context ((x,By m n)::VC) HC PC)
    (fun VC A A' (pf : check_type VC A A') => forall x m n,
      ~ in_var_context x VC ->
      check_type ((x,By m n)::VC) A A')
    (fun VC HC P P' (pf : check_prop VC HC P P') => True) (*forall x m n,
      ~ in_var_context x VC ->
      check_prop ((x,By m n)::VC) HC P P')*)
    (fun VC HC h h' (pf : check_heap VC HC h h') => forall x m n,
      ~ in_var_context x VC ->
      check_heap ((x,By m n)::VC) HC h h')
    (fun VC M A M' (pf : check_intro_term VC M A M') => forall x m n,
      ~ in_var_context x VC ->
      check_intro_term ((x,By m n)::VC) M A M')
    (fun VC K A M (pf : infer_elim_term VC K A M) => forall x m n,
      ~ in_var_context x VC ->
      infer_elim_term ((x,By m n)::VC) K A M)
    (fun VC P E y B Q E' (pf : infer_postcondition VC P E y B Q E') => 
      forall x m n,
      ~ in_var_context x VC ->
      infer_postcondition ((x,By m n)::VC) P E y B Q E')
    (fun VC P E y B Q E' (pf : check_postcondition VC P E y B Q E') => 
      forall x m n,
      ~ in_var_context x VC ->
      check_postcondition ((x,By m n)::VC) P E y B Q E')
    (fun VC HC P Q (pf : sequent VC HC P Q) => forall x m n,
      ~ in_var_context x VC ->
      sequent ((x,By m n)::VC) HC P Q));
    intros; auto.
  (*Computation Type*) clear x. rename x0 into y, x1 into x. step.
    destruct (var_dec y x).
    (*x=y*) check_prop_eq. 
    (*x<>y*) check_prop_swap. apply check_prop_VC_weakening; auto; n_in_head.
  (*Multiply*) eauto. 
  (*CompBinop*) eauto.
  (*check elim term*) eauto.
  (*Select*) eauto. 
  (*Var*) clear x; rename x0 into x, x1 into y. destruct (var_dec x y).
    (*x=y*) absurd (in_var_context x VC0); auto. rewrite e0; auto.
    (*x<>y*) apply ieVar with (InTail y (By m0 n0) pf); auto.
      rewrite <- get_neq with _ _ _ _ pf _; auto.
  (*Return*) step.
  (*LetDia*) clear x; rename x0 into x, x1 into x'. destruct (var_dec x x').
    (*x=x'*) rewrite <- e in *.
      assert (var_context_equiv ((x,A)::VC0) ((x,A)::(x,By m0 n0)::VC0)).
        apply equiv_eq; auto.
      apply ipLetDia with N' E' z R1 R2; auto.
        apply check_prop_equiv with ((x,A)::VC0); auto.
        apply infer_postcondition_equiv with ((x,A)::VC0); auto.
    (*x<>x'*)
      assert (var_context_equiv ((x',By m0 n0)::(x,A)::VC0)
                                ((x,A)::(x',By m0 n0)::VC0)).
        apply equiv_swap; auto.
      assert (~ in_var_context x' ((x,A)::VC0)).
        n_in_head.
      apply ipLetDia with N' E' z R1 R2; auto.
        apply check_prop_equiv with ((x',By m0 n0)::(x,A)::VC0); auto.
        apply infer_postcondition_equiv with ((x',By m0 n0)::(x,A)::VC0); auto.
  (*Annotation*) apply ipAnnotation with z; auto.
  (*Alloc*) clear x; rename x0 into x, x1 into x'. 
    apply ipAlloc with z sp_alloc; auto.
    (*infer*) destruct (var_dec x x').
      (*x'=x*) ip_eq; apply equiv_eq; auto.
      (*x<>x'*) ip_swap. apply H4; auto; n_in_head.
  (*Dealloc*) clear x; rename x0 into x, x1 into x'. 
    apply ipDealloc with sp_dealloc; auto; destruct (var_dec x x').
    (*infer*) 
      (*x=x'*) ip_eq.
      (*x<>x'*) ip_swap. apply H5; auto; n_in_head.
  (*Lookup*) clear x; rename x0 into x, x1 into x'. 
    apply ipLookup with sp_lookup h; auto; destruct (var_dec x x').
    (*infer*) 
      (*x=x'*) ip_eq.
      (*x<>x'*) ip_swap. apply H5; auto; n_in_head.
  (*Mutate*) apply ipMutate with x0 z sp_mutate; auto.
  (*Send*) step.
  (*Receive*) clear x; rename x0 into x, x1 into x'. 
    apply ipReceive; auto; destruct (var_dec x x').
    (*infer*) 
      (*x=x'*) ip_eq.
      (*x<>x'*) ip_swap. apply H4; auto; n_in_head.
  (*If*) apply ipIf with P1 P2; auto. destruct (var_dec x0 x1).
    (*x=x0*) ip_eq.
    (*x<>x0*) ip_swap. apply H6; auto; n_in_head.
  (*Loop*) clear x; rename x0 into x, x1 into x'. 
    apply ipLoop with I''' I'''' J J1 J2 J3 J4 N''; auto.
      (*wf_var_context*) destruct (var_dec y x'); auto.
        (*y=x'*) rewrite <- e in *; clear x' e.
          apply wf_equiv with ((x,A')::(y,A')::VC0); auto. 
          apply equiv_cons. apply equiv_eq; auto.
        (*y<>x'*) apply wf_equiv with ((x,A')::(x',By m0 n0)::(y,A')::VC0); auto.
          destruct (var_dec x x').
        (*x=x'*) rewrite <- e in *; clear x' e.
          apply wf_equiv with ((x,A')::(y,A')::VC0); auto. apply equiv_eq; auto.
        (*x<>x'*) apply wf_equiv with ((x',By m0 n0)::(x,A')::(y,A')::VC0); auto.
        (*equiv*) apply equiv_swap; auto.
        (*equiv*) apply equiv_cons. apply equiv_swap; auto.
      (*wf_var_context*) destruct (var_dec z x'); auto.
        (*z=x'*) rewrite <- e in *; clear x' e.
          apply wf_equiv with ((x,A')::(y,A')::(z,A')::VC0); auto.
          do 2 apply equiv_cons; apply equiv_eq; auto.
        (*z<>x'*) apply wf_equiv with ((x,A')::(y,A')::(x',By m0 n0)::(z,A')::VC0); auto.
          destruct (var_dec y x').
        (*x'=z*) rewrite <- e in *; clear x' e.
          apply wf_equiv with ((x,A')::(y,A')::(z,A')::VC0); auto.
          apply equiv_cons; apply equiv_eq; auto.
        (*y<>x'*) apply wf_equiv with ((x,A')::(x',By m0 n0)::(y,A')::(z,A')::VC0); auto.
          destruct (var_dec x x').
        (*x=x'*) rewrite <- e in *; clear x' e.
          apply wf_equiv with ((x,A')::(y,A')::(z,A')::VC0); auto.
          apply equiv_eq; auto.
        (*x<>x'*) apply wf_equiv with ((x',By m0 n0)::(x,A')::(y,A')::(z,A')::VC0); auto.
          apply equiv_swap; auto.
        (*equiv*) apply equiv_cons; apply equiv_swap; auto.
        (*equiv*) do 2 apply equiv_cons; apply equiv_swap; auto.
      (*check_intro_term*) destruct (var_dec x x'); auto.
        (*x=x'*) rewrite_vars. apply check_intro_term_equiv with ((x',A')::VC0); auto. apply equiv_eq; auto.
        (*x<>x'*) apply check_intro_term_equiv with ((x',By m0 n0)::(x,A')::VC0); auto.
          apply equiv_swap; auto. apply H6; auto; n_in_head.
      (*check_prop I I'*) destruct (var_dec y x'); auto.
        (*y=x'*) rewrite_vars. apply check_prop_equiv with ((x,A')::(x',A')::VC0); auto.
          apply equiv_cons; auto. apply equiv_eq; auto.
        (*y<>x'*) apply check_prop_equiv with ((x,A')::(x',By m0 n0)::(y,A')::VC0); auto.
          (*equiv*) apply equiv_cons; auto. apply equiv_swap; auto.
        destruct (var_dec x x'); auto.
        (*x=x'*) rewrite_vars. apply check_prop_equiv with ((x',A')::(y,A')::VC0); auto.
          apply equiv_eq; auto. 
        (*x<>x'*) apply check_prop_equiv with ((x',By m0 n0)::(x,A')::(y,A')::VC0); auto.
          (*equiv*) apply equiv_swap; auto. 
        apply check_prop_VC_weakening; auto.
        (*~ in_var_context*) inversion 1; auto. 
          inversion H17; auto.
    (*sequent*) destruct (var_dec z x'); auto.
      (*z=x'*) rewrite <- e in *; clear x' e.
        apply sequent_equiv with ((x,A')::(y,A')::(z,A')::VC0); auto.
        do 2 apply equiv_cons; apply equiv_eq; auto.
      (*z<>x'*) apply sequent_equiv with ((x,A')::(y,A')::(x',By m0 n0)::(z,A')::VC0); auto.
        do 2 apply equiv_cons; apply equiv_swap; auto.
      destruct (var_dec y x').
      (*y=x'*) rewrite <- e in *; clear x' e.
        apply sequent_equiv with ((x,A')::(y,A')::(z,A')::VC0); auto.
        apply equiv_cons; apply equiv_eq; auto.
      (*y<>x'*) apply sequent_equiv with ((x,A')::(x',By m0 n0)::(y, A')::(z,A')::VC0); auto.
        apply equiv_cons; apply equiv_swap; auto.
      destruct (var_dec x x').
      (*x=x'*) rewrite <- e in *; clear x' e.
        apply sequent_equiv with ((x,A')::(y,A')::(z,A')::VC0); auto.
        apply equiv_eq; auto.
      (*x<>x'*) apply sequent_equiv with ((x',By m0 n0)::(x,A')::(y,A')::(z,A')::VC0); auto.
        apply equiv_swap; auto.
      apply H9; auto.
      (*~ in_var_context*) inversion 1; auto. inversion H17; auto. inversion H22; auto.
    (*sequent*) destruct (var_dec y x').
      (*y=x'*) rewrite <- e in *; clear x' e.
        apply sequent_equiv with ((x,A')::(y,A')::VC0); auto.
        apply equiv_cons; apply equiv_eq; auto.
      (*y<>x'*) apply sequent_equiv with ((x,A')::(x',By m0 n0)::(y, A')::VC0); auto.
        apply equiv_cons; apply equiv_swap; auto.
      destruct (var_dec x x').
      (*x=x'*) rewrite <- e in *; clear x' e.
        apply sequent_equiv with ((x,A')::(y,A')::VC0); auto.
        apply equiv_eq; auto.
      (*x<>x'*) apply sequent_equiv with ((x',By m0 n0)::(x,A')::(y,A')::VC0); auto.
        apply equiv_swap; auto.
      apply H10; auto.
      inversion 1; auto. inversion H17; auto.
    (*check_postcondition*) destruct (var_dec x x').
      (*x=x'*) rewrite <- e in *; clear x' e.
        apply check_postcondition_equiv with ((x,A')::VC0); auto.
        apply equiv_eq; auto.
      (*x<>x'*) apply check_postcondition_equiv with ((x',By m0 n0)::(x,A')::VC0); auto.
        apply equiv_swap; auto.
      apply H11; auto. inversion 1; auto.
    (*infer_postcondition*) destruct (var_dec y x').
      (*y=x'*) rewrite <- e in *; clear x' e.
        apply infer_postcondition_equiv with ((y,A')::VC0); auto.
        apply equiv_eq; auto.
      (*y<>x'*) apply infer_postcondition_equiv with ((x',By m0 n0)::(y,A')::VC0); auto.
        apply equiv_swap; auto.
      apply H12; auto. inversion 1; auto.
  (*Strengthen*) apply ipStrengthenPre with P; auto.
  (*Check*) clear x. rename x0 into x, x1 into x0. destruct (var_dec x x0).
    (*x=x0*) rewrite <- e in *; clear x0 e.
      apply cpConsequent with R; auto.
      (*check_prop*) apply check_prop_equiv with ((x,A)::VC0); auto.
        (*equiv*) apply equiv_eq; auto.
      (*sequent*) apply sequent_equiv with ((x,A)::VC0); auto.
        (*equiv*) apply equiv_eq; auto.
    (*x<>x0*) apply cpConsequent with R; auto.
      (*check_prop*) apply check_prop_equiv with ((x0,By m0 n0)::(x,A)::VC0); auto.
        (*equiv*) apply equiv_swap; auto.
        apply check_prop_VC_weakening; auto. n_in_head.
      (*sequent*) apply sequent_equiv with ((x0,By m0 n0)::(x,A)::VC0); auto.
        (*equiv*) apply equiv_swap; auto.
        apply H4; auto. n_in_head.
  (*Cut*) apply sCut with P; auto.
  (*ForAllElim*) apply sForAllElim with P' M0; auto.
  (*ForAllIntro*) apply sForAllIntro; auto. clear x; rename x0 into x, x1 into x0.
    destruct (var_dec x x0).
    (*x=x0*) rewrite <- e in *; clear e x0.
      apply sequent_equiv with ((x,A)::VC0); auto.
      (*equiv*) apply equiv_eq; auto.
    (*x<>x0*) apply sequent_equiv with ((x0,By m0 n0)::(x,A)::VC0); auto.
      (*equiv*) apply equiv_swap; auto.
      apply H3; auto. inversion 1; auto.
  (*ExistsElim*) apply sExistsElim; auto. clear x; rename x0 into x, x1 into x0.
    destruct (var_dec x x0).
    (*x=x0*) rewrite <- e in *; clear e x0.
      apply sequent_equiv with ((x,A)::VC0); auto.
      (*equiv*) apply equiv_eq; auto.
    (*x<>x0*) apply sequent_equiv with ((x0,By m0 n0)::(x,A)::VC0); auto.
      (*equiv*) apply equiv_swap; auto.
      apply H3; auto. inversion 1; auto.
  (*ExistsIntro*) apply sExistsIntro with P' M0; auto.
  (*ForAllHeap*) apply sForAllHeapElim with h; auto.
  (*ExistsHeap*) apply sExistsHeapIntro with h; auto.
  (*IdSubst1*) apply sIdSubst1 with x0 Q Q1; auto.
  (*IdSubst2*) apply sIdSubst2 with x0 Q Q2; auto.
  (*HIdSubst1*) apply sHIdSubst1 with h q q1'; auto.
  (*HIdSubst2*) apply sHIdSubst2 with h q q2'; auto.
  (*HIdSubstIntro*) apply sHIdSubstIntro1 with h q q1'; auto.
Qed.

(* This lemma should not be hard to prove. We just need
   some infrastructure about equivalence of heap contexts. *)
Lemma check_prop_HC_weakening : forall VC HC x P P',
      check_prop VC HC P P' ->
      ~ (List.In x HC) ->
      check_prop VC (x::HC) P P'.
Admitted.

Fixpoint var_context_subst x h (VC : var_context) : var_context :=
  match VC with
  | List.nil => List.nil
  | ((y,A)::VC) => (y,type_subst x h A)::(var_context_subst x h VC)
  end.

Lemma check_prop_subst : forall VC HC P P' x y,
      check_prop VC HC P P' ->
      List.In y HC ->
      check_prop VC HC (prop_subst x (HVar y) P) (prop_subst x (HVar y) P').
Admitted.


(***************)
(* Define Bind *)
(***************)

Definition Bind x A M E := LetDia x 
                                (Cast (Dia (IntroTerm M))
                                      (Computation Top x A (And (HId init mem) (Id A (Var x) M))))
                                E.

Lemma bind_typing : forall VC P Q x M m n E y B M' E' O,
  wf_var_context VC ->
  check_type VC B B ->
  check_prop VC init_mem_context P P ->
  check_intro_term VC M (By m n) M' ->
  ~ in_var_context x VC ->
  aux_reduce (By m n) (Dia M') x E' O ->
  infer_postcondition ((x,By m n)::VC) (And P (Id (By m n) (Var x) M')) 
                      E y B Q E' ->
  infer_postcondition VC P (Bind x (By m n) M E) y B 
                      (Exists x (By m n) Q) O.
Proof.
  intros until O; intros wfVC checkB checkP checkM nin_x_VC inferE redO.
  set (R2 := And (HId init mem) (Id (By m n) (Var x) M')).
  assert (wfHId : forall VC, 
          wf_var_context VC ->
          check_prop VC init_mem_context (HId init mem) (HId init mem)).
    intros. step; step; simpl; auto.
  assert (wfId : check_prop ((x,By m n)::VC) init_mem_context
                 (Id (By m n) (Var x) M') (Id (By m n) (Var x) M')).
    step.
    ciVar x (By m n) (InHead x (By m n) VC); simpl; auto.
      destruct (var_dec x x); auto. absurd (x <> x); auto.
    apply check_intro_term_canon with M; auto.
    apply check_intro_term_VC_weakening; auto.
  assert (wfR2 : wf_prop_context ((x,By m n)::VC) init_mem_context R2).
    step. step.
  assert (check_prop_P : check_prop ((x, By m n)::VC) init_mem_context
                         P P).
    apply check_prop_VC_weakening; auto.
  assert (mid_not_init_mem : ~ List.In "mid" init_mem_context).
    destruct 1 as [H | [H | H]]; inversion H.
  assert (check_prop_P' : check_prop ((x, By m n)::VC) ("mid"::init_mem_context) 
                         P P).
    apply check_prop_HC_weakening; auto. 

  apply ipLetDia with 
    (N' := Dia M')
    (E' := E') (z := "mid") (R1 := Top) (R2 := R2); auto.
  (*check_prop Q Q*) 
    apply infer_postcondition_canon with (P := And P (Id (By m n) (Var x) M'))
      (E := E) (y := y) (B := B) (E' := E'); auto.
  (*infer_elim_term*) 
    apply ieCast; auto.
    (*check_type*) step. step. step.
      ciVar x (By m n) (InHead x (By m n) VC); simpl; auto.
        destruct (var_dec x x); auto. absurd (x <> x); auto.
      apply check_intro_term_VC_weakening; auto.
    (*check_intro_term Dia M*) step. 
      apply cpConsequent with 
            (And (And (HId init mem) Top) (Id (By m n) (Var x) M')); auto.
      (*check_prop*) step. 
      (*infer_postcondition*) step.
    (*sequent*) apply sAnd1; auto. 
      apply sAnd1; auto. 
      apply sAnd2; auto. 
      (*wf_prop_context*) step.
      apply sEq; auto. 
      apply sWeak1; auto.
  (*sequent*) apply sTop; auto. step.
  (*infer*) apply ipStrengthenPre with (And P (Id (By m n) (Var x) M')); auto.
    apply sExistsHeapElim; auto. 
      step. 
    apply sAnd1; auto. 
      step. apply check_prop_HC_weakening; auto.
    simpl.
    assert (List.In "mid" ("mid"::init_mem_context)). simpl; auto.
    apply sAnd2; auto.
      step. step. step. step; step; simpl; auto.
      apply check_prop_HC_weakening; auto.
      apply check_prop_subst; auto.
    (*P*) apply sSwap1.
      apply sAnd1; auto. 
        step. apply check_prop_subst; auto. 
      apply sHIdSubst1 with (h := "mem") (q := P) 
                            (q1' := prop_subst "mem" (HVar "mid") P);
        auto. step. step. apply check_prop_subst; auto. 
          apply check_prop_HC_weakening; auto.
          rewrite prop_subst_id; auto.
      apply sWeak1; auto. 
        step. step. apply check_prop_subst; auto. 
        apply check_prop_HC_weakening; auto.
        step. apply check_prop_subst; auto. 
      apply sWeak1; auto.
        step. apply check_prop_subst; auto. 
        step. apply check_prop_subst; auto.
    (*x = M'*) apply sWeak1; auto. 
        step. step. step; step; simpl; auto.
        apply check_prop_HC_weakening; auto.
        step. apply check_prop_HC_weakening; auto.
      apply sAnd1; auto. 
        step; apply check_prop_HC_weakening; auto.
      apply sWeak1; auto. 
        step; apply check_prop_HC_weakening; auto.
        step; apply check_prop_HC_weakening; auto.
Qed.