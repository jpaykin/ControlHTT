Require Import String List Program.Equality.
Require Import syntax.
Set Implicit Arguments.

Definition heap_context := list heap_var.
Definition prop_context := list proposition.

Definition var_binding := (var * type)%type.
Definition var_context := list var_binding.

Inductive in_var_context : var -> var_context -> Prop :=
| InHead : forall x A D, in_var_context x ((x,A)::D)
| InTail : forall x y A D, in_var_context x D -> in_var_context x ((y,A)::D).

Fixpoint delete x D : var_context :=
  match D with
  | nil => nil
  | (y,A)::D' => let D'' := delete x D' in if var_dec x y then D'' else (y,A)::D''
  end.

Lemma nin_nil : forall x, ~ in_var_context x nil.
Proof.
  intros; inversion 1.
Qed.
Lemma neq_in : forall x y A D, x <> y -> in_var_context x ((y,A)::D) -> in_var_context x D.
  intros; inversion H0; try contradiction; auto.
Qed.

Definition in_context_dec : forall x D, {in_var_context x D} + {~ in_var_context x D}.
  refine (fix var_in_dec x D :=
  match D as D0 return {in_var_context x D0} + {~ in_var_context x D0} with
  | nil => right _
  | (y,A)::D' => if var_dec x y then left _ else 
    if var_in_dec x D' then left _ else right _
  end).
  inversion 1.
  destruct _H; apply InHead.
  apply InTail; auto.
  intro H. inversion H; contradiction.
Defined.

Definition get : forall x D, in_var_context x D -> type.
  refine (fix get x D :=
  match D as D0 return in_var_context x D0 -> type with
  | nil => fun pf => match nin_nil pf with end
  | (y,A)::D' => if var_dec x y then fun _ => A else fun _ => get x D' _
  end).
  apply neq_in with y A; auto.
Defined.
Implicit Arguments get [].

Fixpoint get_dec (x:var) (D : var_context) : option type := 
  match D with
  | nil => None
  | (y,A)::D' => if string_dec x y then Some A else get_dec x D'
  end.

Lemma get_pf_irrelevance : forall x D (pf1 pf2 : in_var_context x D), get x D pf1 = get x D pf2.
Proof.
  induction D; intros; simpl.
    destruct (nin_nil pf1).
  destruct a as [y A].
  destruct (var_dec x y); auto.
Qed.

Lemma get_neq : forall x y A D pf pf',
                x <> y -> get x D pf = get x ((y,A)::D) pf'.
  intros. rewrite get_pf_irrelevance with _ _ _ (InTail y A pf).
  revert pf pf' H.
  induction D as [ | [z B]]; intros; simpl; auto.
  (*nil*) destruct (var_dec x y); auto. absurd (x=y); auto.
    destruct (nin_nil pf).
  (*cons*) simpl; destruct (var_dec x z); destruct (var_dec x y); auto;
    try (absurd (x=y); auto; fail).
    rewrite IHD; auto. simpl.
    destruct (var_dec x y); auto; try (absurd (x=y); auto; fail).
    apply get_pf_irrelevance.
    constructor; auto.
    inversion pf; auto.
    absurd (x=z); auto.
Qed.  
Hint Resolve get_neq.
    
Definition domain_subset VC1 VC2 : Prop :=
  forall x, in_var_context x VC1 -> in_var_context x VC2.
Definition domain_equiv VC1 VC2 : Prop :=
  forall x, in_var_context x VC1 <-> in_var_context x VC2.
Definition vals_equiv VC1 VC2 : Prop :=
  forall x pf1 pf2, get x VC1 pf1 = get x VC2 pf2.
Definition var_context_subset VC1 VC2 : Prop :=
  domain_subset VC1 VC2 /\ vals_equiv VC1 VC2.
Definition var_context_equiv VC1 VC2 : Prop :=
  domain_equiv VC1 VC2 /\ vals_equiv VC1 VC2.

Lemma equiv_nil_nil : forall VC, var_context_equiv VC nil ->
                      VC = nil.
Proof.
  destruct VC as [ | (x,A) VC]; intros; auto.
  absurd (in_var_context x nil).
    inversion 1.
    destruct H as [H H']. apply H. apply InHead.
Qed.

Lemma equiv_refl : forall VC, var_context_equiv VC VC.
Proof.
  split.
  (*domain_equiv*) split; auto.
  (*vals_equiv*) intros x pf1 pf2; apply get_pf_irrelevance.
Qed.

Lemma equiv_symm : forall VC1 VC2, 
      var_context_equiv VC1 VC2 ->
      var_context_equiv VC2 VC1.
Proof.
  destruct 1.
  split; auto.
  (*domain_equiv*) split; apply H.
  (*vals_equiv*) intros x pf1 pf2. rewrite H0 with _ _ pf1; auto.
Qed.

Lemma equiv_trans : forall VC1 VC2 VC3,
      var_context_equiv VC1 VC2 ->
      var_context_equiv VC2 VC3 ->
      var_context_equiv VC1 VC3.
Proof.  
  do 2 destruct 1. split.
  (*domain_equiv*) split; intros. apply H1; apply H; auto.
    apply H; apply H1; auto.
  (*vals_equiv*) intros x pf1 pf3.
    assert (pf2 : in_var_context x VC2).
      apply H; auto.
    rewrite H0 with _ _ pf2. apply H2.
Qed.


Lemma equiv_cons : forall VC1 VC2 x A,
      var_context_equiv VC1 VC2 ->
      var_context_equiv ((x,A)::VC1) ((x,A)::VC2).
Proof.
  destruct 1; split.
  (*domain_equiv*) intro z; split; intros.
    (*->*) destruct (var_dec x z); [
      (*x=z*) rewrite e in *; clear x e; apply InHead |
      (*x<>z*) apply InTail; inversion H1; auto;
        [ absurd (x=z); auto | apply H; auto ] ].
    (*<-*) destruct (var_dec x z); [
      (*x=z*) rewrite e in *; clear x e; apply InHead |
      (*x<>z*) apply InTail; inversion H1; auto;
        [ absurd (x=z); auto | apply H; auto ] ].
  (*vals_equiv*) intros z pf1 pf2; simpl.
    destruct (var_dec z x); auto.
Qed.
Hint Resolve equiv_cons.

