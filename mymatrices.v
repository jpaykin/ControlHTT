Require Import matrices Bool Reals Program.Equality.
Set Implicit Arguments.

(* In the matrices library, matrices are defined with respect
   to a carrier ring. We want two types of matrices--numeric 
   and logical. *)

(* Numeric Carrier : R *)

Module Rc <: Carrier.
  Definition A := R.
  Definition Aopp := Ropp.
  Definition Aplus := Rplus.
  Definition Aminus := Rminus.
  Definition Amult := Rmult.
  Definition A0 := 0%R.
  Definition A1 := 1%R.
  Definition A_ring : ring_theory A0 A1 Aplus Amult Aminus Aopp (eq(A:=R)).
    split; auto with real.
    intros. rewrite Rmult_comm.
    rewrite Rmult_plus_distr_l.
    rewrite (Rmult_comm z x).
    rewrite (Rmult_comm z y).
    auto.
  Defined.
End Rc.

Lemma R_eq_dec : forall r1 r2 : R, {r1 = r2} + {r1 <> r2}.
  intros. 
  destruct (Rlt_le_dec r1 r2).
  right; apply Rlt_not_eq; auto.
  destruct (Rle_lt_or_eq_dec r2 r1 r).
  right; apply Rgt_not_eq; auto.
  left; auto.
Qed.
  

(* Numeric Carrier : Z *)
Module Zc <: Carrier.
  Definition A := Z.
  Definition Aopp := Zopp.
  Definition Aplus := Zplus.
  Definition Aminus := Zminus.
  Definition Amult := Zmult.
  Definition A0 := 0%Z.
  Definition A1 := 1%Z.
  Definition A_ring := InitialRing.Zth.
End Zc.

(* Logical Carrier : bool *)
(* Important : ring operations on bool are not
   the same as boolean operations.
   For example, plus = xor (not or);
   opp = id (not neg) *)
Module Bc <: Carrier.
  Definition A := bool.
  Definition Aplus := xorb.
  Definition Amult := andb.
  Definition A0 := false.
  Definition A1 := true.
  Definition Aopp (b:bool) := b.
  Definition Aminus (b1 b2 : bool) : bool := Aplus b1 (Aopp b2).
  Definition A_ring : ring_theory A0 A1 Aplus Amult Aminus Aopp (eq(A:=A)).
    split;
    try (destruct x; auto; 
      try (destruct y; auto;
        try (destruct z; auto)); fail).
  Defined.
End Bc.

Module numVect := Vectors Rc.
Module numMatrices := Matrices Rc.
Module logVect := Vectors Bc.
Module logMatrices := Matrices Bc.

Definition numMatrix : nat -> nat -> Set := fun m n => numMatrices.Lmatrix n m.
Definition logMatrix : nat -> nat -> Set := fun m n => logMatrices.Lmatrix n m.

(* Equality *)

Section vect_dec.
  Variable A : Set.
  Hypothesis A_dec : forall (a b : A), {a = b} + {a <> b}.
  
  Definition vect_dec : forall n (U V : vect A n), {U = V} + {U <> V}.
    intros n U.
    induction U; dependent induction V; auto.
    destruct (A_dec a a0), (IHU V).
      rewrite e, e0; left; auto.
      right. subst. intro H. dependent destruction H. absurd (V <> V); auto.
      right. inversion 1; contradiction.
      right. inversion 1; contradiction.
  Defined.
End vect_dec.

Definition numMatrix_dec : forall m n (A B : numMatrix m n), {A=B} + {A<>B}.
  unfold numMatrix, numMatrices.Lmatrix.
  assert (H : forall p (U V : vect R p), {U=V} + {U<>V}).
    apply (vect_dec R_eq_dec).
  intros.
  destruct (vect_dec (H n) A B); auto.
Defined.

Definition logMatrix_dec : forall m n (A B : logMatrix m n), {A=B} + {A<>B}.
  assert (H : forall p (U V : vect bool p), {U=V} + {U<>V}).
    apply (vect_dec bool_dec).
  intros.
  destruct (vect_dec (H n) A B); auto.
Defined.

(* Set implicit arguments and notations on vectors *)
Implicit Arguments vnil [A]. 
Implicit Arguments vcons [A n].

Notation "[ ]" := vnil.
Notation "[ x , .. , y ]" := (vcons x .. (vcons y vnil) ..).
Notation "[ v1 ; .. ; vn ]" := (vcons v1 .. (vcons vn vnil) ..).

(* Numerical Operations *)
Definition numPlus : forall n m (M1 M2 : numMatrix m n), numMatrix m n :=
  numMatrices.addmatrix.
Definition maybeNumPlus : forall m n (M1 : numMatrix m n) m' n' (M2 : numMatrix m' n'), option (numMatrix m n).
  intros.
  destruct (eq_nat_dec m m'); [idtac | apply None].
  destruct (eq_nat_dec n n'); [idtac | apply None].
  rewrite e, e0 in *; clear e e0. exact (Some (numPlus M1 M2)).
Defined.

Definition numMinus m n (M1 M2 : numMatrix m n) : numMatrix m n :=
  numMatrices.addmatrix _ _ M1 (numMatrices.oppmatrix _ _ M2).
Definition maybeNumMinus : forall m n (M1 : numMatrix m n) m' n' (M2 : numMatrix m' n'), option (numMatrix m n).
  intros.
  destruct (eq_nat_dec m m'); [idtac | apply None].
  destruct (eq_nat_dec n n'); [idtac | apply None].
  rewrite e, e0 in *; clear e e0. exact (Some (numMinus M1 M2)).
Defined.

Definition numNeg m n (M : numMatrix m n) : numMatrix m n :=
  numMatrices.oppmatrix _ _ M.

(* element-wise multiplication *)
Fixpoint numVectTimes n (V : vect R n) : vect R n -> vect R n.
  destruct V.
  (*nil*) refine (fun _ => []).
  (*z::V*) intros V'. dependent destruction V'.
    refine (vcons (Rmult r r0) (numVectTimes _ V V')).
Defined.

Fixpoint numTimes m n (M1 : numMatrix m n) : numMatrix m n -> numMatrix m n.
  destruct M1.
  (*nil*) refine (fun _ => []).
  (*v::M1*) intros M2. dependent destruction M2.
    refine (vcons (numVectTimes v v0) (numTimes _ _ M1 M2)).
Defined.

Definition maybeNumTimes : forall m n (M1 : numMatrix m n) m' n' (M2 : numMatrix m' n'), option (numMatrix m n).
  intros.
  destruct (eq_nat_dec m m'); [idtac | apply None].
  destruct (eq_nat_dec n n'); [idtac | apply None].
  rewrite e, e0 in *; clear e e0. exact (Some (numTimes M1 M2)).
Defined.

(* element-wise division *)
Fixpoint numVectDiv n (V : vect R n) : vect R n -> vect R n.
  destruct V.
  (*nil*) refine (fun _ => []).
  (*z::V*) intros V'. dependent destruction V'.
    refine (vcons (Rdiv r r0) (numVectDiv _ V V')).
Defined.

Fixpoint numDiv m n (M1 : numMatrix m n) : numMatrix m n -> numMatrix m n.
  destruct M1.
  (*nil*) refine (fun _ => []).
  (*v::M1*) intros M2. dependent destruction M2.
    refine (vcons (numVectDiv v v0) (numDiv _ _ M1 M2)).
Defined.

Definition maybeNumDiv : forall m n (M1 : numMatrix m n) m' n' (M2 : numMatrix m' n'), option (numMatrix m n).
  intros.
  destruct (eq_nat_dec m m'); [idtac | apply None].
  destruct (eq_nat_dec n n'); [idtac | apply None].
  rewrite e, e0 in *; clear e e0. exact (Some (numDiv M1 M2)).
Defined.

(*element_wise minimum*)
Fixpoint numVectMin n (V : vect R n) : vect R n -> vect R n.
  destruct V.
  (*nil*) refine (fun _ => []).
  (*z::V*) intros V'. dependent destruction V'.
    refine (vcons (Rmin r r0) (numVectMin _ V V')).
Defined.

Fixpoint numMin m n (M1 : numMatrix m n) : numMatrix m n -> numMatrix m n.
  destruct M1.
  (*nil*) refine (fun _ => []).
  (*v::M1*) intros M2. dependent destruction M2.
    refine (vcons (numVectMin v v0) (numMin _ _ M1 M2)).
Defined.

Definition maybeNumMin : forall m n (M1 : numMatrix m n) m' n' (M2 : numMatrix m' n'), option (numMatrix m n).
  intros.
  destruct (eq_nat_dec m m'); [idtac | apply None].
  destruct (eq_nat_dec n n'); [idtac | apply None].
  rewrite e, e0 in *; clear e e0. exact (Some (numMin M1 M2)).
Defined.

(*element_wise maximum*)
Fixpoint numVectMax n (V : vect R n) : vect R n -> vect R n.
  destruct V.
  (*nil*) refine (fun _ => []).
  (*z::V*) intros V'. dependent destruction V'.
    refine (vcons (Rmax r r0) (numVectMax _ V V')).
Defined.

Fixpoint numMax m n (M1 : numMatrix m n) : numMatrix m n -> numMatrix m n.
  destruct M1.
  (*nil*) refine (fun _ => []).
  (*v::M1*) intros M2. dependent destruction M2.
    refine (vcons (numVectMax v v0) (numMax _ _ M1 M2)).
Defined.

Definition maybeNumMax : forall m n (M1 : numMatrix m n) m' n' (M2 : numMatrix m' n'), option (numMatrix m n).
  intros.
  destruct (eq_nat_dec m m'); [idtac | apply None].
  destruct (eq_nat_dec n n'); [idtac | apply None].
  rewrite e, e0 in *; clear e e0. exact (Some (numMax M1 M2)).
Defined.


(* Matrix Multiplication *)
Definition numProd : 
  forall m n p (M1 : numMatrix m n) (M2 : numMatrix n p), numMatrix m p :=
  fun _ _ _ M1 M2 => numMatrices.prodmat _ _ _ M1 M2.
Definition logProd :
  forall m n p (M1 : logMatrix m n) (M2 : logMatrix n p), logMatrix m p :=
  fun _ _ _ M1 M2 => logMatrices.prodmat _ _ _ M1 M2.

Definition maybeNumProd m n n' p (M1 : numMatrix m n) (M2 : numMatrix n' p) : option (numMatrix m p).
  destruct (eq_nat_dec n n').
  (*n=n'*) rewrite <- e in *; clear e. exact (Some (numProd M1 M2)).
  (*n<>n'*) exact None.
Defined.
Definition maybeLogProd m n n' p (M1 : logMatrix m n) (M2 : logMatrix n' p) : option (logMatrix m p).
  destruct (eq_nat_dec n n').
  (*n=n'*) rewrite <- e in *; clear e. exact (Some (logProd M1 M2)).
  (*n<>n'*) exact None.
Defined.

(* Transpose *)
Fixpoint joinRow A m n (v : vect A n) (M : vect (vect A m) n) 
         : vect (vect A (S m)) n.
  refine (
    match v in vect _ n 
      return vect (vect A m) n -> vect (vect A (S m)) n 
    with
    | vnil => fun M' =>
      match M' with
      | vnil => vnil
      | vcons _ _ _  => _
      end
    | vcons _ a v' => fun M' => _
    end M).
    unfold ID; auto.
    inversion M'; clear n1 H; rename H0 into v'', H1 into M''.
    exact (vcons (vcons a v'') (joinRow _ _ _ v' M'')).
Defined.

Fixpoint consNil A m : vect (vect A 0) m :=
  match m with
  | 0 => vnil
  | S m => vcons vnil (consNil _ m)
  end.

Fixpoint transpose A m n (M : vect (vect A m) n) : vect (vect A n) m :=
  match M in vect _ n return vect (vect A n) m 
  with
  | vnil => consNil A m 
  | vcons _ v M => joinRow v (transpose M)
  end.

(* Logical Matrix Operations *)
Fixpoint notVect n (v : vect bool n) : vect bool n :=
  match v with
  | vnil => vnil
  | vcons _ b v => vcons (negb b) (notVect v)
  end.
Fixpoint notMatrix m n (M : logMatrix m n) : logMatrix m n :=
  match M with
  | vnil => vnil
  | vcons _ v M => vcons (notVect v) (notMatrix M)
  end.

Fixpoint andVect n (v1 : vect bool n) : vect bool n -> vect bool n.
  refine (
    match v1 in vect _ n return vect _ n -> vect _ n 
    with
    | vnil => fun _ => vnil
    | vcons _ b v => fun v2 => _
    end).
  inversion v2; clear n1 H; rename H0 into b', H1 into v'.
  exact (vcons (andb b b') (andVect _ v v')).
Defined.
Fixpoint andMatrix m n (M1 : logMatrix m n) : logMatrix m n -> logMatrix m n.
  refine (
    match M1 with
    | vnil => fun _ => vnil
    | vcons _ v1 M1' => fun M2 => _
    end).
  inversion M2; clear n1 H; rename H0 into v2, H1 into M2'.
  exact (vcons (andVect v1 v2) (andMatrix _ _ M1' M2')).
Defined.

Definition maybeAndMatrix : forall m n (L1 : logMatrix m n) m' n' (L2 : logMatrix m' n'), option (logMatrix m n).
  intros.
  destruct (eq_nat_dec m m'); [idtac | apply None].
  destruct (eq_nat_dec n n'); [idtac | apply None].
  rewrite e, e0 in *; clear e e0. exact (Some (andMatrix L1 L2)).
Defined.

Fixpoint orVect n (v1 : vect bool n) : vect bool n -> vect bool n.
  refine (
    match v1 in vect _ n return vect _ n -> vect _ n 
    with
    | vnil => fun _ => vnil
    | vcons _ b v => fun v2 => _
    end).
  inversion v2; clear n1 H; rename H0 into b', H1 into v'.
  exact (vcons (orb b b') (orVect _ v v')).
Defined.
Fixpoint orMatrix m n (M1 : logMatrix m n) : logMatrix m n -> logMatrix m n.
  refine (
    match M1 with
    | vnil => fun _ => vnil
    | vcons _ v1 M1' => fun M2 => _
    end).
  inversion M2; clear n1 H; rename H0 into v2, H1 into M2'.
  exact (vcons (orVect v1 v2) (orMatrix _ _ M1' M2')).
Defined.

Definition maybeOrMatrix : forall m n (L1 : logMatrix m n) m' n' (L2 : logMatrix m' n'), option (logMatrix m n).
  intros.
  destruct (eq_nat_dec m m'); [idtac | apply None].
  destruct (eq_nat_dec n n'); [idtac | apply None].
  rewrite e, e0 in *; clear e e0. exact (Some (orMatrix L1 L2)).
Defined.

(* Selection *)
Definition select A m n (M : vect (vect A m) n) :
  forall i j, i < m -> j < n -> vect (vect A 1) 1.
  refine (fun i j _ _ =>
    [nth _ (S j) n (transpose ([nth _ (S i) m (transpose M) _ _])) _ _]);
  intuition.
Defined.

(*Binary pointwise equality*)

Fixpoint numVect_bEq m (A : vect R m) : vect R m -> vect bool m.
  destruct A.
  (*nil*) exact (fun _ => []).
  (*z::A*) intros B. dependent destruction B.
    refine (if R_eq_dec r r0 then vcons true (numVect_bEq _ A B)
    else vcons false (numVect_bEq _ A B)).
Defined.

Fixpoint numEq m n (A : numMatrix m n) : numMatrix m n -> logMatrix m n.
  destruct A.
  (*nil*) exact (fun _ => vnil).
  (*v::A*) intros B. dependent destruction B.
    refine (vcons (numVect_bEq v v0) (numEq _ _ A B)).
Defined.

Fixpoint allVect m (A : vect bool m) : bool :=
  match A with
  | vnil => true
  | vcons _ b B => andb b (allVect B)
  end.

Fixpoint all m n (A : logMatrix m n) : bool :=
  match A with
  | vnil => true
  | vcons _ v B => andb (allVect v) (all B)
  end.

Definition none m n (A : logMatrix m n) : bool :=
  negb (all A).

Definition numEqb m n (A B : numMatrix m n) : bool :=
  all (numEq A B).

Definition numNeq m n (A B : numMatrix m n) : logMatrix m n :=
  notMatrix (numEq A B).

Definition numNeqb m n (A B : numMatrix m n) : bool :=
  all (numNeq A B).

Definition maybe_numEq : forall m n (M1 : numMatrix m n) m' n' (M2 : numMatrix m' n'), option (logMatrix m n).
  intros.
  destruct (eq_nat_dec m m'); [idtac | apply None].
  destruct (eq_nat_dec n n'); [idtac | apply None].
  rewrite e, e0 in *; clear e e0. exact (Some (numEq M1 M2)).
Defined.

Definition maybe_numNeq : forall m n (M1 : numMatrix m n) m' n' (M2 : numMatrix m' n'), option (logMatrix m n).
  intros.
  destruct (eq_nat_dec m m'); [idtac | apply None].
  destruct (eq_nat_dec n n'); [idtac | apply None].
  rewrite e, e0 in *; clear e e0. exact (Some (numNeq M1 M2)).
Defined.

Definition maybe_numEqb : forall m n (M1 : numMatrix m n) m' n' (M2 : numMatrix m' n'), option bool.
  intros.
  destruct (eq_nat_dec m m'); [idtac | apply None].
  destruct (eq_nat_dec n n'); [idtac | apply None].
  rewrite e, e0 in *; clear e e0. exact (Some (numEqb M1 M2)).
Defined.

Definition maybe_numNeqb : forall m n (M1 : numMatrix m n) m' n' (M2 : numMatrix m' n'), option bool.
  intros.
  destruct (eq_nat_dec m m'); [idtac | apply None].
  destruct (eq_nat_dec n n'); [idtac | apply None].
  rewrite e, e0 in *; clear e e0. exact (Some (numNeqb M1 M2)).
Defined.

Fixpoint numVect_bLe m (A : vect R m) : vect R m -> vect bool m.
  destruct A.
  (*nil*) exact (fun _ => []).
  (*z::A*) intros B. dependent destruction B.
    refine (if Rle_dec r r0 then vcons true (numVect_bLe _ A B) else (vcons false (numVect_bLe _ A B))).
Defined.

Fixpoint numLe m n (M1 : numMatrix m n) : numMatrix m n -> logMatrix m n.
  destruct M1.
  (*nil*) exact (fun _ => []).
  (*v::M1*) intros M2. dependent destruction M2.
    refine (vcons (numVect_bLe v v0) (numLe _ _ M1 M2)).
Defined.

Definition maybe_numLe : forall m n (M1 : numMatrix m n) m' n' (M2 : numMatrix m' n'), option (logMatrix m n).
  intros.
  destruct (eq_nat_dec m m'); [idtac | apply None].
  destruct (eq_nat_dec n n'); [idtac | apply None].
  rewrite e, e0 in *; clear e e0. exact (Some (numLe M1 M2)).
Defined.

Definition numLeb m n (M1 M2 : numMatrix m n) : bool :=
  all (numLe M1 M2).

Definition maybe_numLeb : forall m n (M1 : numMatrix m n) m' n' (M2 : numMatrix m' n'), option bool.
  intros.
  destruct (eq_nat_dec m m'); [idtac | apply None].
  destruct (eq_nat_dec n n'); [idtac | apply None].
  rewrite e, e0 in *; clear e e0. exact (Some (numLeb M1 M2)).
Defined.