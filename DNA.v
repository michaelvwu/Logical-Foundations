(** 
Michael Wu mvw5mf
Austin Ly ahl5hm
Sonwoo Kim **)

From LF Require Import LF.Poly.

Inductive dnabase : Type :=
  |A : dnabase
  |C : dnabase
  |G : dnabase
  |T : dnabase.

Fixpoint eq_dnabase(x y : dnabase): bool :=
  match x,y with
  |A, A => true
  |C, C => true
  |G, G => true
  |T, T => true
  |A, C => false
  |C, G => false
  |G, T => false
  |T, A => false
  |A, G => false
  |C, T => false
  |G, A => false
  |T, C => false
  |A, T => false
  |C, A => false
  |G, C => false
  |T, G => false
  end. 
  
Fixpoint complement_dnabase (x : dnabase) : dnabase :=
  match x with
  |A => T
  |T => A
  |C => G
  |G => C
  end.


Example test_compl:
 forall x:dnabase, complement_dnabase (complement_dnabase x) = x.
 Proof.
  intros x. 
  destruct x. 
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
 Qed.

Definition dnastrand := list dnabase.

(*Fixpoint complement_dnastrand (s:dnastrand) : dnastrand :=
  match s with
  | nil => nil
  | cons b t => b :: complement_dnastrand(t)
  end.*)

Definition dnabasepair := list(prod dnabase dnabase). 

(*Fixpoint mk_dnabasepair (s:dnabase) : dnabasepair :=
  (s, (complement_dnabase s)).*)
 

Definition dnadoublehelix := list(prod dnabasepair dnabasepair).

Fixpoint ck_dnadoublehelix (b1:dnabasepair) : bool :=
  match b1 with
  |






