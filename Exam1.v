(*
Save this file in your "lf" directory. In a terminal window,
compile it using the command "coqc -R . LF Exam1.v".
If this step fails, you have a configuration problem that
needs to be fixed before you can proceed. Talk to your
instructor if necessary to get it resolved.

Next, shut down your Coq IDE if it's open. Then open
this file in the IDE. This step should not pose problems.

Third, make sure that you can process the following
line of code, [From LF Require Export Poly.]. If you
have problems here, then you have a configuration
problem that needs to be fixed before you can proceed.

If you have no configuration problems, then proceed
with the exam. Just follow the instructions that are
embedded in the code.

If you do have a configuration problem, you should
first (1) exit from your IDE. (2) run "make clean" in
the "lf" directory in a terminal window; if you are not
able to do this, then you have not properly installed
make. (3) Run "make" in your terminal window. (4)
Recompile Exam1.v using "coqc -R . LF Exam1.v".
(5) Reopen your IDE, open Exam1.v, and try again.
If you get to this point and don't know what to do, you
should contact your instructor.
*)

From LF Require Export Tactics.

(**********************************************************)

(* 
Problem #1: Enumerated types. A [Bit] abstract data
type.
*)

(*
1A. Define a datatype called [Bit] with two values, 
called [zerob] and [oneb]. 
*)

Inductive Bit : Type :=
  |zerob : Bit
  |oneb : Bit.

(*
1B. Define a function called [compb] 
of type [Bit -> Bit], that when given a [Bit], returns its
complement. That is, when given the value, [oneb],
it returns [zerob], and when given [zerob] it returns
[oneb].
*)

Definition compb (b:Bit) : Bit :=
  match b with
  | zerob => oneb
  | oneb => zerob
  end.

(*
1C. Write and prove two "test cases", [compb_test1]
and [compb_test2], using [Example], sufficient to show
that your [compb] function is correct. Remember that
exhaustive testing is tantamount to a proof.
*)

Example compb_test1: (compb zerob) = oneb.
Proof. simpl. reflexivity. Qed.


Example compb_test2: (compb oneb) = zerob.
Proof. simpl. reflexivity. Qed.


(*
1D. Define and prove a theorem, [compb_involutive],
stating that for all values, [b], of type [Bit], 
[compb (compb b) = b].
*)

Theorem compb_involutive : forall b : Bit, 
  compb (compb b) = b.
  
Proof.
  intros b. destruct b.
    simpl. reflexivity.
    simpl. reflexivity.
    Qed.



(*
1E. Define a binary function [bitEq] that takes two 
[Bit] values and that returns [true] if and only if the
two values are the same.
*)
Definition bitEq (b1:Bit) (b2:Bit) : bool :=
  match b1, b2 with
  | oneb, oneb => true
  | zerob, zerob => true
  | _, _ => false
  end.
  


(*
1F. Define a binary function [bitAnd] that takes two 
[Bit] values and returns a [Bit] value, where [bitAnd]
returns [oneb] if and only if both of its arguments are
[oneb]. Match on both argument bits and use pattern 
matching in the cases within your [match] statement
so as to implement the function in just two cases: one
where both arguments are [oneb] and one where this
is not the case.
*)

Definition bitAnd (b1:Bit) (b2:Bit) : Bit :=
  match b1, b2 with
  |oneb, oneb => oneb
  |_, _ => zerob
  end.




(*
1G. Define and prove a theorem [onebID] stating
that [oneb] is a left identity element for [bitAnd]. 
That is, for all [Bit] values, [b], [bitAnd oneb b = b].
*)


Theorem onebID : forall b : Bit,
  bitAnd oneb b = b. 
  
Proof. 
  intros b. destruct b.
    simpl. reflexivity.
    simpl. reflexivity.
    Qed.



(*
1H. Define and prove a theorem, [bitEqGood], 
stating that for all [Bit] values [b1] and [b2], if 
[bitEq b1 b2] returns true then [b1 = b2].
*)


Theorem bitEqGood : forall (b1 b2 : Bit),
  bitEq b1 b2 = true -> b1 = b2.
  

Proof.
  intros b1. induction b1.
    simpl. intros b2 eq. destruct b2.
      reflexivity.
      inversion eq.
      simpl.
    
    intros b2 eq.
    destruct b2.
      inversion eq.
      
      reflexivity.
      Qed.


(**********************************************************)

(* 
Problem #2: Polymorphic, recursive types. A 
polymorphic [Tree] abstract data type.
*)

(*
2A. A [Tree] of values of type [A] is either [emptyTree] 
or it's a [nodeTree] that has an associated "value" of 
type [A] and two "children" (subtrees), each itself
a tree of values of type [A]. Define a polymorphic 
[Tree] type accordingly.

Declare the argument [A] of the type constructor to 
be of type [Set] (meaning that values in trees will be 
limited to be computational values, not things such 
as proofs). Make the argument [A] explicit. Call the
constructors [emptyTree] and [nodeTree].
*)

Inductive Tree (A:Set) : Type :=
  |emptyTree : Tree A
  |nodeTree : A -> Tree A -> Tree A -> Tree A.




(* 2B. 
Use the Arguments directive in Coq
to declare the type parameters to emptyTree and
nodeTree to be implicit. (Hint: See how this was
done for List T.)
*)

Arguments emptyTree {A}.
Arguments nodeTree {A} _ _ _.


(* 
2C. Define [emptyNatTree] to be the empty tree
of natural numbers, using [@] to turn off implicit
parameters.
*)

Definition emptyNatTree := @emptyTree nat.



(*
2D. Use the available constructors to build a term,
called [aTree] representing this tree of nats:

                                       1
                                     /    \
                                   3      4
                                  /  \    /  \
                                 5   E   E   E
                                /  \
                              E    E

*)

Definition aTree := nodeTree 1
                    (nodeTree 3
                      (nodeTree 5
                        emptyTree
                        emptyTree)
                      emptyTree)
                    (nodeTree 4
                      emptyTree
                      emptyTree).



(*
2E. Write a (polymorphic) function (with implicit type
parameter A: Set) called [eqTree] that takes two trees 
and a Boolean bfunction for comparing elements for 
equality and that returns [true] if and only if the two 
trees are equal. Then prove the two test cases below.
*)


Fixpoint eqTree {A : Set} (t1 t2 : Tree A) (bf : A -> A -> bool) : bool :=
  match t1, t2 with
  | emptyTree, emptyTree => true
  | nodeTree n1 t11 t12, nodeTree n2 t21 t22 => (bf n1 n2) && (eqTree t11 t21 bf) && (eqTree t12 t22 bf)
  | _,_ => false
 end.



Example treeTest1: eqTree aTree aTree beq_nat = true.
Proof.
simpl. reflexivity.
Qed.

Example treeTest2: eqTree aTree emptyTree beq_nat = false.
Proof.
simpl. reflexivity.
Qed.

(*
2F. Write a function, [treeSize], (polymorphic in the 
implicit parameter, [A]) that takes a tree and returns 
 the number of nodes in the tree.  Prove the following
test case. We define the size of an empty tree to be
zero.
*)

Fixpoint treeSize {A:Set} (T : Tree A) : nat :=
  match T with 
  | emptyTree => 0
  | nodeTree n T1 T2 => S (treeSize T1 + treeSize T2)
  end.



Example treeSizeTest1: treeSize aTree = 4.
Proof.
simpl. reflexivity.
Qed.


(*
2G. Write a function, [treeHead], implicitly polymorphic
in [A] that takes an argument, [t: tree A], and returns the
value at the root of the tree, if there is one, as a [Some]
option, and that otherwise returns a [None] option. Then
write and prove tests called [headTest1] and [headTest2]
that assert, respectively, that treeHead applied to an
empty tree is [None] and that treeHead applied to 
[aTree] is [Some 1].
*)


Fixpoint treeHead {A:Set} (T : Tree A) : option A :=
  match T with
  | emptyTree => None
  | nodeTree n t1 t2 => Some n
  end.


(*tests for treeHead*)



(*
2H. Write a function called [treeMap], polymorphic in
implicit parameter [A], that takes a function, [f: A -> A], 
and a tree of A's, and and that returns the tree derived
from the given tree by applying [f] to each element in
the given tree. Then prove the test case below.
*)

Fixpoint treeMap {A:Set} (f: A->A) (T: Tree A) : Tree A :=
  match T with
  | emptyTree => T
  | nodeTree n t1 t2 => nodeTree(f n) (treeMap f t1) (treeMap f t2)
  end.



(* For use in the following test case *)
Definition bTree := nodeTree 2 
                                (nodeTree 4 
                                   (nodeTree 6 
                                      emptyTree 
                                      emptyTree) 
                                   emptyTree) 
                                (nodeTree 5 
                                   emptyTree 
                                   emptyTree).

Example treeMapGood: treeMap S aTree = bTree.
Proof. simpl. reflexivity. Qed.

Example treeMapGood2: 
                         treeMap S emptyTree = emptyTree.
Proof. simpl. reflexivity. Qed.

(*
2H. Prove the following theorem.
*)

Theorem sillyTrees: 
                  eqTree aTree bTree beq_nat = true -> 
                      forall n:nat, n = S n.

Proof. 
  intros. inversion H. Qed.


(**********************************************************)

(* Problem #3: Proof tactics and techniques. *) 


(* 3A Prove the following using backward reasoning. *)

Theorem t1: forall A B C: Prop, 
           (A -> B) -> (B -> C) -> (A -> C).

Proof.
  intros A B C eq1 eq2 H. 
  apply eq2. apply eq1. apply H. Qed.



(* 3B Now prove it using forward reasoning. *)

Theorem t1': forall A B C: Prop, 
           (A -> B) -> (B -> C) -> (A -> C).

Proof.
  intros A B C eq1 eq2 H. 
  apply eq1 in H. apply eq2 in H. apply H. Qed.



(* 3C. Prove the following without using [rewrite]. *)

Theorem t2: forall T: Type, forall v1 v2: T, 
                   v1 = v2 -> v2 = v1.

Proof.
  intros. symmetry. apply H.
  Qed.

(* 3D. Use [trans_eq] to prove this. *)

Theorem t3: forall T: Type, forall f: T -> T, 
                      forall v1 v2 v3: T, 
                         f v1 = v2 -> 
                         v2 = v3  -> 
                         f v1 = v3.
Proof.
  intros T v1 v2 v3 f.
  apply trans_eq. Qed.

(* 3D. Prove. *)

Theorem t4: forall x y: nat, forall p: nat * nat, 
  (3, 4) = (x, y) -> y = 4.

Proof.
  intros x y. symmetry. inversion H. reflexivity. Qed.


(* 3E. Prove. *)

Theorem t5: beq_nat 0 1 = true -> 0 = 1.

Proof.
  intros. inversion H. Qed.


(* 3F. Consider the following code *)

Definition pairAdd (p1 p2: nat * nat): nat * nat :=
  match p1, p2 with
    | (x1,y1), (x2, y2) => (x1+x2, y1+y2)
  end.

(* Now prove this test. *)

Example t6: forall p: nat * nat, p = (3,4) -> pairAdd p p = (6,8).

Proof.
  intros p h. induction p. rewrite h. reflexivity.
 Qed.

(* 3G. Prove the following. *)

Theorem t7: forall n1 n2: nat, S n1 = S n2 -> n1 = n2.

Proof. 
  intros n1 n2 H. inversion H. reflexivity. Qed.

(* 
3H. Prove the following (map_rev).
*)

(* need a lemma to help prove map_rev*)

Lemma map_assoc: forall (X Y: Type) (f : X-> Y) (l1 l2 : list X),
  map f (l1 ++l2 ) = (map f l1) ++ (map f l2).
  
Proof.
  intros X Y f l1 l2.
    induction l1. 
    simpl. reflexivity. 
    simpl. rewrite -> IHl1. reflexivity. Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).


Proof.
  intros. induction l. 
    simpl. reflexivity.
    simpl. rewrite ->map_assoc. rewrite ->IHl. 
    simpl. reflexivity. Qed.

(**** END OF EXAM GOOD JOB! ****)



