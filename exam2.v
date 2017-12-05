(* Exam 2 *)

(* 
Michael Wu
mvw5mf 
*)

(*** solutions that are partially worked out but incomplete are
encapsulated by the comment type*)

(*

#1A: A natural number, n > 1, is said to be "composite" if there
exists natural numbers, h and k, h > 1 /\ h < n, k > 1 /\ k < n, 
such that n is equal to h * k. First, specify the "composite" 
*property* of natural numbers in Coq. Your inductive family 
of propositions (that's a hint) will need one proof constructor. 
Call it [factors]. 
*)

(* Inductive factors : nat -> Prop :=
  | comp_h : forall n h h1 : nat, h > 1 /\ h < n -> h1 
  | comp_k : forall n k k1 : nat, k > 1 /\ k < n -> k1. *)


Inductive composite: nat -> Prop :=
  factors: forall n: nat, 
          n > 1 ->
          (exists h k: nat,
          h>1 /\ k>1 /\ n= h* k) ->
          composite n. 

(* #1B: Now write and then prove a theorem stating that 4 is composite. 
As a hint, recall that > is just a notation for a function.
*)

(* Theorem composite_4 : composite 4. 
Proof. 
  split. apply factors. apply factors. Qed. *)
  
Theorem composite_4 : composite 4.
apply factors. 
unfold gt. unfold lt. apply le_S. apply le_S. apply le_n.
exists 2. exists 2. split.

unfold gt. unfold lt. apply le_n. 
split. 
unfold gt. unfold lt. apply le_n.
reflexivity. 
Qed.



(*
#2: We formalize ordinary logical conjunction in Coq as a type,
constructor, [and], polymorphic in two ("smaller") propositions,
with a proof constructor, [conj], that when given a proof of [P]
and a proof of [Q] constructs and returns a proof of [and P Q] 

In some legal situations, one requires only a "preponderance"
of evidence to justify a conclusion. Your assignment here is to
define a new operator, we'll call it [prepand], that takes three
propositions, let's call them [P], [Q], and [R], that we will define 
to be true if one has proofs for at least two of the three given 
propositions. Write a Coq specification of [prepond]. Hint: You
can model your answer to some extend on the definition of the
[and] operator in the Curry-Howard Correspondence chapter of
the book.

Then write and prove the proposition, call it [notprep], stating 
that it is *not* the case that [prepand 0=1 true=false []=[1]] is 
true.
*)

(* You will need the following two lines to use the [] notation. *)
Require Import Coq.Lists.List.
Import ListNotations.

(* Inductive prepond (P Q R : Prop) : Prop :=
| prepand : P -> Q -> R -> prepand P Q R
| proof2 : Q -> R -> prepond Q R 
| proof3 : R -> P -> prepond R P.

Theorem notprep :  *)



(*
#3: In a precise but informal sentence, state what the axiom 
of "functional extensionality" asserts. Write your answer in 
terms of two functions, f and g, each from some type, A, to 
some type B. Write your answer within this comment block:

ANSWER:  forall (A B : Type) (f g : A -> B), (forall x : X, f x = g x) -> f = g 

Given functions f and g from A to B, if for every value , a, of type A, fa = g a then f =g. 
*)

(*
#4: In a precise but informal sentence, state what it 
means for a relation to be a function? You can write your answer
in terms of a function, f, from some type, A, to some type B. 

ANSWER: if for all a fo type A, f(a) = x and f(a) = y, then x = y. 
*)

(*
#5: In a precise but informal sentence, state what it
means a function to be injective. You can write your answer in
terms of a function, f, from some type, A, to some type B. 

ANSWER: {A B} (f : A → B) := forall x y : A, f x = f y → x = y.
*)

(*
#6: In precise informal language, what does the induction 
principle for the type, [list A], say? Keep your answer short.

ANSWER: 

 Inductive list (A:Type) : Type :=
        | nil : list A
        | cons : A → list A → list A.
        
Short Explanation says that: 
For all values x1...xn of types a1...an, 
if P holds for each of the inductive arguments (each xi of type t), 
then P holds for c x1 ... xn

For any propoerty P of values of type [list A] if the empty list has P, and 
if P is preserved by cons, then all lists have property P.
*)

(*
#7: Some languages allow you to assign values to more than
one variable at a time. Here you will build a little system that
will let you do this using total maps as a representation of a
simple "environment" (a mapping from variables to values).
*)


(*
Define a type, [var], with three constructors, [X, Y, Z]. 
These will be your "variables." 
*)

Inductive var : Type :=
| X : var
| Y : var
| Z : var.

(*
Define a function, [eq_var], that takes two variables and 
return [true] if they're the same and [false] otherwise.
*)

(* Definition eq_var a b := 
   match a,b with
    | X, Y => if [X Y] then true else false
   end. *)

(*
Define [env] to be the type, [var -> nat]. You will model a given
environment (mapping from variables to nat values) as a value
of this function type.
*)



(*
Define [init] to be the value of type [env] that maps every
variable to zero. Use [fun] notation.
*)

(*
Now define a function, [override2], that takes two variables,
two nats, and and environment (of type [env]) and that returns 
an environment  in which the given variables have the given 
values and no other changes occur. 
*)

(*
Assign to [nEnv] the result of overriding the [init] environment
with an assignment of 1 to X and 2 to Y.
*)

(*
Finally prove that the result is correct by uncommenting and 
proving this test case.

Example or2Works: nEnv X = 1 /\ nEnv Y = 2 /\ nEnv Z = 0.
*)

(*
EXTRA CREDIT BELOW!
*)

(*
#EC_A: Define the syntax of a simple expression language
as an inductive data type, [sExp]. The language has just 
two expressions: "Const n", where n is a nat, and "Square s", 
where s is an sExp.
*)

Inductive sExp : Type :=
  | sNum : nat -> sExp
  | sSquare : sExp -> sExp.

(*
#EC_B: Define an operational semantics, [sEval], for [sExp], as 
follows. An [sExp] evaluates to a [nat]  as follows. [Const n] 
evalautes to [n], and [Square s] evaluates to the square of the 
value of [s].
*)

(*
#EC_C: Prove a theorem called [itworks] asserting that the 
expression in which Square is applied twice to Const 3 
equals 81.
*)

(*
#EC_D: Write a semantics, call it [sEvalR], for [sExp] as a 
relation and prove the same test case (call it [itworksR]), but 
using the inference rules of  your semantics. Hint: Assert a 
little lemma that will let you rewrite 81 into the form required 
to unify. 
*)