(* Copyright (c) 2006, 2011-2012, 2015, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Arith List Omega.

Require Import Cpdt.CpdtTactics Cpdt.Coinductive.

Require Extraction.

Set Implicit Arguments.
Set Asymmetric Patterns.
(* end hide *)

(** * Well-Founded Recursion *)

(** The essence of terminating recursion is that there are no infinite chains of nested recursive calls.  This intuition is commonly mapped to the mathematical idea of a%\index{well-founded relation}% _well-founded relation_, and the associated standard technique in Coq is%\index{well-founded recursion}% _well-founded recursion_.  The syntactic-subterm relation that Coq applies by default is well-founded, but many cases demand alternate well-founded relations.  To demonstrate, let us see where we get stuck on attempting a standard merge sort implementation. *)

Section mergeSort.
  Variable A : Type.
  Variable le : A -> A -> bool.

  (** We have a set equipped with some "less-than-or-equal-to" test. *)

  (** A standard function inserts an element into a sorted list, preserving sortedness. *)

  Fixpoint insert (x : A) (ls : list A) : list A :=
    match ls with
      | nil => x :: nil
      | h :: ls' =>
	if le x h
	  then x :: ls
	  else h :: insert x ls'
    end.

  (** We will also need a function to merge two sorted lists.  (We use a less efficient implementation than usual, because the more efficient implementation already forces us to think about well-founded recursion, while here we are only interested in setting up the example of merge sort.) *)

  Fixpoint merge (ls1 ls2 : list A) : list A :=
    match ls1 with
      | nil => ls2
      | h :: ls' => insert h (merge ls' ls2)
    end.

  (** The last helper function for classic merge sort is the one that follows, to split a list arbitrarily into two pieces of approximately equal length. *)

  Fixpoint split (ls : list A) : list A * list A :=
    match ls with
      | nil => (nil, nil)
      | h :: nil => (h :: nil, nil)
      | h1 :: h2 :: ls' =>
	let (ls1, ls2) := split ls' in
	  (h1 :: ls1, h2 :: ls2)
    end.

  (** Now, let us try to write the final sorting function, using a natural number "[<=]" test [leb] from the standard library.
[[
  Fixpoint mergeSort (ls : list A) : list A :=
    if leb (length ls) 1
      then ls
      else let lss := split ls in
	merge (mergeSort (fst lss)) (mergeSort (snd lss)).
]]
<<
Recursive call to mergeSort has principal argument equal to
"fst (split ls)" instead of a subterm of "ls".
>>
The definition is rejected for not following the simple primitive recursion criterion.  In particular, it is not apparent that recursive calls to [mergeSort] are syntactic subterms of the original argument [ls]; indeed, they are not, yet we know this is a well-founded recursive definition.
To produce an acceptable definition, we need to choose a well-founded relation and prove that [mergeSort] respects it.  A good starting point is an examination of how well-foundedness is formalized in the Coq standard library. *)

  Print well_founded.
  (** %\vspace{-.15in}% [[
well_founded = 
fun (A : Type) (R : A -> A -> Prop) => forall a : A, Acc R a
]]
The bulk of the definitional work devolves to the%\index{accessibility relation}\index{Gallina terms!Acc}% _accessibility_ relation [Acc], whose definition we may also examine. *)

(* begin hide *)
(* begin thide *)
Definition Acc_intro' := Acc_intro.
(* end thide *)
(* end hide *)

  Print Acc.
(** %\vspace{-.15in}% [[
Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
    Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x
]]
In prose, an element [x] is accessible for a relation [R] if every element "less than" [x] according to [R] is also accessible.  Since [Acc] is defined inductively, we know that any accessibility proof involves a finite chain of invocations, in a certain sense that we can make formal.  Building on Chapter 5's examples, let us define a co-inductive relation that is closer to the usual informal notion of "absence of infinite decreasing chains." *)

  CoInductive infiniteDecreasingChain A (R : A -> A -> Prop) : stream A -> Prop :=
  | ChainCons : forall x y s, infiniteDecreasingChain R (Cons y s)
    -> R y x
    -> infiniteDecreasingChain R (Cons x (Cons y s)).

(** We can now prove that any accessible element cannot be the beginning of any infinite decreasing chain. *)

(* begin thide *)
  Lemma noBadChains' : forall A (R : A -> A -> Prop) x, Acc R x
    -> forall s, ~infiniteDecreasingChain R (Cons x s).
    induction 1; crush;
      match goal with
        | [ H : infiniteDecreasingChain _ _ |- _ ] => inversion H; eauto
      end.
  Qed.

(** From here, the absence of infinite decreasing chains in well-founded sets is immediate. *)

  Theorem noBadChains : forall A (R : A -> A -> Prop), well_founded R
    -> forall s, ~infiniteDecreasingChain R s.
    destruct s; apply noBadChains'; auto.
  Qed.
(* end thide *)

(** Absence of infinite decreasing chains implies absence of infinitely nested recursive calls, for any recursive definition that respects the well-founded relation.  The [Fix] combinator from the standard library formalizes that intuition: *)

  Check Fix.
(** %\vspace{-.15in}%[[
Fix
     : forall (A : Type) (R : A -> A -> Prop),
       well_founded R ->
       forall P : A -> Type,
       (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
       forall x : A, P x
]]
A call to %\index{Gallina terms!Fix}%[Fix] must present a relation [R] and a proof of its well-foundedness.  The next argument, [P], is the possibly dependent range type of the function we build; the domain [A] of [R] is the function's domain.  The following argument has this type:
[[
       forall x : A, (forall y : A, R y x -> P y) -> P x
]]
This is an encoding of the function body.  The input [x] stands for the function argument, and the next input stands for the function we are defining.  Recursive calls are encoded as calls to the second argument, whose type tells us it expects a value [y] and a proof that [y] is "less than" [x], according to [R].  In this way, we enforce the well-foundedness restriction on recursive calls.
The rest of [Fix]'s type tells us that it returns a function of exactly the type we expect, so we are now ready to use it to implement [mergeSort].  Careful readers may have noticed that [Fix] has a dependent type of the sort we met in the previous chapter.
Before writing [mergeSort], we need to settle on a well-founded relation.  The right one for this example is based on lengths of lists. *)

  Definition lengthOrder (ls1 ls2 : list A) :=
    length ls1 < length ls2.

  (** We must prove that the relation is truly well-founded.  To save some space in the rest of this chapter, we skip right to nice, automated proof scripts, though we postpone introducing the principles behind such scripts to Part III of the book.  Curious readers may still replace semicolons with periods and newlines to step through these scripts interactively. *)

  Hint Constructors Acc.

  Lemma lengthOrder_wf' : forall len, forall ls, length ls <= len -> Acc lengthOrder ls.
    unfold lengthOrder; induction len; crush.
  Defined.

  Theorem lengthOrder_wf : well_founded lengthOrder.
    red; intro; eapply lengthOrder_wf'; eauto.
  Defined.

  (** Notice that we end these proofs with %\index{Vernacular commands!Defined}%[Defined], not [Qed].  Recall that [Defined] marks the theorems as %\emph{%#<i>#transparent#</i>#%}%, so that the details of their proofs may be used during program execution.  Why could such details possibly matter for computation?  It turns out that [Fix] satisfies the primitive recursion restriction by declaring itself as _recursive in the structure of [Acc] proofs_.  This is possible because [Acc] proofs follow a predictable inductive structure.  We must do work, as in the last theorem's proof, to establish that all elements of a type belong to [Acc], but the automatic unwinding of those proofs during recursion is straightforward.  If we ended the proof with [Qed], the proof details would be hidden from computation, in which case the unwinding process would get stuck.
     To justify our two recursive [mergeSort] calls, we will also need to prove that [split] respects the [lengthOrder] relation.  These proofs, too, must be kept transparent, to avoid stuckness of [Fix] evaluation.  We use the syntax [@foo] to reference identifier [foo] with its implicit argument behavior turned off.  (The proof details below use Ltac features not introduced yet, and they are safe to skip for now.) *)

  Lemma split_wf : forall len ls, 2 <= length ls <= len
    -> let (ls1, ls2) := split ls in
      lengthOrder ls1 ls /\ lengthOrder ls2 ls.
    unfold lengthOrder; induction len; crush; do 2 (destruct ls; crush);
      destruct (le_lt_dec 2 (length ls));
        repeat (match goal with
                  | [ _ : length ?E < 2 |- _ ] => destruct E
                  | [ _ : S (length ?E) < 2 |- _ ] => destruct E
                  | [ IH : _ |- context[split ?L] ] =>
                    specialize (IH L); destruct (split L); destruct IH
                end; crush).
  Defined.

  Ltac split_wf := intros ls ?; intros; generalize (@split_wf (length ls) ls);
    destruct (split ls); destruct 1; crush.

  Lemma split_wf1 : forall ls, 2 <= length ls
    -> lengthOrder (fst (split ls)) ls.
    split_wf.
  Defined.

  Lemma split_wf2 : forall ls, 2 <= length ls
    -> lengthOrder (snd (split ls)) ls.
    split_wf.
  Defined.

  Hint Resolve split_wf1 split_wf2.

  (** To write the function definition itself, we use the %\index{tactics!refine}%[refine] tactic as a convenient way to write a program that needs to manipulate proofs, without writing out those proofs manually.  We also use a replacement [le_lt_dec] for [leb] that has a more interesting dependent type.  (Note that we would not be able to complete the definition without this change, since [refine] will generate subgoals for the [if] branches based only on the _type_ of the test expression, not its _value_.) *)

  Definition mergeSort : list A -> list A.
(* begin thide *)
    refine (Fix lengthOrder_wf (fun _ => list A)
      (fun (ls : list A)
        (mergeSort : forall ls' : list A, lengthOrder ls' ls -> list A) =>
        if le_lt_dec 2 (length ls)
	  then let lss := split ls in
            merge (mergeSort (fst lss) _) (mergeSort (snd lss) _)
	  else ls)); subst lss; eauto.
  Defined.
(* end thide *)
End mergeSort.

(** The important thing is that it is now easy to evaluate calls to [mergeSort]. *)

Eval compute in mergeSort leb (1 :: 2 :: 36 :: 8 :: 19 :: nil).
(** [= 1 :: 2 :: 8 :: 19 :: 36 :: nil] *)

(** %\smallskip{}%Since the subject of this chapter is merely how to define functions with unusual recursion structure, we will not prove any further correctness theorems about [mergeSort]. Instead, we stop at proving that [mergeSort] has the expected computational behavior, for all inputs, not merely the one we just tested. *)

(* begin thide *)
Theorem mergeSort_eq : forall A (le : A -> A -> bool) ls,
  mergeSort le ls = if le_lt_dec 2 (length ls)
    then let lss := split ls in
      merge le (mergeSort le (fst lss)) (mergeSort le (snd lss))
    else ls.
  intros; apply (Fix_eq (@lengthOrder_wf A) (fun _ => list A)); intros.

  (** The library theorem [Fix_eq] imposes one more strange subgoal upon us.  We must prove that the function body is unable to distinguish between "self" arguments that map equal inputs to equal outputs.  One might think this should be true of any Gallina code, but in fact this general%\index{extensionality}% _function extensionality_ property is neither provable nor disprovable within Coq.  The type of [Fix_eq] makes clear what we must show manually: *)

  Check Fix_eq.
(** %\vspace{-.15in}%[[
Fix_eq
     : forall (A : Type) (R : A -> A -> Prop) (Rwf : well_founded R)
         (P : A -> Type)
         (F : forall x : A, (forall y : A, R y x -> P y) -> P x),
       (forall (x : A) (f g : forall y : A, R y x -> P y),
        (forall (y : A) (p : R y x), f y p = g y p) -> F x f = F x g) ->
       forall x : A,
       Fix Rwf P F x = F x (fun (y : A) (_ : R y x) => Fix Rwf P F y)
]]
  Most such obligations are dischargeable with straightforward proof automation, and this example is no exception. *)

  match goal with
    | [ |- context[match ?E with left _ => _ | right _ => _ end] ] => destruct E
  end; simpl; f_equal; auto.
Qed.
(* end thide *)

(** As a final test of our definition's suitability, we can extract to OCaml. *)

Extraction mergeSort.

(** <<
let rec mergeSort le x =
  match le_lt_dec (S (S O)) (length x) with
  | Left ->
    let lss = split x in
    merge le (mergeSort le (fst lss)) (mergeSort le (snd lss))
  | Right -> x
>>
  We see almost precisely the same definition we would have written manually in OCaml!  It might be a good exercise for the reader to use the commands we saw in the previous chapter to clean up some remaining differences from idiomatic OCaml.
  One more piece of the full picture is missing.  To go on and prove correctness of [mergeSort], we would need more than a way of unfolding its definition.  We also need an appropriate induction principle matched to the well-founded relation.  Such a principle is available in the standard library, though we will say no more about its details here. *)

Check well_founded_induction.
(** %\vspace{-.15in}%[[
well_founded_induction
     : forall (A : Type) (R : A -> A -> Prop),
       well_founded R ->
       forall P : A -> Set,
       (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
       forall a : A, P a
]]
  Some more recent Coq features provide more convenient syntax for defining recursive functions.  Interested readers can consult the Coq manual about the commands %\index{Function}%[Function] and %\index{Program Fixpoint}%[Program Fixpoint]. *)

