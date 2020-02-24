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

(* 
forall (A : Type) (R : A -> A -> Prop) (P : A -> Prop), 
(forall x : A, (forall y : A, R y x -> Acc R y) -> (forall y : A, R y x -> P y) -> P x) ->
(forall x : A, Acc R x -> P x)
 *)
  
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

(*  Fix_F =  *)
(* fun (A : Type) (R : A -> A -> Prop) (P : A -> Type) *)
(*   (F : forall x : A, (forall y : A, R y x -> P y) -> P x) => *)
(* fix Fix_F (x : A) (a : Acc R x) {struct a} : P x := *)
(*   F x (fun (y : A) (h : R y x) => Fix_F y (Acc_inv a h)) *)
(*      : forall (A : Type) (R : A -> A -> Prop) (P : A -> Type), *)
(*        (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall x : A, Acc R x -> P x *)
(* Fix_F P F (Rwf x) *)
  

  Definition lengthOrder (ls1 ls2 : list A) :=
    length ls1 < length ls2.

  (** We must prove that the relation is truly well-founded.  To save some space in the rest of this chapter, we skip right to nice, automated proof scripts, though we postpone introducing the principles behind such scripts to Part III of the book.  Curious readers may still replace semicolons with periods and newlines to step through these scripts interactively. *)

  Hint Constructors Acc.

  Lemma lengthOrder_wf' : forall len, forall ls, length ls <= len -> Acc lengthOrder ls.
    unfold lengthOrder; induction len; crush.
  Defined.

  Theorem lengthOrder_wf : well_founded lengthOrder.
    red. intro. eapply lengthOrder_wf'. eauto.
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
	else ls)).
    -
      subst lss. apply split_wf1. assumption.
    -
      subst lss. apply split_wf2. assumption.
  Defined.

  Definition mergeSort'_1 : list A -> list A.
    refine ( fun (ls : list A) =>
               Fix_F (fun _ => list A)
                     (fun (ls : list A)
                          (realRecur : forall ls' : list A, lengthOrder ls' ls -> list A) =>
                        if le_lt_dec 2 (length ls)                                     
                        then
                          let lss := split ls in
                          merge (realRecur (fst lss) _) (realRecur (snd lss) _)
                        else
                          ls) _
           ).
    -
      subst lss. apply split_wf1. assumption.
    -
      subst lss. apply split_wf2. assumption.
    -
      apply (lengthOrder_wf ls).
  Defined.

  Definition mergeSort'' : list A -> list A.
    refine (fun ls : list A =>
              (fix outer (ls : list A) (HAcc : Acc lengthOrder ls) : list A :=
                 (fun (ls : list A) (inner : forall ls', lengthOrder ls' ls -> list A) =>
                    if le_lt_dec 2 (length ls)
                    then
                      let lss := split ls in
                      merge (inner (fst lss) _) (inner (snd lss) _)
                    else
                      ls
                 )
                   ls
                   (fun (ls' : list A) (HR : lengthOrder ls' ls) => outer ls' (Acc_inv HAcc HR))
              ) ls _).
    -
      subst lss. apply split_wf1. assumption.
    -
      subst lss. apply split_wf2. assumption.
    -
      apply (lengthOrder_wf ls).
  Defined.

  (* Definition mergeSort''' : list A -> list A. *)
  (*   refine (fun ls : list A => *)
  (*             (fix outer (ls : list A) : list A := *)
  (*                (fun (ls : list A) (inner : list A -> list A) => *)
  (*                   if leb (length ls) 1 *)
  (*                   then ls *)
  (*                   else *)
  (*                     let lss := split ls in *)
  (*                     merge (inner (fst lss)) (inner (snd lss)) *)
  (*                ) *)
  (*                  ls *)
  (*                  (fun (ls' : list A) => outer ls')                                         *)
  (*             ) *)
  (*               ls).             *)
  
  Definition mergeSortManual1 : list A -> list A :=
    fun ls : list A =>
      (fix outer (ls0 : list A) (HAcc : Acc lengthOrder ls0) {struct HAcc} : 
         list A :=
         (fun (ls1 : list A) (inner : forall ls' : list A, lengthOrder ls' ls1 -> list A) =>
            match le_lt_dec 2 (length ls1) with
            | left x =>
              let lss := split ls1 in
              merge (inner (fst lss) (split_wf1 ls1 x)) (inner (snd lss) (split_wf2 ls1 x))
            | right _ => ls1
            end) ls0 (fun (ls' : list A) (HR : lengthOrder ls' ls0) => outer ls' (Acc_inv HAcc HR))) ls
                                                                                                     (lengthOrder_wf ls).

  (* Definition mergeSortManual2 : list A -> list A := *)
  (*   fun ls : list A => *)
  (*     (fix outer (ls0 : list A) : list A := *)
  (*        (fun (ls1 : list A) (inner : forall ls' : list A, list A) => *)
  (*           match leb (length ls1) 1 with *)
  (*           | false => *)
  (*             let lss := split ls1 in *)
  (*             merge (inner (fst lss)) (inner (snd lss)) *)
  (*           | true => ls1 *)
  (*           end) ls0 (fun (ls' : list A) => outer ls')) ls. *)

  
      
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

Definition Fix_F_manual : forall (A : Type) (R : A -> A -> Prop) (P : A -> Type),
    (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
    forall x : A, Acc R x -> P x :=
  fun (A : Type) (R : A -> A -> Prop) (P : A -> Type)
      (F : forall x : A, (forall y : A, R y x -> P y) -> P x) =>
    fix recur (x : A ) (a : Acc R x) {struct a} : P x :=
    F x (fun (y : A) (h : R y x) => recur y (Acc_inv a h)).

(* Definition Fix_F_manual' : forall (A : Type) (P : A -> Type), *)
(*     (forall x : A, (forall y : A, P y) -> P x) -> *)
(*     forall x : A, P x := *)
(*   fun (A : Type) (P : A -> Type) *)
(*       (F : forall x : A, (forall y : A, P y) -> P x) => *)
(*     fix recur (x : A) : P x := *)
(*     F x (fun (y : A) => recur y). *)

(* Definition Fix_F_manual'' : *)
(*     (forall x : list nat, (forall y : list nat,  list nat) -> list nat) -> *)
(*     forall x : list nat, list nat := *)
(*   fun  (F : forall x : list nat, (forall y : list nat, list nat) -> list nat) => *)
(*     fix recur (x : list nat) : list nat := *)
(*     F x (fun (y : list nat) => recur y). *)

(** * A Non-Termination Monad Inspired by Domain Theory *)

(** The key insights of %\index{domain theory}%domain theory%~\cite{WinskelDomains}% inspire the next approach to modeling non-termination.  Domain theory is based on _information orders_ that relate values representing computation results, according to how much information these values convey.  For instance, a simple domain might include values "the program does not terminate" and "the program terminates with the answer 5."  The former is considered to be an _approximation_ of the latter, while the latter is _not_ an approximation of "the program terminates with the answer 6."  The details of domain theory will not be important in what follows; we merely borrow the notion of an approximation ordering on computation results.
   Consider this definition of a type of computations. *)

Section computation.
  Variable A : Type.
  (** The type [A] describes the result a computation will yield, if it terminates.
     We give a rich dependent type to computations themselves: *)

  Definition computation :=
    {f : nat -> option A
      | forall (n : nat) (v : A),
	f n = Some v
	-> forall (n' : nat), n' >= n
	  -> f n' = Some v}.

  (** A computation is fundamentally a function [f] from an _approximation level_ [n] to an optional result.  Intuitively, higher [n] values enable termination in more cases than lower values.  A call to [f] may return [None] to indicate that [n] was not high enough to run the computation to completion; higher [n] values may yield [Some].  Further, the proof obligation within the subset type asserts that [f] is _monotone_ in an appropriate sense: when some [n] is sufficient to produce termination, so are all higher [n] values, and they all yield the same program result [v].
  It is easy to define a relation characterizing when a computation runs to a particular result at a particular approximation level. *)

  Definition runTo (m : computation) (n : nat) (v : A) :=
    proj1_sig m n = Some v.

  (** On top of [runTo], we also define [run], which is the most abstract notion of when a computation runs to a value. *)

  Definition run (m : computation) (v : A) :=
    exists n, runTo m n v.
End computation.

(** The book source code contains at this point some tactics, lemma proofs, and hint commands, to be used in proving facts about computations.  Since their details are orthogonal to the message of this chapter, I have omitted them in the rendered version. *)
(* begin hide *)

Hint Unfold runTo.

Ltac run' := unfold run, runTo in *; try red; crush;
  repeat (match goal with
            | [ _ : proj1_sig ?E _ = _ |- _ ] =>
              match goal with
                | [ x : _ |- _ ] =>
                  match x with
                    | E => destruct E
                  end
              end
            | [ |- context[match ?M with exist _ _ => _ end] ] => let Heq := fresh "Heq" in
              case_eq M; intros ? ? Heq; try rewrite Heq in *; try subst
            | [ _ : context[match ?M with exist _ _ => _ end] |- _ ] => let Heq := fresh "Heq" in
              case_eq M; intros ? ? Heq; try rewrite Heq in *; subst
            | [ H : forall n v, ?E n = Some v -> _,
                _ : context[match ?E ?N with Some _ => _ | None => _ end] |- _ ] =>
              specialize (H N); destruct (E N); try rewrite (H _ (eq_refl _)) by auto; try discriminate
            | [ H : forall n v, ?E n = Some v -> _, H' : ?E _ = Some _ |- _ ] => rewrite (H _ _ H') by auto
          end; simpl in *); eauto 7.

Ltac run := run'; repeat (match goal with
                            | [ H : forall n v, ?E n = Some v -> _
                                |- context[match ?E ?N with Some _ => _ | None => _ end] ] =>
                              specialize (H N); destruct (E N); try rewrite (H _ (eq_refl _)) by auto; try discriminate
                          end; run').

Lemma ex_irrelevant : forall P : Prop, P -> exists n : nat, P.
  exists 0; auto.
Qed.

Hint Resolve ex_irrelevant.

Require Import Max.

Theorem max_spec_le : forall n m, n <= m /\ max n m = m \/ m <= n /\ max n m = n.
  induction n; destruct m; simpl; intuition;
    specialize (IHn m); intuition.
Qed.

Ltac max := intros n m; generalize (max_spec_le n m); crush.

Lemma max_1 : forall n m, max n m >= n.
  max.
Qed.

Lemma max_2 : forall n m, max n m >= m.
  max.
Qed.

Hint Resolve max_1 max_2.

Lemma ge_refl : forall n, n >= n.
  crush.
Qed.

Hint Resolve ge_refl.

Hint Extern 1 => match goal with
                   | [ H : _ = exist _ _ _ |- _ ] => rewrite H
                 end.
(* end hide *)
(** remove printing exists *)

(** Now, as a simple first example of a computation, we can define [Bottom], which corresponds to an infinite loop.  For any approximation level, it fails to terminate (returns [None]).  Note the use of [abstract] to create a new opaque lemma for the proof found by the #<tt>#%\coqdocvar{%run%}%#</tt># tactic.  In contrast to the previous section, opaque proofs are fine here, since the proof components of computations do not influence evaluation behavior.  It is generally preferable to make proofs opaque when possible, as this enforces a kind of modularity in the code to follow, preventing it from depending on any details of the proof. *)

Section Bottom.
  Variable A : Type.

  Definition Bottom : computation A.
    exists (fun _ : nat => @None A); abstract run.
  Defined.

  Definition Bottom_manual : computation A.
    refine (exist _ (fun _ : nat => @None A) _).
    intros. assumption.
  Qed.
               
  Theorem run_Bottom : forall v, ~run Bottom v.
    run.
  Qed.

  Theorem run_Bottom_manual : forall v, run Bottom v -> False.
    unfold run. unfold runTo. intros.
    destruct H. simpl in H. inversion H.
  Qed.
  
End Bottom.

(** A slightly more complicated example is [Return], which gives the same terminating answer at every approximation level. *)

Section Return.
  Variable A : Type.
  Variable v : A.

  Definition Return : computation A.
    intros; exists (fun _ : nat => Some v); abstract run.
  Defined.

  Definition Return_manual : computation A.
    refine (exist _ (fun _ : nat => Some v) _).
    intros. assumption.
  Qed.

  Theorem run_Return : run Return v.
    run.
  Qed.

  Theorem run_Return_manualo : run Return v.
    unfold run. exists 0. unfold runTo. reflexivity.
  Qed.
    
End Return.

(** The name [Return] was meant to be suggestive of the standard operations of %\index{monad}%monads%~\cite{Monads}%.  The other standard operation is [Bind], which lets us run one computation and, if it terminates, pass its result off to another computation.  We implement bind using the notation [let (x, y) := e1 in e2], for pulling apart the value [e1] which may be thought of as a pair.  The second component of a [computation] is a proof, which we do not need to mention directly in the definition of [Bind]. *)

Section Bind.
  Variables A B : Type.
  Variable m1 : computation A.
  Variable m2 : A -> computation B.

  Definition Bind : computation B.
    exists (fun n =>
      let (f1, _) := m1 in
      match f1 n with
	| None => None
	| Some v =>
	  let (f2, _) := m2 v in
	    f2 n
      end); abstract run.
  Defined.

  Definition Bind_manual : computation B.
    refine (exist _ (fun n =>
                       let (f1, _) := m1 in
                       match f1 n with
                       | Some v =>
                         let (f2, _) := m2 v in
                         f2 n
                       | None => None
                       end
                    ) _ ).
    destruct m1.
    intros. 
    destruct (x n) eqn:Heq.
    -
      assert (H' : x n' = Some a). eauto.
      rewrite H'. 
      destruct (m2 a).
      eauto.
    -
      inversion H.
  Defined.        
      
  Theorem run_Bind : forall (v1 : A) (v2 : B),
    run m1 v1
    -> run (m2 v1) v2
    -> run Bind v2.
    run; match goal with
           | [ x : nat, y : nat |- _ ] => exists (max x y)
         end; run.
  Qed.

  Theorem run_Bind_manual : forall (v1 : A) (v2 : B),
      run m1 v1 ->
      run (m2 v1) v2 ->
      run Bind v2.
    intros.
    destruct H as [x1 H1]. destruct H0 as [x2 H2].
    exists (x1 + x2).
    unfold runTo. unfold Bind. simpl.
    destruct m1 as [f1 e1].
    unfold runTo in H1; simpl in H1.
    assert (H1' : f1 (x1 + x2) = Some v1).
    apply e1 with x1. assumption. omega.
    rewrite H1'.
    destruct (m2 v1) as [f2 e2].
    unfold runTo in H2; simpl in H2.
    apply e2 with x2. assumption. omega.
  Qed.      
    
End Bind.

(** A simple notation lets us write [Bind] calls the way they appear in Haskell. *)

Notation "x <- m1 ; m2" :=
  (Bind m1 (fun x => m2)) (right associativity, at level 70).

(** We can verify that we have indeed defined a monad, by proving the standard monad laws.  Part of the exercise is choosing an appropriate notion of equality between computations.  We use "equality at all approximation levels." *)

Definition meq A (m1 m2 : computation A) := forall n, proj1_sig m1 n = proj1_sig m2 n.

Theorem left_identity : forall A B (a : A) (f : A -> computation B),
  meq (Bind (Return a) f) (f a).
  run.
Qed.

Theorem left_identity_manual : forall A B (a : A) (f : A -> computation B),
    meq (Bind (Return a) f) (f a).
  intros. unfold meq. intros. simpl.
  destruct (f a) as [f' e'].
  reflexivity.
Qed.


Theorem right_identity : forall A (m : computation A),
  meq (Bind m (@Return _)) m.
  run.
Qed.

Theorem right_identity_manual : forall A (m : computation A),
    meq (Bind m (@Return A)) m.
  intros. unfold meq. intros. simpl.
  destruct m. simpl. destruct (x n).
  reflexivity. reflexivity.
Qed.


Theorem associativity : forall A B C (m : computation A)
  (f : A -> computation B) (g : B -> computation C),
  meq (Bind (Bind m f) g) (Bind m (fun x => Bind (f x) g)).
  run.
Qed.

Theorem associativity_manual : forall A B C (m : computation A)
                                      (f : A -> computation B) (g : B -> computation C),
    meq (Bind (Bind m f) g) (Bind m (fun x => Bind (f x) g)).
  intros.  unfold meq. intros. simpl.
  destruct m as [f_m H_m].
  destruct (f_m n) eqn:HEq.
  -
    destruct (f a) as [f_f H_f].
    reflexivity.
  -
    reflexivity.
Qed.

Section Lattice.
  Variables A : Type.

  Definition leq (x y : option A) :=
    forall v : A, x = Some v -> y = Some v.
End Lattice.

Section Fix.
  Variables A B : Type.

  Variable f : (A -> computation B) -> (A -> computation B).

  Hypothesis f_continuous :
    forall v1 n x v, runTo (f v1 x) n v ->
                     forall (v2 : A -> computation B), (forall x : A, leq (proj1_sig (v1 x) n) (proj1_sig (v2 x) n)) ->
                                runTo (f v2 x) n v.

  Fixpoint Fix' (n : nat) (x : A) : (computation B) :=
    match n with
    | 0 => Bottom _
    | S n' => f (Fix' n') x
    end.

  Lemma Fix'_ok : forall steps n x v,
      proj1_sig (Fix' n x) steps = Some v ->
      forall n', n' >= n -> proj1_sig (Fix' n' x) steps = Some v.
  Proof.
    induction n.
    -
      (* P 0 *)
      intros; inversion H.
    -
      (* P n -> P (S n) *)
      intros. destruct n'.
      +
        (* n' = 0 *)
        inversion H0.
      +
        (* n' = S n *)
        simpl.                 
        apply f_continuous with (Fix' n).  (* analyze with f_continous *)
        * simpl in H. assumption. (* trivial *)
        * unfold leq. intros. apply IHn. assumption. omega. (* trivial after proving leq *)
  Qed.

  Definition Fix : A -> computation B.
    refine (fun x : A => exist _ (fun n : nat => proj1_sig (Fix' n x) n) _).
    intros.    
    assert(HCrit : proj1_sig (Fix' n' x) n = Some v).
    {
      apply (@Fix'_ok n n x v H) in H0. 
      assumption.
    }
    destruct (Fix' n' x).
    eauto.
  Defined.

  Theorem Fix_ok : forall x v,
      run (f Fix x) v -> run (Fix x) v.
    intros. destruct H as [n].
    assert(HCrit : runTo (f (Fix' n) x) n v).
    {
      apply f_continuous with Fix.
      assumption.
      simpl. unfold leq. intros.
      destruct n.
      -
        inversion H0.
      -
        assumption.
    }
    exists (S n). unfold runTo. simpl.
    destruct (f (Fix' n) x).
    unfold runTo in HCrit; simpl in HCrit.
    simpl.
    apply e with n. assumption. omega.
  Qed.

End Fix.

Definition mergeSort' : forall (A : Type) (le : A -> A -> bool),  (list A) -> computation (list A).
  refine ( fun (A : Type) (le : A -> A -> bool) =>
      Fix (fun (mergeSortRec : (list A) -> computation (list A)) (ls : list A) =>
                 match le_lt_dec 2 (length ls) with
                 | left _ =>
                   let lss := split ls in
                   ls1 <- mergeSortRec (fst lss);
                   ls2 <- mergeSortRec (snd lss);
                   Return (merge le ls1 ls2)
                 | right _ =>
                   Return ls
                 end) _).
  intros.
  destruct (le_lt_dec 2 (length x)).
  -
    unfold runTo; simpl.
    unfold runTo in H; simpl in H.
    unfold leq in H0.
    assert(H1 : forall v : list A, proj1_sig (v1 (fst (split x))) n = Some v -> proj1_sig (v2 (fst (split x))) n = Some v). apply H0.
    assert(H2 : forall v : list A, proj1_sig (v1 (snd (split x))) n = Some v -> proj1_sig (v2 (snd (split x))) n = Some v). apply H0.        
    destruct (v1 (fst (split x))) as [f1_1 e1_1].
    destruct (v1 (snd (split x))) as [f1_2 e1_2].
    destruct (v2 (fst (split x))) as [f2_1 e2_1].
    destruct (v2 (snd (split x))) as [f2_2 e2_2].
    destruct (f1_1 n) eqn:Eqn_f1_1.
    +
      simpl in H1.
      apply H1 in Eqn_f1_1.
      rewrite Eqn_f1_1.
      destruct (f1_2 n) eqn:Eqn_f2_2.
      *
        simpl in H2.
        apply H2 in Eqn_f2_2.
        rewrite Eqn_f2_2.
        assumption.
      *
        inversion H.
    +
      inversion H.
  -
    assumption.
Defined.

Lemma testMergeSort' : run (mergeSort' leb (1 :: 2 :: 36:: 8 :: 19 :: nil)) (1 :: 2 :: 8 :: 19 :: 36 :: nil).
  exists 4. reflexivity.
Qed.

Definition looper : bool -> computation unit.
  refine (Fix (fun looper (b:bool) =>
                 if b then Return tt else looper b) _).
  intros.
  destruct x.
  -
    assumption.
  -
    unfold leq in H0. unfold runTo in H.
    apply H0 in H.
    unfold runTo. assumption.
Defined.

Lemma test_looper : run (looper true) tt.
  exists 1; reflexivity.
Qed.

