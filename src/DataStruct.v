(* Copyright (c) 2008-2012, 2015, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Arith List.

Require Import Cpdt.CpdtTactics.

Set Implicit Arguments.
Set Asymmetric Patterns.
(* end hide *)


(** %\chapter{Dependent Data Structures}% *)

(** Our red-black tree example from the last chapter illustrated how dependent types enable static enforcement of data structure invariants.  To find interesting uses of dependent data structures, however, we need not look to the favorite examples of data structures and algorithms textbooks.  More basic examples like length-indexed and heterogeneous lists come up again and again as the building blocks of dependent programs.  There is a surprisingly large design space for this class of data structure, and we will spend this chapter exploring it. *)

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist 0
  | Cons : forall n, A -> ilist n -> ilist (S n).

  Inductive fin : nat -> Set :=
  | Find : forall n, fin (S n)
  | Next : forall n, fin n -> fin (S n).

  Fixpoint get n (ls : ilist n) : fin n -> A :=
    match ls with
    | Nil =>
      fun f =>
        match f in (fin n') return (match n' with
                                    | 0 => A
                                    | _ => unit
                                    end) with
        | Find _ => tt
        | Next _ _ => tt
        end
    | Cons n1 x ls' => 
      fun f =>
        (match f in (fin n') return ((fin (pred n') -> A) -> A) with
         | Find _ => fun _ => x
         | Next _ f' => fun new_f => new_f f'
         end) (get ls')
    end.
End ilist.

Arguments Nil [A].
Arguments Find [n].

Check Cons 0 (Cons 1 (Cons 2 Nil)).

Eval simpl in get (Cons 0 (Cons 1 (Cons 2 Nil))) Find.
Eval simpl in get (Cons 0 (Cons 1 (Cons 2 Nil))) (Next Find).
Eval simpl in get (Cons 0 (Cons 1 (Cons 2 Nil))) (Next (Next Find)).


Section ilist_map.
  Variables A B : Set.

  Variable f : A -> B.

  Fixpoint ilist_map n (ls : ilist A n) : ilist B n :=
    match ls in (ilist _ n) return (ilist B n) with
    | Nil => Nil
    | Cons n x ls' => Cons (f x) (ilist_map ls')                           
    end.

  Theorem get_imap : forall n (ls : ilist A n) (fdx : fin n),
      get (ilist_map ls) fdx = f (get ls fdx).
    induction ls.
    -
      intros; simpl. inversion fdx.
    -
      simpl; intros; dep_destruct fdx.
      reflexivity. apply IHls.
  Qed.
End ilist_map.                                       

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall x ls, B x -> hlist ls -> hlist (x :: ls).

  Variable elem : A.

  Inductive member : list A -> Type :=
  | HFirst : forall ls, member (elem :: ls)
  | HNext : forall x ls, member ls -> member (x :: ls).

  Fixpoint hget (ls : list A) (hls : hlist ls) : member ls -> B elem :=
    match hls with
    | HNil =>
      fun memb =>
        match memb in (member ls') return (match ls' with
                                           | nil => B elem
                                           | _ => unit
                                           end) with
        | HFirst _ => tt
        | _ => tt
        end
    | HCons _ _ val rem_ls =>
      fun memb =>
        (match memb in (member ls') return (match ls' with
                                            | nil => Empty_set
                                            | x' :: ls'' =>
                                              B x' -> (member ls'' -> B elem) -> B elem
                                            end) with
         | HFirst _ => fun x _ => x
         | HNext _ _ memb' => fun _ recur => recur memb'
         end) val (hget rem_ls)
    end.
End hlist.

Arguments HNil [A B].
Arguments HCons [A B x ls] _ _.

Arguments HFirst [A elem ls].
Arguments HNext [A elem x ls] _.

Definition someTypes : list Set := nat :: bool :: nil.

Example someValues : hlist (fun T : Set =>  T) someTypes :=
  HCons 5 (HCons true HNil).

Eval simpl in (hget someValues HFirst).

Eval simpl in (hget someValues (HNext HFirst)).

Example somePairs : hlist (fun T : Set => T * T)%type someTypes :=
  HCons (1, 2) (HCons (true, false) HNil).

      
                                             

(** ** A Lambda Calculus Interpreter *)

(** Heterogeneous lists are very useful in implementing %\index{interpreters}%interpreters for functional programming languages.  Using the types and operations we have already defined, it is trivial to write an interpreter for simply typed lambda calculus%\index{lambda calculus}%.  Our interpreter can alternatively be thought of as a denotational semantics (but worry not if you are not familiar with such terminology from semantics).

   We start with an algebraic datatype for types. *)

Inductive type : Set :=
| Unit : type
| Arrow : type -> type -> type.

(** Now we can define a type family for expressions.  An [exp ts t] will stand for an expression that has type [t] and whose free variables have types in the list [ts].  We effectively use the de Bruijn index variable representation%~\cite{DeBruijn}%.  Variables are represented as [member] values; that is, a variable is more or less a constructive proof that a particular type is found in the type environment. *)

Inductive exp : list type -> type -> Set :=
| Const : forall ts, exp ts Unit
(* begin thide *)
| Var : forall ts t, member t ts -> exp ts t
| App : forall ts dom ran, exp ts (Arrow dom ran) -> exp ts dom -> exp ts ran
| Abs : forall ts dom ran, exp (dom :: ts) ran -> exp ts (Arrow dom ran).
(* end thide *)

Arguments Const [ts].

(** We write a simple recursive function to translate [type]s into [Set]s. *)

Fixpoint typeDenote (t : type) : Set :=
  match t with
    | Unit => unit
    | Arrow t1 t2 => typeDenote t1 -> typeDenote t2
  end.

(** Now it is straightforward to write an expression interpreter.  The type of the function, [expDenote], tells us that we translate expressions into functions from properly typed environments to final values.  An environment for a free variable list [ts] is simply an [hlist typeDenote ts].  That is, for each free variable, the heterogeneous list that is the environment must have a value of the variable's associated type.  We use [hget] to implement the [Var] case, and we use [HCons] to extend the environment in the [Abs] case. *)

(* EX: Define an interpreter for [exp]s. *)

(* begin thide *)
Fixpoint expDenote ts t (e : exp ts t) : hlist typeDenote ts -> typeDenote t :=
  match e with
    | Const _ => fun _ => tt

    | Var _ _ mem => fun s => hget s mem
    | App _ _ _ e1 e2 => fun s => (expDenote e1 s) (expDenote e2 s)
    | Abs _ _ _ e' => fun s => fun x => expDenote e' (HCons x s)
  end.

(** Like for previous examples, our interpreter is easy to run with [simpl]. *)

Eval simpl in expDenote Const HNil.
(** %\vspace{-.15in}% [[
    = tt
     : typeDenote Unit
]]
*)

Eval simpl in expDenote (Abs (dom := Unit) (Var HFirst)) HNil.
(** %\vspace{-.15in}% [[
     = fun x : unit => x
     : typeDenote (Arrow Unit Unit)
]]
*)

Eval simpl in expDenote (Abs (dom := Unit)
  (Abs (dom := Unit) (Var (HNext HFirst)))) HNil.
(** %\vspace{-.15in}% [[
     = fun x _ : unit => x
     : typeDenote (Arrow Unit (Arrow Unit Unit))
]]
*)

Eval simpl in expDenote (Abs (dom := Unit) (Abs (dom := Unit) (Var HFirst))) HNil.
(** %\vspace{-.15in}% [[
     = fun _ x0 : unit => x0
     : typeDenote (Arrow Unit (Arrow Unit Unit))
]]
*)

Eval simpl in expDenote (App (Abs (Var HFirst)) Const) HNil.
(** %\vspace{-.15in}% [[
     = tt
     : typeDenote Unit
]]
*)

(* end thide *)

(** We are starting to develop the tools behind dependent typing's amazing advantage over alternative approaches in several important areas.  Here, we have implemented complete syntax, typing rules, and evaluation semantics for simply typed lambda calculus without even needing to define a syntactic substitution operation.  We did it all without a single line of proof, and our implementation is manifestly executable.  Other, more common approaches to language formalization often state and prove explicit theorems about type safety of languages.  In the above example, we got type safety, termination, and other meta-theorems for free, by reduction to CIC, which we know has those properties. *)


(** * Recursive Type Definitions *)

(** %\index{recursive type definition}%There is another style of datatype definition that leads to much simpler definitions of the [get] and [hget] definitions above.  Because Coq supports "type-level computation," we can redo our inductive definitions as _recursive_ definitions.  Here we will preface type names with the letter [f] to indicate that they are based on explicit recursive _function_ definitions. *)

(* EX: Come up with an alternate [ilist] definition that makes it easier to write [get]. *)

Section filist.
  Variable A : Set.

(* begin thide *)
  Fixpoint filist (n : nat) : Set :=
    match n with
      | O => unit
      | S n' => A * filist n'
    end%type.

  (** We say that a list of length 0 has no contents, and a list of length [S n'] is a pair of a data value and a list of length [n']. *)

  Fixpoint ffin (n : nat) : Set :=
    match n with
      | O => Empty_set
      | S n' => option (ffin n')
    end.

  (** We express that there are no index values when [n = O], by defining such indices as type [Empty_set]; and we express that, at [n = S n'], there is a choice between picking the first element of the list (represented as [None]) or choosing a later element (represented by [Some idx], where [idx] is an index into the list tail).  For instance, the three values of type [ffin 3] are [None], [Some None], and [Some (Some None)]. *)

  Fixpoint fget (n : nat) : filist n -> ffin n -> A :=
    match n with
      | O => fun _ idx => match idx with end
      | S n' => fun ls idx =>
        match idx with
          | None => fst ls
          | Some idx' => fget n' (snd ls) idx'
        end
    end.

  (** Our new [get] implementation needs only one dependent [match], and its annotation is inferred for us.  Our choices of data structure implementations lead to just the right typing behavior for this new definition to work out. *)
(* end thide *)

End filist.

(** Heterogeneous lists are a little trickier to define with recursion, but we then reap similar benefits in simplicity of use. *)

(* EX: Come up with an alternate [hlist] definition that makes it easier to write [hget]. *)

Section fhlist.
  Variable A : Type.
  Variable B : A -> Type.

(* begin thide *)
  Fixpoint fhlist (ls : list A) : Type :=
    match ls with
      | nil => unit
      | x :: ls' => B x * fhlist ls'
    end%type.

  (** The definition of [fhlist] follows the definition of [filist], with the added wrinkle of dependently typed data elements. *)

  Variable elm : A.

  Fixpoint fmember (ls : list A) : Type :=
    match ls with
      | nil => Empty_set
      | x :: ls' => (x = elm) + fmember ls'
    end%type.

  (** The definition of [fmember] follows the definition of [ffin].  Empty lists have no members, and member types for nonempty lists are built by adding one new option to the type of members of the list tail.  While for [ffin] we needed no new information associated with the option that we add, here we need to know that the head of the list equals the element we are searching for.  We express that idea with a sum type whose left branch is the appropriate equality proposition.  Since we define [fmember] to live in [Type], we can insert [Prop] types as needed, because [Prop] is a subtype of [Type].

     We know all of the tricks needed to write a first attempt at a [get] function for [fhlist]s.
     [[
  Fixpoint fhget (ls : list A) : fhlist ls -> fmember ls -> B elm :=
    match ls with
      | nil => fun _ idx => match idx with end
      | _ :: ls' => fun mls idx =>
        match idx with
          | inl _ => fst mls
          | inr idx' => fhget ls' (snd mls) idx'
        end
    end.
    ]]
    %\vspace{-.15in}%Only one problem remains.  The expression [fst mls] is not known to have the proper type.  To demonstrate that it does, we need to use the proof available in the [inl] case of the inner [match]. *)

  Fixpoint fhget (ls : list A) : fhlist ls -> fmember ls -> B elm :=
    match ls with
      | nil => fun _ idx => match idx with end
      | _ :: ls' => fun mls idx =>
        match idx with
          | inl pf => match pf with
                        | eq_refl => fst mls
                      end
          | inr idx' => fhget ls' (snd mls) idx'
        end
    end.

  (** By pattern-matching on the equality proof [pf], we make that equality known to the type-checker.  Exactly why this works can be seen by studying the definition of equality. *)

  (* begin hide *)
  (* begin thide *)
  Definition foo := @eq_refl.
  (* end thide *)
  (* end hide *)

  Print eq.
  (** %\vspace{-.15in}% [[
Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : x = x
]]

In a proposition [x = y], we see that [x] is a parameter and [y] is a regular argument.  The type of the constructor [eq_refl] shows that [y] can only ever be instantiated to [x].  Thus, within a pattern-match with [eq_refl], occurrences of [y] can be replaced with occurrences of [x] for typing purposes. *)
(* end thide *)

End fhlist.

Arguments fhget [A B elm ls] _ _.

(** How does one choose between the two data structure encoding strategies we have presented so far?  Before answering that question in this chapter's final section, we introduce one further approach. *)


(** * Data Structures as Index Functions *)

(** %\index{index function}%Indexed lists can be useful in defining other inductive types with constructors that take variable numbers of arguments.  In this section, we consider parameterized trees with arbitrary branching factor. *)

(* begin hide *)
Definition red_herring := O.
(* working around a bug in Coq 8.5! *)
(* end hide *)

Section tree.
  Variable A : Set.

  Inductive tree : Set :=
  | Leaf : A -> tree
  | Node : forall n, ilist tree n -> tree.
End tree.

(** Every [Node] of a [tree] has a natural number argument, which gives the number of child trees in the second argument, typed with [ilist].  We can define two operations on trees of naturals: summing their elements and incrementing their elements.  It is useful to define a generic fold function on [ilist]s first. *)

Section ifoldr.
  Variables A B : Set.
  Variable f : A -> B -> B.
  Variable i : B.

  Fixpoint ifoldr n (ls : ilist A n) : B :=
    match ls with
      | Nil => i
      | Cons _ x ls' => f x (ifoldr ls')
    end.
End ifoldr.

Fixpoint sum (t : tree nat) : nat :=
  match t with
    | Leaf n => n
    | Node _ ls => ifoldr (fun t' n => sum t' + n) O ls
  end.

Fixpoint inc (t : tree nat) : tree nat :=
  match t with
    | Leaf n => Leaf (S n)
    | Node _ ls => Node (imap inc ls)
  end.

(** Now we might like to prove that [inc] does not decrease a tree's [sum]. *)

Theorem sum_inc : forall t, sum (inc t) >= sum t.
(* begin thide *)
  induction t; crush.
  (** [[
  n : nat
  i : ilist (tree nat) n
  ============================
   ifoldr (fun (t' : tree nat) (n0 : nat) => sum t' + n0) 0 (imap inc i) >=
   ifoldr (fun (t' : tree nat) (n0 : nat) => sum t' + n0) 0 i
 
   ]]

   We are left with a single subgoal which does not seem provable directly.  This is the same problem that we met in Chapter 3 with other %\index{nested inductive type}%nested inductive types. *)

  Check tree_ind.
  (** %\vspace{-.15in}% [[
  tree_ind
     : forall (A : Set) (P : tree A -> Prop),
       (forall a : A, P (Leaf a)) ->
       (forall (n : nat) (i : ilist (tree A) n), P (Node i)) ->
       forall t : tree A, P t
]]

The automatically generated induction principle is too weak.  For the [Node] case, it gives us no inductive hypothesis.  We could write our own induction principle, as we did in Chapter 3, but there is an easier way, if we are willing to alter the definition of [tree]. *)

Abort.

Reset tree.
(* begin hide *)
Reset red_herring.
(* working around a bug in Coq 8.5! *)
(* end hide *)

(** First, let us try using our recursive definition of [ilist]s instead of the inductive version. *)

Section tree.
  Variable A : Set.

  (** %\vspace{-.15in}% [[
  Inductive tree : Set :=
  | Leaf : A -> tree
  | Node : forall n, filist tree n -> tree.
]]

<<
Error: Non strictly positive occurrence of "tree" in
 "forall n : nat, filist tree n -> tree"
>>

  The special-case rule for nested datatypes only works with nested uses of other inductive types, which could be replaced with uses of new mutually inductive types.  We defined [filist] recursively, so it may not be used in nested inductive definitions.

  Our final solution uses yet another of the inductive definition techniques introduced in Chapter 3, %\index{reflexive inductive type}%reflexive types.  Instead of merely using [fin] to get elements out of [ilist], we can _define_ [ilist] in terms of [fin].  For the reasons outlined above, it turns out to be easier to work with [ffin] in place of [fin]. *)

  Inductive tree : Set :=
  | Leaf : A -> tree
  | Node : forall n, (ffin n -> tree) -> tree.

  (** A [Node] is indexed by a natural number [n], and the node's [n] children are represented as a function from [ffin n] to trees, which is isomorphic to the [ilist]-based representation that we used above. *)

End tree.

Arguments Node [A n] _.

(** We can redefine [sum] and [inc] for our new [tree] type.  Again, it is useful to define a generic fold function first.  This time, it takes in a function whose domain is some [ffin] type, and it folds another function over the results of calling the first function at every possible [ffin] value. *)

Section rifoldr.
  Variables A B : Set.
  Variable f : A -> B -> B.
  Variable i : B.

  Fixpoint rifoldr (n : nat) : (ffin n -> A) -> B :=
    match n with
      | O => fun _ => i
      | S n' => fun get => f (get None) (rifoldr n' (fun idx => get (Some idx)))
    end.
End rifoldr.

Arguments rifoldr [A B] f i [n] _.

Fixpoint sum (t : tree nat) : nat :=
  match t with
    | Leaf n => n
    | Node _ f => rifoldr plus O (fun idx => sum (f idx))
  end.

Fixpoint inc (t : tree nat) : tree nat :=
  match t with
    | Leaf n => Leaf (S n)
    | Node _ f => Node (fun idx => inc (f idx))
  end.

(** Now we are ready to prove the theorem where we got stuck before.  We will not need to define any new induction principle, but it _will_ be helpful to prove some lemmas. *)

Lemma plus_ge : forall x1 y1 x2 y2,
  x1 >= x2
  -> y1 >= y2
  -> x1 + y1 >= x2 + y2.
  crush.
Qed.

Lemma sum_inc' : forall n (f1 f2 : ffin n -> nat),
  (forall idx, f1 idx >= f2 idx)
  -> rifoldr plus O f1 >= rifoldr plus O f2.
  Hint Resolve plus_ge.

  induction n; crush.
Qed.

Theorem sum_inc : forall t, sum (inc t) >= sum t.
  Hint Resolve sum_inc'.

  induction t; crush.
Qed.

(* end thide *)

(** Even if Coq would generate complete induction principles automatically for nested inductive definitions like the one we started with, there would still be advantages to using this style of reflexive encoding.  We see one of those advantages in the definition of [inc], where we did not need to use any kind of auxiliary function.  In general, reflexive encodings often admit direct implementations of operations that would require recursion if performed with more traditional inductive data structures. *)

(** ** Another Interpreter Example *)

(** We develop another example of variable-arity constructors, in the form of optimization of a small expression language with a construct like Scheme's <<cond>>.  Each of our conditional expressions takes a list of pairs of boolean tests and bodies.  The value of the conditional comes from the body of the first test in the list to evaluate to [true].  To simplify the %\index{interpreters}%interpreter we will write, we force each conditional to include a final, default case. *)

Inductive type' : Type := Nat | Bool.

Inductive exp' : type' -> Type :=
| NConst : nat -> exp' Nat
| Plus : exp' Nat -> exp' Nat -> exp' Nat
| Eq : exp' Nat -> exp' Nat -> exp' Bool

| BConst : bool -> exp' Bool
(* begin thide *)
| Cond : forall n t, (ffin n -> exp' Bool)
  -> (ffin n -> exp' t) -> exp' t -> exp' t.
(* end thide *)

(** A [Cond] is parameterized by a natural [n], which tells us how many cases this conditional has.  The test expressions are represented with a function of type [ffin n -> exp' Bool], and the bodies are represented with a function of type [ffin n -> exp' t], where [t] is the overall type.  The final [exp' t] argument is the default case.  For example, here is an expression that successively checks whether [2 + 2 = 5] (returning 0 if so) or if [1 + 1 = 2] (returning 1 if so), returning 2 otherwise. *)

Example ex1 := Cond 2
  (fun f => match f with
              | None => Eq (Plus (NConst 2) (NConst 2)) (NConst 5)
              | Some None => Eq (Plus (NConst 1) (NConst 1)) (NConst 2)
              | Some (Some v) => match v with end
            end)
  (fun f => match f with
              | None => NConst 0
              | Some None => NConst 1
              | Some (Some v) => match v with end
            end)
  (NConst 2).

(** We start implementing our interpreter with a standard type denotation function. *)

Definition type'Denote (t : type') : Set :=
  match t with
    | Nat => nat
    | Bool => bool
  end.

(** To implement the expression interpreter, it is useful to have the following function that implements the functionality of [Cond] without involving any syntax. *)

(* begin thide *)
Section cond.
  Variable A : Set.
  Variable default : A.

  Fixpoint cond (n : nat) : (ffin n -> bool) -> (ffin n -> A) -> A :=
    match n with
      | O => fun _ _ => default
      | S n' => fun tests bodies =>
        if tests None
          then bodies None
          else cond n'
            (fun idx => tests (Some idx))
            (fun idx => bodies (Some idx))
    end.
End cond.

Arguments cond [A] default [n] _ _.
(* end thide *)

(** Now the expression interpreter is straightforward to write. *)

(* begin thide *)
Fixpoint exp'Denote t (e : exp' t) : type'Denote t :=
  match e with
    | NConst n => n
    | Plus e1 e2 => exp'Denote e1 + exp'Denote e2
    | Eq e1 e2 =>
      if eq_nat_dec (exp'Denote e1) (exp'Denote e2) then true else false

    | BConst b => b
    | Cond _ _ tests bodies default =>
      cond
      (exp'Denote default)
      (fun idx => exp'Denote (tests idx))
      (fun idx => exp'Denote (bodies idx))
  end.
(* begin hide *)
Reset exp'Denote.
(* end hide *)
(* end thide *)

(* begin hide *)
Fixpoint exp'Denote t (e : exp' t) : type'Denote t :=
  match e with
    | NConst n => n
    | Plus e1 e2 => exp'Denote e1 + exp'Denote e2
    | Eq e1 e2 =>
      if eq_nat_dec (exp'Denote e1) (exp'Denote e2) then true else false

    | BConst b => b
    | Cond _ _ tests bodies default =>
(* begin thide *)
      cond
      (exp'Denote default)
      (fun idx => exp'Denote (tests idx))
      (fun idx => exp'Denote (bodies idx))
(* end thide *)
  end.
(* end hide *)

(** We will implement a constant-folding function that optimizes conditionals, removing cases with known-[false] tests and cases that come after known-[true] tests.  A function [cfoldCond] implements the heart of this logic.  The convoy pattern is used again near the end of the implementation. *)

(* begin thide *)
Section cfoldCond.
  Variable t : type'.
  Variable default : exp' t.

  Fixpoint cfoldCond (n : nat)
    : (ffin n -> exp' Bool) -> (ffin n -> exp' t) -> exp' t :=
    match n with
      | O => fun _ _ => default
      | S n' => fun tests bodies =>
        match tests None return _ with
          | BConst true => bodies None
          | BConst false => cfoldCond n'
            (fun idx => tests (Some idx))
            (fun idx => bodies (Some idx))
          | _ =>
            let e := cfoldCond n'
              (fun idx => tests (Some idx))
              (fun idx => bodies (Some idx)) in
            match e in exp' t return exp' t -> exp' t with
              | Cond n _ tests' bodies' default' => fun body =>
                Cond
                (S n)
                (fun idx => match idx with
                              | None => tests None
                              | Some idx => tests' idx
                            end)
                (fun idx => match idx with
                              | None => body
                              | Some idx => bodies' idx
                            end)
                default'
              | e => fun body =>
                Cond
                1
                (fun _ => tests None)
                (fun _ => body)
                e
            end (bodies None)
        end
    end.
End cfoldCond.

Arguments cfoldCond [t] default [n] _ _.
(* end thide *)

(** Like for the interpreters, most of the action was in this helper function, and [cfold] itself is easy to write. *)

(* begin thide *)
Fixpoint cfold t (e : exp' t) : exp' t :=
  match e with
    | NConst n => NConst n
    | Plus e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' return exp' Nat with
        | NConst n1, NConst n2 => NConst (n1 + n2)
        | _, _ => Plus e1' e2'
      end
    | Eq e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' return exp' Bool with
        | NConst n1, NConst n2 => BConst (if eq_nat_dec n1 n2 then true else false)
        | _, _ => Eq e1' e2'
      end

    | BConst b => BConst b
    | Cond _ _ tests bodies default =>
      cfoldCond
      (cfold default)
      (fun idx => cfold (tests idx))
      (fun idx => cfold (bodies idx))
  end.
(* end thide *)

(* begin thide *)
(** To prove our final correctness theorem, it is useful to know that [cfoldCond] preserves expression meanings.  The following lemma formalizes that property.  The proof is a standard mostly automated one, with the only wrinkle being a guided instantiation of the quantifiers in the induction hypothesis. *)

Lemma cfoldCond_correct : forall t (default : exp' t)
  n (tests : ffin n -> exp' Bool) (bodies : ffin n -> exp' t),
  exp'Denote (cfoldCond default tests bodies)
  = exp'Denote (Cond n tests bodies default).
  induction n; crush;
    match goal with
      | [ IHn : forall tests bodies, _, tests : _ -> _, bodies : _ -> _ |- _ ] =>
        specialize (IHn (fun idx => tests (Some idx)) (fun idx => bodies (Some idx)))
    end;
    repeat (match goal with
              | [ |- context[match ?E with NConst _ => _ | _ => _ end] ] =>
                dep_destruct E
              | [ |- context[if ?B then _ else _] ] => destruct B
            end; crush).
Qed.

(** It is also useful to know that the result of a call to [cond] is not changed by substituting new tests and bodies functions, so long as the new functions have the same input-output behavior as the old.  It turns out that, in Coq, it is not possible to prove in general that functions related in this way are equal.  We treat this issue with our discussion of axioms in a later chapter.  For now, it suffices to prove that the particular function [cond] is _extensional_; that is, it is unaffected by substitution of functions with input-output equivalents. *)

Lemma cond_ext : forall (A : Set) (default : A) n (tests tests' : ffin n -> bool)
  (bodies bodies' : ffin n -> A),
  (forall idx, tests idx = tests' idx)
  -> (forall idx, bodies idx = bodies' idx)
  -> cond default tests bodies
  = cond default tests' bodies'.
  induction n; crush;
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E
    end; crush.
Qed.

(** Now the final theorem is easy to prove. *)
(* end thide *)

Theorem cfold_correct : forall t (e : exp' t),
  exp'Denote (cfold e) = exp'Denote e.
(* begin thide *)
  Hint Rewrite cfoldCond_correct.
  Hint Resolve cond_ext.

  induction e; crush;
    repeat (match goal with
              | [ |- context[cfold ?E] ] => dep_destruct (cfold E)
            end; crush).
Qed.
(* end thide *)

(** We add our two lemmas as hints and perform standard automation with pattern-matching of subterms to destruct. *)

(** * Choosing Between Representations *)

(** It is not always clear which of these representation techniques to apply in a particular situation, but I will try to summarize the pros and cons of each.

   Inductive types are often the most pleasant to work with, after someone has spent the time implementing some basic library functions for them, using fancy [match] annotations.  Many aspects of Coq's logic and tactic support are specialized to deal with inductive types, and you may miss out if you use alternate encodings.

   Recursive types usually involve much less initial effort, but they can be less convenient to use with proof automation.  For instance, the [simpl] tactic (which is among the ingredients in [crush]) will sometimes be overzealous in simplifying uses of functions over recursive types.  Consider a call [get l f], where variable [l] has type [filist A (S n)].  The type of [l] would be simplified to an explicit pair type.  In a proof involving many recursive types, this kind of unhelpful "simplification" can lead to rapid bloat in the sizes of subgoals.  Even worse, it can prevent syntactic pattern-matching, like in cases where [filist] is expected but a pair type is found in the "simplified" version.  The same problem applies to applications of recursive functions to values in recursive types: the recursive function call may "simplify" when the top-level structure of the type index but not the recursive value is known, because such functions are generally defined by recursion on the index, not the value.

   Another disadvantage of recursive types is that they only apply to type families whose indices determine their "skeletons."  This is not true for all data structures; a good counterexample comes from the richly typed programming language syntax types we have used several times so far.  The fact that a piece of syntax has type [Nat] tells us nothing about the tree structure of that syntax.

   Finally, Coq type inference can be more helpful in constructing values in inductive types.  Application of a particular constructor of that type tells Coq what to expect from the arguments, while, for instance, forming a generic pair does not make clear an intention to interpret the value as belonging to a particular recursive type.  This downside can be mitigated to an extent by writing "constructor" functions for a recursive type, mirroring the definition of the corresponding inductive type.

   Reflexive encodings of data types are seen relatively rarely.  As our examples demonstrated, manipulating index values manually can lead to hard-to-read code.  A normal inductive type is generally easier to work with, once someone has gone through the trouble of implementing an induction principle manually with the techniques we studied in Chapter 3.  For small developments, avoiding that kind of coding can justify the use of reflexive data structures.  There are also some useful instances of %\index{co-inductive types}%co-inductive definitions with nested data structures (e.g., lists of values in the co-inductive type) that can only be deconstructed effectively with reflexive encoding of the nested structures. *)
