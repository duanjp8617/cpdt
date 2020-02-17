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

Section mergeSort.
  Variable A : Type.
  Variable le : A -> A -> bool.

  Fixpoint insert (x : A) (ls : list A) :=
    match ls with
    | nil => x :: nil
    | y :: ls' => if le x y then x :: ls else y :: (insert x ls')
    end.

  Fixpoint merge (ls1 ls2 : list A) :=
    match ls1 with
    | nil => ls2
    | h :: ls1' => insert h (merge ls1' ls2)
    end.

  Fixpoint split (ls : list A) : list A * list A :=
    match ls with
    | nil => (nil, nil)
    | x :: nil => (ls, nil)
    | x :: y :: ls' =>
      let (ls1', ls2') := split ls' in
      (x :: ls1', y :: ls2')
    end.

  (* Fixpoint mergeSort (ls : list A) := *)
  (*   if (leb (length ls) 1) *)
  (*   then ls *)
  (*   else *)
  (*     let (ls1, ls2) := split ls in *)
  (*     merge (mergeSort ls1) (mergeSort ls2). *)
  
  
  Inductive Acc' (A : Type) (R : A -> A -> Prop): A -> Prop :=
  | Acc_intro' : forall x : A, (forall y : A, R y x -> Acc' R y) -> Acc' R x.
  
  CoInductive infiniteDecreasingChain A (R : A -> A -> Prop) : stream A -> Prop :=
  | ChainCons : forall x y s, infiniteDecreasingChain R (Cons y s) -> R y x -> infiniteDecreasingChain R (Cons x (Cons y s)).

  Lemma noBadChains' : forall A (R : A -> A -> Prop) x, Acc R x -> forall s, ~ infiniteDecreasingChain R (Cons x s).
    intros. generalize dependent s. induction H.
    intro s. intro Contra.
    inversion Contra.
    apply (H0 y H4 s0 H3).
  Qed.
  
  
  Theorem noBadChains : forall A (R : A -> A -> Prop), (forall a : A, Acc R a) -> forall s, ~ infiniteDecreasingChain R s.
    destruct s. apply noBadChains'. eauto.
  Qed.
  
  Check Fix.
  
  Definition lengthOrder (ls1 ls2 : list A) :=
    length ls1 < length ls2.

  Hint Constructors Acc.

  Lemma lengthOrder_wf' : forall len ls, length ls <= len -> Acc lengthOrder ls.
    unfold lengthOrder; induction len; crush.
  Defined.

  Theorem lengthOrder_wf : well_founded lengthOrder.
    red; intro; eapply lengthOrder_wf'; eauto.
  Defined.

  Lemma split_wf : forall len ls, 2 <= length ls <= len
                              -> let (ls1, ls2) := split ls in
                                 lengthOrder ls1 ls /\ lengthOrder ls2 ls.
  unfold lengthOrder; induction len; crush; do 2 (destruct ls; crush);
                                                 destruct (le_lt_dec 2 (length ls));
                                                 repeat (match goal with
                                                         | [ _ : length ?E <2 |- _ ] => destruct E
                                                         | [ _ : S (length ?E) < 2 |- _ ] => destruct E
                                                         | [IH : _ |- context [split ?l] ] => specialize (IH L); destruct (split L); destruct IH
                                                         end; crush).
  
  
