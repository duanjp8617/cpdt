(* Copyright (c) 2008-2012, 2015, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import List.

Require Import Cpdt.CpdtTactics.

Set Implicit Arguments.
Set Asymmetric Patterns.
(* end hide *)

Check (fun x: nat => x).

Check (fun x: True => x).

Check I.

Check (fun _: False => I).

Check (fun x: False => x).

Inductive unit: Set :=
| tt.

Check unit.

Check tt.

Theorem unit_singleton: forall x: unit, x = tt.
Proof.
  destruct x. reflexivity.
Qed.

Check unit_ind.

Inductive Empty_set : Set := .

Theorem the_sky_is_faling: forall x: Empty_set, 2 + 2 = 5.
Proof.
  destruct 1.
Qed.

Check Empty_set_ind.

Definition e2u (e: Empty_set) : unit := match e with end.

Check e2u.

Inductive bool: Set :=
| true
| false.

Check bool_ind.

Definition negb (b: bool) : bool :=
  match b with
  | true => false
  | fales => true
  end.

Definition negb' (b : bool) : bool :=
  if b then false else true.

Theorem negb_inverse : forall b : bool, negb (negb b) = b.
Proof.
  destruct b; reflexivity.
Qed.

Theorem negb_ineq' : forall b : bool, negb b = b -> False.
Proof.
  destruct b; discriminate.
Qed.

Theorem negb_ineq : forall b : bool, negb b <> b.
Proof.
  destruct b; discriminate.
Qed.

Check bool_ind.

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Definition isZero (n : nat) : bool :=
  match n with
  | O => true
  | S _ => false
  end.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.


Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Theorem O_plus_n : forall n : nat, plus O n = n.
Proof.
  intros. reflexivity.
Qed.

Theorem n_plus_O : forall n : nat, plus n O = n.
  induction n.
  reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Theorem n_plus_O' : forall n : nat, plus n O = n.
  induction n; crush.
Qed.

Check nat_ind.

Theorem S_inj : forall n m : nat, S n = S m -> n = m.
Proof.
  injection 1; trivial.
Qed.

Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.

Check nat_list_ind.

Fixpoint nlength (ls : nat_list) : nat :=
  match ls with
  | NNil => O
  | NCons _ ls' => S (nlength ls')
  end.

Fixpoint napp (ls1 ls2 : nat_list) : nat_list :=
  match ls1 with
  | NNil => ls2
  | NCons n ls' => NCons n (napp ls' ls2)
  end.

Theorem nlength_napp : forall ls1 ls2 : nat_list, nlength (napp ls1 ls2) = plus (nlength ls1) (nlength ls2).
Proof.
  induction ls1; crush.
Qed.


Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

Check nat_btree_ind.

Fixpoint nsize (tr : nat_btree) : nat :=
  match tr with
  | NLeaf => S O
  | NNode tr1' _ tr2' => plus (nsize tr1') (nsize tr2')
  end.

Fixpoint nsplice (tr1 tr2 : nat_btree) : nat_btree :=
  match tr1 with
  | NLeaf => NNode tr2 O NLeaf
  | NNode tr1' n tr2' => NNode (nsplice tr1' tr2) n tr2'
  end.

Theorem plus_assoc : forall n1 n2 n3 : nat, plus (plus n1 n2) n3 = plus n1 (plus n2 n3).
Proof.
  induction n1; crush.
Qed.

Hint Rewrite n_plus_O plus_assoc.

Theorem nsize_nsplice : forall tr1 tr2 : nat_btree, nsize (nsplice tr1 tr2) = plus (nsize tr2) (nsize tr1).
  induction tr1; crush.
Qed.

Check nat_btree_ind.

Inductive list (T : Set) : Set :=
| Nil : list T
| Cons : T -> list T -> list T.

Fixpoint length T (ls : list T) : nat :=
  match ls with
  | Nil => O
  | Cons _ ls' => S (length ls')
  end.

Fixpoint app T (ls1 ls2 : list T) : list T :=
  match ls1 with
  | Nil => ls2
  | Cons n ls' => Cons n (app ls' ls2)
  end.


Theorem length_app : forall (T : Set) (ls1 ls2 : list T), plus (length ls1) (length ls2) = length (app ls1 ls2).
Proof.
  induction ls1; crush.
Qed.

Arguments Nil [T].

Print list.

Check length.

Check list_ind.

Inductive even_list : Set :=
| ENil : even_list
| ECons : nat -> odd_list -> even_list

with odd_list : Set :=
| OCons : nat -> even_list -> odd_list.

Check even_list_ind.

Check odd_list_ind.

Fixpoint elength (el : even_list) : nat :=
  match el with
  | ENil => O
  | ECons _ ol => S (olength ol)
  end
    

with olength (ol : odd_list) : nat :=
       match ol with
       | OCons _ el => S (elength el)
       end.

Fixpoint eapp (el1 el2 : even_list) : even_list :=
  match el1 with
  | ENil => el2
  | ECons n ol => ECons n (oapp ol el2)
  end

with oapp (ol : odd_list) (el : even_list) : odd_list :=
       match ol with
       | OCons n el' => OCons n (eapp el' el)
       end.

Theorem elength_eapp : forall (el1 el2 : even_list), plus (elength el1) (elength el2) = elength (eapp el1 el2).
  induction el1; crush.
Abort.

Scheme even_list_mut := Induction for even_list Sort Prop
  with odd_list_mut := Induction for odd_list Sort Prop.

Theorem elength_eapp : forall (el1 el2 : even_list), plus (elength el1) (elength el2) = elength (eapp el1 el2).
Proof.
  apply (even_list_mut
           (fun el1 => forall (el2 : even_list), plus (elength el1) (elength el2) = elength (eapp el1 el2))
           (fun ol => forall (el : even_list), plus (olength ol) (elength el) = olength (oapp ol el))); crush.
Qed.

Inductive pformula : Set :=
| Truth : pformula
| Falsehood : pformula
| Conjuction : pformula -> pformula -> pformula.

Fixpoint pformulaDenote (f : pformula) : Prop :=
  match f with
  | Truth => True
  | Falsehood => False
  | Conjuction f1 f2 => pformulaDenote f1 /\ pformulaDenote f2
  end.

Inductive formula : Set :=
| Eq : nat -> nat -> formula
| And : formula -> formula -> formula
| Forall :  (nat -> formula) -> formula.

Fixpoint formulaDenote (f : formula) : Prop :=
  match f with
  | Eq x y => x = y
  | And f1 f2 => (formulaDenote f1) /\ (formulaDenote f2)
  | Forall f' => forall n : nat, formulaDenote (f' n)
  end.

Fixpoint swapper (f : formula) : formula :=
  match f with
  | Eq x y => Eq y x
  | And f1 f2 => And f2 f1
  | Forall f' => Forall (fun n => swapper (f' n))
  end.


Theorem swapper_preserves_truth : forall f, formulaDenote f -> formulaDenote (swapper f).
  induction f; crush.
Qed.

Check formula_ind.

Print nat_ind.
                                 
Print nat_rect.

Definition nat_ind' : forall P : nat -> Prop, P O -> (forall n : nat,  P n -> P (S n)) -> forall n : nat,  P n := fun P : nat -> Prop => nat_rect P.

Print nat_rec.

Definition nat_rec' : forall P : nat -> Set, P O -> (forall n : nat,  P n -> P (S n)) -> forall n : nat, P n := fun P => nat_rect P.

Fixpoint plus_recursive (n : nat) : nat -> nat :=
  match n with
  | O => fun m => m
  | S n' => fun m => S (plus_recursive n' m)
  end.

Definition plus_rec : nat -> nat -> nat :=
  nat_rec (fun _ : nat => nat -> nat) (fun m => m) (fun n f =>  (fun m =>  S (f m))).

Definition plus_rec' : nat -> nat -> nat :=
  nat_rec (fun _ : nat => nat -> nat) (fun m => m) (fun _ r m => S (r m)).

Theorem plus_equivalent : plus_recursive = plus_rec.
Proof.
  unfold plus_recursive.
  unfold plus_rec.
  unfold nat_rec.
  unfold nat_rect.
  reflexivity.
Qed.

Print nat_rect.

Fixpoint nat_rect' (P: nat -> Type)
         (HO : P O)
         (HS : forall n, P n -> P (S n)) (n : nat) :=
  match n return P n with
  | O => HO
  | S n' => HS n' (nat_rect' P HO HS n')
  end.

Fixpoint even_list_ind' (PE : even_list -> Prop)
         (PO : odd_list -> Prop)
         (H0 : PE ENil)
         (H1 : forall (n : nat) (lo : odd_list), PO lo -> PE (ECons n lo))
         (H2 : forall (n: nat) (le : even_list), PE le -> PO (OCons n le))
         (le : even_list) :=
  match le return PE le with
  | ENil => H0
  | ECons n lo => H1 n lo (odd_list_ind' PE PO H0 H1 H2 lo)
  end

with odd_list_ind' (PE : even_list -> Prop)
         (PO : odd_list -> Prop)
         (H0 : PE ENil)
         (H1 : forall (n : nat) (lo : odd_list), PO lo -> PE (ECons n lo))
         (H2 : forall (n: nat) (le : even_list), PE le -> PO (OCons n le))
         (lo : odd_list) :=
       match lo return PO lo with
       | OCons n le => H2 n le (even_list_ind' PE PO H0 H1 H2 le)
       end.

Section even_list_mut_from_the_book'.
  Variable Peven : even_list -> Prop.
  Variable Podd : odd_list -> Prop.

  Hypothesis ENil_case : Peven ENil.
  Hypothesis ECons_case : forall (n : nat) (o : odd_list), Podd o -> Peven (ECons n o).
  Hypothesis OCons_case : forall (n : nat) (e : even_list), Peven e -> Podd (OCons n e).

  Fixpoint even_list_mut' (e : even_list) : Peven e :=
    match e with
    | ENil => ENil_case
    | ECons n o => ECons_case n (odd_list_mut' o)
    end
  with odd_list_mut' (o : odd_list) : Podd o :=
         match o with
         | OCons n e => OCons_case n (even_list_mut' e)
         end.
End even_list_mut_from_the_book'.

Fixpoint formula_ind' (P : formula -> Prop)
         (H0 : forall (n0 n1 : nat), P (Eq n0 n1))
         (H1 : forall (f0 f1 : formula), P f0 -> P f1 -> P (And f0 f1))
         (H2 : forall (f : nat -> formula), (forall n : nat, P (f n)) -> P (Forall f))
                                                                         (f : formula) :=
            match f return P f with
            | Eq n0 n1 => H0 n0 n1
            | And f0 f1 => H1 f0 f1 (formula_ind' P H0 H1 H2 f0) (formula_ind' P H0 H1 H2 f1)
            | Forall func => H2 func (fun n => formula_ind' P H0 H1 H2 (func n))
            end.

Inductive nat_tree : Set :=
| NNode' : nat -> list nat_tree -> nat_tree.

Check nat_tree_ind.

Section All.
  Variable T : Set.
  Variable P : T -> Prop.
  Fixpoint All (ls : list T) : Prop :=
    match ls with
    | Nil => True
    | Cons h t => (P h) /\ All t
    end.
End All.

Locate "/\".

Print and.

Print All.

Section nat_tree_ind'.
  Variable P : nat_tree -> Prop.
  Hypothesis NNode'_case : forall (n : nat) (ls : list nat_tree), All P ls -> P (NNode' n ls).
Fixpoint nat_tree_ind' (tr : nat_tree) : P tr :=
  match tr with
  | NNode' n ls => NNode'_case n ls
                               ((fix list_nat_tree_ind (ls : list nat_tree) : All P ls :=
                                   match ls with
                                   | Nil => I
                                   | Cons tr' rest => conj (nat_tree_ind' tr') (list_nat_tree_ind rest)
                                   end
                                ) ls)
  end.  
End nat_tree_ind'.    

Check nat_tree_ind'.                                                                         
Section map.
  Variables T T' : Set.
  Variable F : T -> T'.

  Fixpoint map (ls : list T) : list T' :=
    match ls with
    | Nil => Nil
    | Cons h t => Cons (F h) (map t)
    end.
End map.

Fixpoint sum (ls : list nat) : nat :=
  match ls with
  | Nil => O
  | Cons n t => plus n (sum t)
  end.

Fixpoint ntsize (tr : nat_tree) : nat :=
  match tr with
  | NNode' _ trs => S (sum (map ntsize trs))
  end.

Fixpoint ntsize' (tr : nat_tree) : nat :=
  match tr with
  | NNode' _ Nil => S O
  | NNode' _ (Cons tr rest) => S (sum (Cons (ntsize' tr) (map ntsize' rest)))
  end.


Fixpoint ntsplice (tr1 tr2 : nat_tree) : nat_tree :=
  match tr1 with
  | NNode' n Nil => NNode' n (Cons tr2 Nil)
  | NNode' n (Cons tr rest) => NNode' n (Cons (ntsplice tr tr2) rest)
  end.

Lemma plus_S : forall n1 n2 : nat, plus n1 (S n2) = S (plus n1 n2).
  induction n1; crush.
Qed.

Hint Rewrite plus_S.

Theorem ntsize_ntsplice' : forall tr1 tr2 : nat_tree, ntsize' (ntsplice tr1 tr2) = plus (ntsize' tr2) (ntsize' tr1).
  induction tr1 using nat_tree_ind'; crush.
  induction ls; crush.
Qed.
  
Theorem ntsize_ntsplice : forall tr1 tr2 : nat_tree, ntsize (ntsplice tr1 tr2) = plus (ntsize tr2) (ntsize tr1).
  induction tr1 using nat_tree_ind'; crush.
  Restart.
  Hint Extern 1 (ntsize (match ?LS with Nil => _ | Cons _ _ => _ end) = _) => destruct LS; crush.
  induction tr1 using nat_tree_ind'; crush.
Qed.

Theorem true_neq_false : true <> false.
  red.
  intro H.
  Definition toProp (b : bool) := if b then True else False.
  change (toProp false).
  rewrite <- H.
  simpl.
  trivial.
Qed.

Theorem S_inj' : forall n m : nat, S n = S m -> n = m.
  intros n m H.
  change (pred (S n) = pred (S m)).
  rewrite H.
  reflexivity.
Qed.

Print False_ind.
  
  

                     
                                     
