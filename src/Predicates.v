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

(* Extra definitions to get coqdoc to choose the right fonts. *)

(* begin thide *)
Inductive unit := tt.
Inductive Empty_set := .
Inductive bool := true | false.
Inductive sum := .
Inductive prod := .
Inductive and := conj.
Inductive or := or_introl | or_intror.
Inductive ex := ex_intro.
Inductive eq := eq_refl.
Reset unit.
(* end thide *)
(* end hide *)

Print unit.

Print True.

Section Propositional.
  Variables P Q R : Prop.

  Theorem obvious : True.
    apply I.
  Qed.

  Theorem obivious' : True.
    constructor.
  Qed.

  Print False.

  Theorem Flase_imp : False -> 2 + 2 = 5.
    intro H.
    apply False_ind.
    trivial.
  Qed.

  Theorem False_imp' : False -> 2 + 2 = 5.
    destruct 1.
  Qed.

  Theorem arith_neq : 2 + 2 = 5 -> 9 + 9 = 835.
    intro H.
    exfalso.
    crush.
  Qed.

  Print not.

  Theorem arith_neq' : ~ (2 + 2 = 5).
    unfold not.
    crush.
  Qed.

  Print and.

  Theorem and_comm : P /\ Q -> Q /\ P.
    destruct 1.
    split.
    trivial.
    trivial.
  Qed.

  Definition and_comm_func : forall (P Q : Prop),  P /\ Q -> Q /\ P :=
    fun (P Q : Prop) (H0 : P /\ Q) =>

      match H0 with
      | conj P Q => conj Q P
      end.

  Theorem and_comm' : P /\ Q -> Q /\ P.
    apply and_comm_func.
  Qed.

  Definition or_comm_func : forall (P Q : Prop), P \/ Q -> Q \/ P :=
    fun (P Q : Prop) (H0 : P \/ Q) =>
      match H0 with
      | or_introl P => or_intror P
      | or_intror Q => or_introl Q
      end.

  Theorem or_comm : P \/ Q -> Q \/ P.
    apply or_comm_func.
  Qed.

  Theorem or_comm' : P \/ Q -> Q \/ P.
    tauto.
  Qed.

  Theorem arith_comm : forall ls1 ls2 : list nat,
      length ls1 = length ls2 \/ length ls1 + length ls2 = 6 -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
    intuition.
    rewrite app_length.
    tauto.
  Qed.

  Theorem arith_comm' : forall ls1 ls2 : list nat,
      length ls1 = length ls2 \/ length ls1 + length ls2 = 6 -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
    Hint Rewrite app_length.
    crush.
  Qed.
End Propositional.

Print ex. 

Inductive ex' (A : Type) (P : A -> Prop) : Prop :=
  ex_intro' : forall x, (P x -> ex' P).

Theorem exists1 : exists x : nat, x + 1 = 2.
  exists 1.
  reflexivity.
Qed.

Theorem very_trivial : 1 + 1 = 2.
  reflexivity.
Qed.
                                

Definition exists1_manual : ex (fun x : nat => x + 1 = 2) :=
  ex_intro (fun x : nat => x + 1 = 2) 1 very_trivial.

Theorem exists1' : exists x : nat, x + 1 = 2.
  apply exists1_manual.
Qed.

Theorem exists2' : forall n m : nat, (exists x : nat, n + x = m) -> n <= m.
  destruct 1.
  crush.
Qed.

Theorem exists2_subproof : forall n m x : nat, n + x = m -> n <= m.
  intros.
  crush.
Qed.

Definition exists2_manual_correct : forall n m : nat, (exists x : nat, n + x = m) -> n <= m :=
  (fun (local_subproof : forall n m x : nat, n + x = m -> n <= m) (n m : nat) (H : exists x : nat, n + x = m) =>
     match H with
     | ex_intro x H0 (*@ex_intro _ _ x H0*) => local_subproof n m x H0
     end) exists2_subproof.


(* Why the second is wrong? *)
(* Definition exists2_manual_wrong : forall n m : nat, (exists x : nat, n + x = m) -> n <= m := *)
(*   (fun (n m : nat) (H : exists x : nat, n + x = m) => *)
(*      match H with *)
(*      | ex_intro x H0 => exists2_subproof n m x H0 *)
(*      end). *)

Inductive isZero : nat -> Prop :=
| IsZero : isZero 0.

Theorem isZero_zero : isZero 0.
  constructor.
Qed.

Inductive isZero' (n : nat) : Prop :=
| IsZero_constr : isZero' n.

Print eq.

Inductive ex'' (A : Type) (P : A -> Prop) : Prop :=
| ex''_constr : forall x : A, P x -> ex'' P.

Inductive eq' (A : Type) (x : A) : A -> Prop :=
| eq_refl' : eq' x x.

Locate "=".

Theorem trivial1 : eq' 1 1.
  apply (eq_refl' 1).
Qed.

Theorem trivial2 : forall n : nat, eq' (S n) (S n).
  intros.
  apply (eq_refl' (S n)).
Qed.

Theorem trivial3' : forall n m, n = m -> S n = S m.
  intros.
  rewrite H.
  reflexivity.
Qed.

Theorem trivial3'_helper : forall n, S n = S n.
  intros.
  apply (eq_refl (S n)).
Qed.

Definition trivial3'' : forall n m, n = m -> S n = S m :=
  fun n m (H : n = m) =>
    eq_ind n (fun x => S n = S x) (eq_refl (S n)) m H.

(* I'm still confused about the how to do induction on inductive propositions *)

Theorem isZero_plus : forall n m : nat, isZero m -> n + m = n.
  destruct 1.
  crush.
Qed.

Theorem isZero_contra : isZero 1 -> False.
  inversion 1.

Qed.


Theorem isZero_contra' : isZero 1 -> 2 + 2 = 5.
  inversion 1.
Qed.

Check isZero_ind.

Inductive even : nat -> Prop :=
| EvenO : even 0
| EvenSS : forall n : nat, even n -> even (S (S n)).

Print even_ind.

Theorem even_O : even 0.
  constructor.
Qed.

Theorem even_4 : even 4.
  constructor; constructor; constructor.
Qed.

Hint Constructors even.

Theorem even_4' : even 4.
  auto.
Qed.

Theorem even_1_contra : even 1 -> False.
  inversion 1.
Qed.

Theorem even_3_contra : even 3 -> False.
  inversion 1.
  inversion H1.
Qed.

Theorem even_plus : forall n m, even n -> even m -> even (n + m).
  induction 1.
  simpl; trivial.
  intro; simpl; apply EvenSS; apply IHeven; trivial.
Qed.

Print even_ind.

Lemma even_contra' : forall n', even n' -> forall n, n' = S (n + n) -> False.
  induction 1; crush.
  destruct n; destruct n0; crush.
  apply (IHeven n0).
  rewrite H0.
  SearchRewrite (_ + S _).
  symmetry. apply plus_n_Sm.
  Restart.
  Hint Rewrite <- plus_n_Sm.
  induction 1; crush;
    match goal with
    | [H : S ?N = ?N0 + ?N0 |- _] => destruct N; destruct N0
    end; crush.
Qed.

Theorem even_contra : forall n, even (S (n + n)) -> False.
  intros; eapply even_contra'; eauto.
Qed.

Theorem even_contra'' : forall n, even (S (n + n)) -> False.
  intros. eapply even_contra'; eauto.
Qed.

Lemma even_contra_old_style : forall n, even (S (n + n)) -> False.
  intros. remember (S (n + n)) as n' in H.
  generalize dependent n.
  induction H.
  -
    intros. inversion Heqn'.
  -
    intros. 
    destruct n0.
    +
      inversion Heqn'.
    +
      inversion Heqn'.
      apply (IHeven n0).
      rewrite H1.
      symmetry. apply plus_n_Sm.
Qed.

    
    

  
