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

    
