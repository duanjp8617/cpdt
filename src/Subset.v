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

Require Extraction.

Set Implicit Arguments.
Set Asymmetric Patterns.
(* end hide *)

Print pred.

Extraction pred.

Lemma zgtz' : 0 > 0 -> False.
  unfold gt. unfold lt. intros.
  inversion H.
Qed.

Lemma zgtz : 0 > 0 -> False.
  crush.
Qed.

Definition pred_strong1 (n : nat) : n > 0 -> nat :=
  match n with
  | O => fun pf : 0 > 0 => match zgtz pf with end
  | S n' => fun _ => n'
  end.


Theorem two_gt0 : 2 > 0.
  repeat constructor.
Qed.

Eval compute in pred_strong1 two_gt0.

(* Definition pred_strong1' (n : nat) (pf : n > 0) : nat := *)
(*   match n with *)
(*   | O => match zgtz pf with end *)
(*   | S n' => n' *)
(*   end. *)

Definition pred_strong1' (n : nat) : n > 0 -> nat :=
  match n return n > 0 -> nat with
  | O => fun pf : 0 > 0 => match zgtz pf with end
  | S n' => fun _ => n'
  end.

Extraction pred_strong1.

Print sig.

Definition pred_strong2 (s : sig (fun n : nat => n > 0) ) : nat :=
  match s with
  | exist O pf => match zgtz pf with end
  | exist (S n') _ => n'
  end.

Eval compute in pred_strong2 (exist _ 2 two_gt0).

Extraction pred_strong2.



                       
