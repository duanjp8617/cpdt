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


Definition pred_strong3 (s : {n : nat | n > 0}) : {m : nat | proj1_sig s = S m} :=
  match s return {m : nat | proj1_sig s = S m} with
  | exist 0 pf => match zgtz pf with end
  | exist (S n') _ => exist _ n' (eq_refl _)
  end.

Eval compute in pred_strong3 (exist _ 2 two_gt0).

Extraction pred_strong3.

Definition pred_strong4 : forall n : nat, n > 0 -> {m : nat | n = S m}.
  refine (fun n =>
            match n with
            | 0 => fun _ => False_rec _ _
            | S n' => fun _ => exist _ n' _
            end).
  -
    inversion g.
  -
    reflexivity.
Defined.

Extraction pred_strong4.

Definition pred_strong4' : forall n : nat, n > 0 -> {m : nat | n = S m}.
  refine (fun n =>
            match n with
            | 0 => fun _ => False_rec _ _
            | S n' => fun _ => exist _ n' _
            end); abstract crush.
Defined.

Print pred_strong4'.

Eval compute in pred_strong4 (two_gt0).

Print sumbool.

Definition eq_nat_dec : forall n m : nat, sumbool (n = m) (n <> m).
  refine (fix F (n m : nat) : sumbool (n = m) (n <> m) :=
            match n, m with
            | 0, 0 => left _ _
            | S n', S m' => if F n' m' then left _ _ else right _ _
            | _, _ => right _ _
            end).
  -
    reflexivity.
  -
    unfold not. intro H; inversion H.
  -
    unfold not; intro H; inversion H.
  -
    rewrite e; reflexivity.
  -
    unfold not; intro H; inversion H; apply n0; assumption.
Defined.

Eval compute in eq_nat_dec 2 2.

Eval compute in eq_nat_dec 2 3.

Extraction eq_nat_dec.

Section In_dec.
  Variable A : Set.
  Variable A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  Definition In_dec : forall (x : A) (ls : list A), {In x ls} + {~ In x ls}.
    refine (fix f (x : A) (ls : list A) :=
              match ls with
              | nil => right _ _
              | y :: ls' =>
                if A_eq_dec x y
                then
                  left _ _
                else
                  if f x ls'
                  then left _ _
                  else right _ _
              end                
           ).
    -
      intros H. unfold In in H. assumption.
    -
      unfold In. left. rewrite e. reflexivity.
    -
      simpl. right. assumption.
    -
      simpl. intro H. destruct H.
      apply n; symmetry; assumption.
      apply n0; assumption.
  Defined.
End In_dec.

Eval compute in In_dec eq_nat_dec 2 (1 :: 2 :: nil).

Eval compute in In_dec eq_nat_dec 3 (1 :: 2 :: nil).

Extraction In_dec.

Inductive maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x : A, P x -> maybe P.

Definition pred_strong7 : forall n : nat, maybe (fun m : nat => n = S m).
  refine (fun (n : nat) =>
            match n return maybe (fun m : nat => n = S m) with
            | 0 => Unknown _
            | S n' => Found _ _ _
            end              
         ).
  trivial.
Qed.

Eval compute in pred_strong7 2.

Eval compute in pred_strong7 0.
  
Print sumor.

Extraction pred_strong7.

Definition pred_strong8 : forall n : nat, sumor (sig (fun m : nat => n = S m)) (n = 0).
  refine (fun n : nat =>
            match n return sumor (sig (fun m : nat => n = S m)) (n = 0) with
            | 0 => inright _ _
            | S n' => inleft _ (exist _ n' _)
            end
         ); repeat reflexivity.
Qed.

Eval compute in pred_strong8 2.

Eval compute in pred_strong8 0.


Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown _).
Notation "[| x |]" := (Found _ x _).

(* Notation "x <- e1 ; e2" := (match e1 with *)
(*                              | Unkown => ?? *)
(*                              | Found x _ => e2 *)
(*                             end) *)
(* (right associativity, at level 60). *)

Notation "x <- e1 ; e2" := (match e1 with
                            | Unknown => ??
                            | Found x _ => e2
                            end)
                             (right associativity, at level 60).

Definition double_pred : forall n1 n2 : nat, {{ p | n1 = S (fst p) /\ n2 = S (snd p) }}.
  refine (fun n1 n2 =>
            m1 <- pred_strong7 n1;
            m2 <- pred_strong7 n2;
            [| (m1, m2) |]).
  tauto.
Qed.

Definition double_pred': forall n1 n2 : nat, maybe (fun p => n1 = S (fst p) /\ n2 = S (snd p)).
  refine (fun n1 n2 =>
            match pred_strong7 n1 with
            | Unknown => Unknown _
            | Found m1 _ => match pred_strong7 n2 with
                            | Unknown => Unknown _
                            | Found m2 _ => Found _ (m1, m2) _
                            end
            end).
  auto.
Qed.


Notation "x <- e1 ; e2" :=
  (match e1 with
   | inright _ => inright _ _
   | inleft (exist x _) => e2
   end)
    (right associativity, at level 60).

Definition double_pred'' : forall n1 n2, sumor (sig (fun p => n1 = S (fst p) /\ n2 = S (snd p))) (n1 = 0 \/ n2 = 0).
  refine (fun n1 n2 =>
            m1 <- pred_strong8 n1;
            m2 <- pred_strong8 n2;
            (inleft _ (exist _ (m1, m2) _))
         ).
  -
    auto.
  -
    auto.
  -
    auto.
Qed.

Inductive exp : Set :=
| Nat : nat -> exp
| Plus : exp -> exp -> exp
| Bool : bool -> exp
| And : exp -> exp -> exp.

Inductive type : Set := | TNat : type | TBool : type.

Inductive hasType : exp -> type -> Prop :=
| HtNat : forall n : nat, hasType (Nat n) TNat
| HtPlus : forall e1 e2 : exp, hasType e1 TNat -> hasType e2 TNat -> hasType (Plus e1 e2) TNat
| HtBool : forall b : bool, hasType (Bool b) TBool
| HtAnd : forall e1 e2 : exp, hasType e1 TBool -> hasType e2 TBool -> hasType (And e1 e2) TBool.

Definition eq_type_dec : forall t1 t2 : type, sumbool (t1 = t2) (t1 <> t2).
  refine (fun t1 t2 : type =>
            match t1, t2 with
            | TNat, TNat => left _ _
            | TBool, TBool => left _ _
            | _, _ => right _ _
            end).
  auto. intro H; inversion H. intro H; inversion H. auto.
Qed.

Notation "x <- e1 ; e2" := (match e1 with
                            | Unknown => ??
                            | Found x _ => e2
                            end)
                             (right associativity, at level 60).

Notation "e1 ;; e2" := (if e1 then e2 else Unknown _) (right associativity, at level 60).

Definition typeCheck : forall e : exp, maybe (fun t : type => hasType e t).
  refine (fix f (e : exp) :=
            match e with
            | Nat _ => Found _ (TNat) _
            | Plus e1 e2 =>
              t1 <- f e1;
              t2 <- f e2;
              eq_type_dec t1 TNat;;
              eq_type_dec t2 TNat;;
              Found _ TNat _
            | Bool _ => Found _ (TBool) _
            | And e1 e2 =>
              t1 <- f e1;
              t2 <- f e2;
              eq_type_dec t1 TBool;;
              eq_type_dec t2 TBool;;
              Found _ TBool _
            end
         ).
  -
    constructor.
  -
    constructor. rewrite e0 in h. assumption. rewrite e3 in h0. assumption.
  -
    constructor.
  -
    constructor. rewrite e0 in h. assumption. rewrite e3 in h0. assumption.
Qed.

Definition typeCheck' : forall e : exp, maybe (fun t : type => hasType e t).
  refine (fix f (e : exp) :=
            match e with
            | Nat _ => Found _ (TNat) _
            | Plus e1 e2 =>
              t1 <- f e1;
              t2 <- f e2;
              (match t1 with               
               | TNat => match t2 with
                         | TNat => Found _ (TNat) _
                         | _ => Unknown _
                         end
               | _ => Unknown _
               end)
            | Bool _ => Found _ (TBool) _
            | And e1 e2 =>
              t1 <- f e1;
              t2 <- f e2;
              (match t1 with
               | TBool => match t2 with
                          | TBool => Found _ (TBool) _
                          | _ => Unknown _
                          end
               | _ => Unknown _
               end)
            end).
  -
    constructor.
  -
    constructor.
    (* We are missing some important hypothesises here, because the Coq doesn't recognize 
the type of the match result. We should provide hints to the match, but I don't how to do it *)
Abort.

Eval compute in typeCheck (Nat 0).

Extraction typeCheck.
    

Notation "e1 ;; e2" := (if e1 then e2 else inright _  _) (right associativity, at level 60).


Notation "x <- e1 ; e2" :=
  (match e1 with
   | inright _ => inright _ _
   | inleft (exist x _) => e2
   end)
    (right associativity, at level 60).

Theorem helper : forall e t1, hasType e t1 -> forall t2, hasType e t2 -> t1 = t2.
  induction 1; crush.
  -
    inversion H. reflexivity.
  -
    inversion H1. reflexivity.
  -
    inversion H. reflexivity.
  -
    inversion H1. reflexivity.
Qed.


Definition typeCheckSumor : forall e : exp, sumor (sig (fun t => hasType e t))  (forall t, ~ (hasType e t)).
  refine (fix f (e : exp) :=
            match e with
            | Nat _ => inleft _ (exist _ TNat _)
            | Plus e1 e2 =>
              t1 <- f e1;
              t2 <- f e2;
              eq_type_dec t1 TNat;;
              eq_type_dec t2 TNat;;
              inleft _ (exist _ TNat _)
            | Bool _ => inleft _ (exist _ TBool _)
            | And e1 e2 =>
              t1 <- f e1;
              t2 <- f e2;
              eq_type_dec t1 TBool;;
              eq_type_dec t2 TBool;;
              inleft _ (exist _ TBool _)
            end
         ).
  -
    constructor.
  -
    constructor. rewrite e0 in h. assumption. rewrite e3 in h0. assumption.
  -
    unfold not. intros. inversion H. apply (helper  h0) in H4. apply n in H4. assumption.
  -
    unfold not. intros. inversion H. apply (helper h) in H2. apply n in H2. assumption.
  -
    unfold not. intros. inversion H. apply n in H4. assumption.
  -
    unfold not. intros. inversion H. apply n in H2. assumption.
  -
    constructor.
  -
    constructor. rewrite e0 in h. assumption. rewrite e3 in h0. assumption.
  -
    unfold not. intros. inversion H. apply (helper h0) in H4. apply n in H4. assumption.
  -
    unfold not. intros. inversion H. apply (helper h) in H2. apply n in H2. assumption.
  -
    unfold not. intros. inversion H. apply n in H4. assumption.
  -
    unfold not. intros. inversion H. apply n in H2. assumption.
Qed.

    
                 
                             
    
    
    
              

    
    
              
