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

Definition bad : unit := tt.

Set Implicit Arguments.
Set Asymmetric Patterns.
(* end hide *)


Section stream.
  Variable A : Type.
  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
End stream.

CoFixpoint zeros : stream nat := Cons 0 zeros.

CoFixpoint trues_falses : stream bool := Cons true falses_trues
with falses_trues : stream bool := Cons false trues_falses.

Fixpoint approx A (s : stream A) (n : nat) : list A :=
  match n with
  | O => nil
  | S n' =>
    match s with
    | Cons h t => h :: approx t n'
    end
  end.

Eval simpl in approx zeros 10.

Eval simpl in approx trues_falses 10.

Section map.
  Variables A B : Type.
  Variable f : A -> B.
  CoFixpoint map (s : stream A) : stream B :=
    match s with
    | Cons h t => Cons (f h) (map t)
    end.
End map.

Section interleave.
  Variable A : Type.
  CoFixpoint interleave (s1 s2 : stream A) : stream A :=
    match s1, s2 with
    | Cons h1 t1, Cons h2 t2 => Cons h1 (Cons h2 (interleave t1 t2))
    end.
End interleave.

(* Section map'. *)
(*   Variables A B : Type. *)
(*   Variable f : A -> B. *)
(*   CoFixpoint map' (s : stream A) : stream B := *)
(*     match s with *)
(*     | Cons h t => interleave (Cons (f h) (map' t)) (Cons (f h) (map' t)) *)
(*     end. *)
  
Definition tl A (s : stream A) : stream A :=
  match s with
  | Cons _ s' => s'
  end.

(* CoFixpoint bad : stream nat := tl (Cons 0 bad). *) 
(* The restrictions of Coq on coinductive types and cofix function definitions. As coinductive is used to produce infinite data structure, a cofix function must produce a result through a constructor for a coinductive type. Coq's restriction is so tight that any indirections may fail Coq's check *)

CoFixpoint ones : stream nat := Cons 1 ones.
Definition ones' := map S zeros.

Theorem ones_eq : ones = ones'.
Abort.

Section stream_eq.
  Variable A : Type.
  CoInductive stream_eq : stream A -> stream A -> Prop :=
  | Stream_eq : forall h t1 t2, stream_eq t1 t2 -> stream_eq (Cons h t1) (Cons h t2).
End stream_eq.

Theorem ones_eq : stream_eq ones ones'.
  cofix ones_eq.
  assumption.
  Undo.
  simpl.
Abort.

Definition frob A (s : stream A) : stream A :=
  match s with
  | Cons h t => Cons h t
  end.

Theorem frob_eq : forall A (s : stream A), s = frob s.
  destruct s. simpl. reflexivity.
Qed.

Theorem ones_eq : stream_eq ones ones'.
  cofix ones_eq.
  rewrite (frob_eq ones).
  rewrite (frob_eq ones').
  simpl.
  constructor.
  assumption.
Qed.

Theorem ones_eq' : stream_eq ones ones'.
  cofix ones_eq'; crush.
Abort.

Definition hd A (s : stream A) : A :=
  match s with
  | Cons x _ => x
  end.

Section stream_eq_coind.
  Variable A : Type.
  Variable R : stream A -> stream A -> Prop.
  Hypothesis Cons_case_hd : forall s1 s2, R s1 s2 -> hd s1 = hd s2.
  Hypothesis Cons_case_tl : forall s1 s2, R s1 s2 -> R (tl s1) (tl s2).

  Theorem stream_eq_coind : forall s1 s2, R s1 s2 -> stream_eq s1 s2.
    cofix stream_eq_coind; destruct s1; destruct s2; intro.
    generalize (Cons_case_hd H); intro Heq; simpl in Heq; rewrite Heq.
    constructor.
    apply stream_eq_coind.
    apply (Cons_case_tl H).
  Qed.
End stream_eq_coind.

Print stream_eq_coind.

Theorem ones_eq'' : stream_eq ones ones'.
  apply (stream_eq_coind (fun s1 s2 => s1 = ones /\ s2 = ones')); crush.
Qed.

Theorem ones_eq_manual : stream_eq ones ones'.
  cofix ones_eq_manual.
  apply (stream_eq_coind (fun s1 s2 => s1 = ones /\ s2 = ones')).
  -
    intros. destruct H. rewrite H. rewrite H0. reflexivity.
  -
    intros. destruct H. rewrite H. rewrite H0. split.
    +
      reflexivity.
    +
      reflexivity.
  -
    split. reflexivity. reflexivity.
Qed.

Require Import Arith.
Print fact.

CoFixpoint fact_slow' (n : nat) : stream nat := Cons (fact n) (fact_slow' (S n)).
Definition fact_slow := fact_slow' 1.

CoFixpoint fact_iter' (n acc : nat) : stream nat := Cons acc (fact_iter' (S n) (n * acc)).
Definition fact_iter := fact_iter' 2 1.

Eval simpl in approx fact_iter 5.
Eval simpl in approx fact_slow 5.

(* Lemma fact_def : forall x n, *)
(*     fact_iter' x (fact n * S n) = fact_iter' x (fact (S n)). *)
(*   simpl. intros. f_equal. ring. *)
(* Qed. *)

(* Hint Resolve fact_def. *)

Lemma fact_eq' : forall n, stream_eq (fact_iter' (S n) (fact n)) (fact_slow' n).
  intros; apply (stream_eq_coind (fun s1 s2 => exists n, s1 = fact_iter' (S n) (fact n) /\ s2 = fact_slow' n)); crush; eauto.
Qed.

Theorem fact_eq : stream_eq fact_iter fact_slow.
  apply fact_eq'.
Qed.

Lemma fact_eq_manual : forall n, stream_eq (fact_iter' (S n) (fact n)) (fact_slow' n).
  intros.
  apply (stream_eq_coind (fun s1 s2 => exists n, s1 = (fact_iter' (S n) (fact n)) /\ s2 = (fact_slow' n))).
  -
    intros. destruct H. destruct H. rewrite H. rewrite H0. reflexivity.
  -
    intros. destruct H. destruct H. rewrite H. rewrite H0.
    exists (S x). split.
    +
      simpl. reflexivity.
    +
      simpl. reflexivity.
  -
    exists n. split. reflexivity. reflexivity.
Qed.

Definition var := nat.

Definition vars := var -> nat.

Definition set (vs : vars) (v : var) (n : nat) : vars :=
  fun v' => if beq_nat v v' then n else vs v.

Inductive exp : Set :=
| Const : nat -> exp
| Var : var -> exp
| Plus : exp -> exp -> exp.

Fixpoint evalExp (vs : vars) (e : exp) : nat :=
  match e with
  | Const n => n
  | Var v => vs v
  | Plus e1 e2 => evalExp vs e1 + evalExp vs e2
  end.

Inductive cmd : Set :=
| Assign : var -> exp -> cmd
| Seq : cmd -> cmd -> cmd
| While : exp -> cmd -> cmd.

CoInductive evalCmd : vars -> cmd -> vars -> Prop :=
| EvalAssign : forall vs v e,
    evalCmd vs (Assign v e) (set vs v (evalExp vs e))
| EvalSeq : forall c1 c2 vs1 vs2 vs3,
    evalCmd vs1 c1 vs2 ->
    evalCmd vs2 c2 vs3 ->
    evalCmd vs1 (Seq c1 c2) vs3
| EvalWhileFalse : forall vs e c,
    evalExp vs e = 0 ->
    evalCmd vs (While e c) vs
| EvalWhileTrue : forall vs1 vs2 vs3 e c,
    evalExp vs1 e <> 0 ->
    evalCmd vs1 c vs2 ->
    evalCmd vs2 (While e c) vs3 ->
    evalCmd vs1 (While e c) vs3.
                      
Section evalCmd_ind.
  Variable R : vars -> cmd -> vars -> Prop.

  Hypothesis AssignCase : forall v e vs1 vs2, R vs1 (Assign v e) vs2 -> vs2 = set vs1 v (evalExp vs1 e).

  Hypothesis SeqCase : forall vs1 vs3 c1 c2, R vs1 (Seq c1 c2) vs3 -> exists vs2, R vs1 c1 vs2 /\ R vs2 c2 vs3.

  Hypothesis WhileCase : forall vs1 vs3 e c, R vs1 (While e c) vs3 -> (evalExp vs1 e = 0 /\ vs1 = vs3) \/ (exists vs2,  evalExp vs1 e <> 0 /\ R vs1 c vs2 /\ R vs2 (While e c) vs3).

  Theorem evalCmd_ind : forall vs1 c vs2, R vs1 c vs2 -> evalCmd vs1 c vs2.
    cofix evalCmd_ind.
    intros. destruct c.
    -
      apply AssignCase in H. rewrite H. apply EvalAssign.
    -
      apply SeqCase in H. destruct H. destruct H. apply EvalSeq with x.
      +
        apply evalCmd_ind. assumption.
      +
        apply evalCmd_ind. assumption.
    -
      apply WhileCase in H. destruct H.
      +
        destruct H. rewrite H0. apply EvalWhileFalse. rewrite <- H0. assumption.
      +
        destruct H.  destruct H. destruct H0. apply EvalWhileTrue with x.
        *
          assumption.
        *
          apply evalCmd_ind in H0. assumption.
        *
          apply evalCmd_ind in H1. assumption.
  Qed.
End evalCmd_ind.


Fixpoint optExp (e : exp) : exp :=
  match e with
  | Plus (Const 0) e => optExp e
  | Plus e1 e2 => Plus (optExp e1) (optExp e2)
  | _ => e
  end.

Eval simpl in (optExp (optExp (Plus (Plus (Const 0) (Const 0)) (Const 5)))).

Fixpoint optCmd (c : cmd) : cmd :=
  match c with
  | Assign v e => Assign v (optExp e)
  | Seq c1 c2 => Seq (optCmd c1) (optCmd c2)
  | While e c => While (optExp e) (optCmd c)
  end.

Lemma optExp_correct : forall vs e, evalExp vs e = evalExp vs (optExp e).
  intros. generalize dependent vs.
  induction e.
  -
    intros. reflexivity.
  -
    intros. reflexivity.
  -
    intros. simpl.
    destruct e1.
    +
      destruct n.
      *
        simpl. apply (IHe2 vs).
      *
        simpl. rewrite IHe2. reflexivity.
    +
      simpl. rewrite IHe2. reflexivity.
    +
      crush.
Qed.

Lemma optCmd_correct1 : forall vs1 c vs2, evalCmd vs1 (optCmd c) vs2 -> evalCmd vs1 c vs2.
  intros. apply (evalCmd_ind (fun vs1 c vs2 => evalCmd vs1 (optCmd c) vs2)).
  -
    intros. simpl in H0. inversion H0. rewrite <- optExp_correct. reflexivity.
  -
    intros. simpl in H0. inversion H0. exists vs5. split.
    +
      assumption.
    +
      assumption.
  -
    intros. simpl in H0. inversion H0.
    +
      left. split. rewrite optExp_correct. assumption. reflexivity.
    +
      right. exists vs5. split.
      *
        rewrite optExp_correct. assumption.
      *
        split. { assumption. } { assumption. }
  -
    assumption.
Qed.

Lemma optCmd_correct2_helper : forall vs1 c vs2, (exists c', c = optCmd c' /\ evalCmd vs1 c' vs2) -> evalCmd vs1 c vs2.
  intros. apply (evalCmd_ind (fun vs1 c vs2 => exists c', c = optCmd c' /\ evalCmd vs1 c' vs2)).
  -
    intros. destruct H0. destruct H0. destruct x.
    +
      simpl in H0. injection H0. intros. inversion H1.
      rewrite H3. rewrite H2. rewrite <- optExp_correct. reflexivity.
    +
      simpl in H0. inversion H0.
    +
      simpl in H0. inversion H0.
  -
    intros. destruct H0. destruct H0. destruct x.
    +
      simpl in H0. inversion H0.
    +
      simpl in H0. injection H0. intros. inversion H1.
      exists vs5. split.
      *
        exists x1. split. assumption. assumption.
      *
        exists x2. split. assumption. assumption.
    +
      simpl in H0. inversion H0.
  -
    intros. destruct H0. destruct H0. destruct x.
    +
      simpl in H0. inversion H0.
    +
      simpl in H0. inversion H0.
    +
      simpl in H0. injection H0. intros.
      inversion H1.
      *
        left. split. rewrite H3. rewrite <- optExp_correct. assumption. reflexivity.
      *
        right. exists vs5. split.
        { rewrite H3. rewrite <- optExp_correct. assumption. }
        { split.
          { exists x. split. assumption. assumption. }
          { exists (While e0 x). split.
           { assumption. }
           { assumption. }}}
  -
    assumption.
Qed.                    

Lemma optCmd_correct2 : forall vs1 c vs2, evalCmd vs1 c vs2 -> evalCmd vs1 (optCmd c) vs2.
  intros.
  apply (optCmd_correct2_helper ).
  exists c. split. reflexivity. assumption.
Qed.

      
Lemma optCmd_correct : forall vs1 c vs2, evalCmd vs1 c vs2 <-> evalCmd vs1 (optCmd c) vs2.
  intros. split. apply optCmd_correct2. apply optCmd_correct1.
Qed.

      
          
          

  
    
      
    

