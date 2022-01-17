
Require Import FunInd.
From Coq Require Import Arith Bool Ascii String ZArith.Int.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Require Import Coq.Program.Wf.
Require Import Coq.Arith.Plus.

Inductive singleES : Type :=
| bot
| emp
| singleton    
| cons      (es1: singleES) (es2: singleES)
| disj      (es1: singleES) (es2: singleES)
| kleene    (es: singleES)
| infity    (es: singleES)
| omega     (es: singleES).

Definition hypothesis : Type := list (singleES * singleES).

(*returns a set of hypothesis and the entailment validility*)
Definition result : Type := (hypothesis * bool).


Fixpoint compareEff (eff1 eff2: singleES): bool :=
match eff1, eff2 with
| bot, bot => true
| emp, emp => true
| singleton, singleton => true
| cons e1 e2, cons e3 e4 => compareEff e1 e3 && compareEff e2 e4
| disj e1 e2, disj e3 e4 => (compareEff e1 e3 && compareEff e2 e4) ||
                            (compareEff e1 e4 && compareEff e2 e3)
| kleene e1, kleene e2 => compareEff e1 e2
| infity e1, infity e2 => compareEff e1 e2
| omega e1, omega e2 => compareEff e1 e2
| _,_ => false
end.


Fixpoint normal (eff:singleES) :singleES :=
match eff with
   | cons bot  _  => bot
   | cons _ bot   => bot
   | cons emp e   => normal e
   | cons e emp   => normal e
   | cons e1 e2   =>  
    (
      match normal e1, normal e2 with 
      | emp, e   => e
      | e, emp   => e
      | bot, _   => bot
      | _, bot   => bot
      | _, _ => (cons (normal e1) (normal e2))
      end
    )
    
   | disj bot e   => normal e
   | disj e bot   => normal e
   | disj e1 e2   =>  
    (
      match normal e1, normal e2 with 
      | bot, e  => e
      | e, bot  => e
      | _, _ => (disj (normal e1) (normal e2))
      end
    )
   
   | kleene emp   => emp
   | kleene e     =>  
    (match normal e with 
    | emp => emp
    | _   =>(kleene (normal e))
    end)
   | _ => eff
end.

Fixpoint reoccurTRS (hy:hypothesis) (lhs rhs: singleES) : bool :=
match hy with
| [] => false
| (lhs', rhs')::xs => if compareEff (normal lhs) (normal lhs') &&  compareEff (normal rhs) (normal rhs') then true else reoccurTRS xs lhs rhs
end.

Fixpoint nullable (eff:singleES): bool :=
match eff with
| emp          => true
| disj e1 e2   => nullable e1 || nullable e2
| cons e1 e2   => nullable e1 && nullable e2
| kleene _     => true
| infity _     => true
| _           => false
end.

Fixpoint infinitiable (eff:singleES): bool :=
match eff with
| disj e1 e2   => infinitiable e1 || infinitiable e2
| cons e1 e2   => infinitiable e1 && infinitiable e2
| infity _     => true
| omega _      => true
| _ => false 
end.




Inductive fstT : Type := one.

Fixpoint fst (eff:singleES): list fstT  :=
match eff with
| bot          => []
| emp          => []
| singleton    => [one]
| disj e1 e2   => fst e1 ++ fst e2
| cons e1 e2   => if nullable e1 then fst e1 ++ fst e2
                  else fst e1
| kleene e     => fst e
| infity e     => fst e
| omega e      => fst e
end.

Definition entailFst (f1 f2 : fstT) : bool :=
  match f1, f2 with 
  | one , one => true 
  end.


Fixpoint derivitive (eff:singleES) (f:fstT) : singleES :=
match eff with
| bot          => bot
| emp          => bot
| singleton    => match entailFst f (one)  with
                  | true => emp 
                  | flase => bot
end
| cons e1 e2   => match nullable e1 with
                  | true => disj (cons (derivitive e1 f) e2)  (derivitive e2 f)
                  | flase => cons (derivitive e1 f) e2
end
| disj e1 e2   => disj (derivitive e1 f) (derivitive e2 f)
| kleene e     => cons (derivitive e f) eff
| infity e     => cons (derivitive e f) eff
| omega e     => cons (derivitive e f) eff
end.



Definition neg (v:bool): bool :=
match v with
| true => false
| false => true
end.


Local Open Scope nat_scope.

Fixpoint entailment (n:nat) (hy:hypothesis) (lhs rhs: singleES): bool :=
  match n with 
  | O => true  
  | S n' =>
    (
      match nullable lhs, nullable rhs with 
      | true , false => false 
      | _, _ =>  
        (match infinitiable lhs, infinitiable rhs with 
        | true, false => false
        | _, _ =>  
          (
          match reoccurTRS hy lhs rhs with 
          | true => true 
          | false => 
    let fst := fst lhs in
    let subTrees := List.map (fun f =>
        let der1 := (derivitive lhs f) in
        let der2 := (derivitive rhs f) in
        entailment (n') ((lhs, rhs) :: hy) der1 der2
        ) fst in
    List.fold_left (fun acc a => acc && a) subTrees true
          end)
        end)
      end
    )
  end.

Definition entailmentShell (n:nat) (lhs rhs: singleES) : bool :=
  entailment n [] lhs rhs.



Lemma bot_entails_everything:
  forall (rhs: singleES) , 
    entailment 1 [] bot rhs = true.
Proof.
  intro rhs.
  intros. unfold entailment. fold entailment.
  unfold nullable. unfold reoccurTRS. unfold derivitive. unfold normal.
  unfold fst. unfold map. unfold fold_left. reflexivity.
Qed.

Lemma emp_entails_nullable:
  forall (rhs: singleES) (hy:hypothesis), 
    nullable rhs = true ->
    entailment 1 [] emp rhs = true.
Proof. 
  intro rhs.
  intro. intro.
  unfold entailment. fold entailment. unfold nullable. fold nullable.
  destruct (nullable rhs) as [].
  - unfold reoccurTRS. unfold derivitive. unfold normal.
    unfold fst. unfold map. unfold fold_left. reflexivity.
  - discriminate H.
Qed.




Lemma bool_trans:
  forall (a b c: bool), a = b  -> a = c -> b = c.
Proof.
  intro a. induction a. 
  - intro b. induction b.
    + intro c. induction c.
      * intros. reflexivity.
      * intros. discriminate H0.
    + intro c. induction c.
      * intros. discriminate H.
      * intros. reflexivity. 
  - intro b. induction b.
    + intro c. induction c.
      * intros. discriminate H.
      * intros. discriminate H.
    + intro c. induction c.
      * intros. discriminate H0. 
      * intros. reflexivity.
Qed. 

Compute (entailment 1 [] singleton bot).

Lemma singlon_entaill_rhs_then_der_rhs_nullable n:
  forall (rhs:singleES) (f:fstT),
    entailment n [] singleton rhs = true -> 
      entailment n [] emp (derivitive rhs f) = true.
Proof.
Admitted. 


Theorem soundnessTRS: 
  forall (lhs: singleES)  (rhs: singleES) (f:fstT), exists n, 
    entailment n [] lhs rhs = true -> 
      entailment n [] (derivitive lhs f) (derivitive rhs f) = true .
Proof.
  intro lhs. induction lhs.
  - intros. unfold derivitive. fold derivitive. exists 1. intro.
    exact (bot_entails_everything (derivitive rhs f)). 
  - intros. unfold derivitive. fold derivitive. exists 1. intro.
    exact (bot_entails_everything (derivitive rhs f)).
  - intros.
    induction f. simpl. exists 2.
    exact (singlon_entaill_rhs_then_der_rhs_nullable 2 rhs one).
  - intros. induction f. simpl. 
    induction lhs1.
    + exists 2. simpl. intro. reflexivity.
    + exists 2. induction lhs2.
      * simpl. intro. reflexivity.
      * simpl. case_eq (nullable rhs).
        -- intros. reflexivity.
        -- intros. discriminate H0.
      * unfold nullable. unfold entailment. fold entailment.
      (* STOP HERE *)
      
      case_eq(nullable (derivitive rhs one)).
        -- simpl. intros. simpl. exact H0. 
        --  intros. discriminate H0.
      * case_eq(nullable (derivitive rhs one)).
    
    simpl. 
      * simpl.  induction rhs. 
        -- simpl. exists 2. simpl. intro. 

  - intros. induction f. simpl. 
    induction lhs1. induction lhs2.
    + simpl. exists 1. intro. simpl. reflexivity.  
    + simpl. exists 1. intro. simpl. reflexivity.  
    + simpl. exists 2. simpl.  
      case_eq (nullable (derivitive rhs one)).
      * intros. reflexivity.
      * intros. discriminate H0.
    + simpl.   
        
    
    
    unfold entailment. 

  - intros. 
    unfold derivitive. fold derivitive. exists 2. 
    intro H. 
    assert (H1:= (singleton_entails_rhs_imply_nullable_rhs rhs s H)).
    + induction f.
      * unfold entailFst.
        case_eq ((s0 =? s)%string ).
        -- intros.  unfold entailment. unfold nullable. fold nullable.
           Search (String.eqb).
           assert (H_temp := String.eqb_eq s0 s).
           destruct H_temp as [Hn Hm].
           assert (equla := Hn H0).
Abort.
(*
           apply equla in H1.
           rewrite  in equla.
           Check (Hn H0).
           Check (String.eqb_eq s0 s H0).
        
        rewrite (String.eqb s0 s).
    unfold entailment. fold entailment. unfold nullable. fold nullable.
    unfold reoccurTRS.
    case_eq (nullable (derivitive rhs f)). intros.
    + unfold derivitive. fold derivitive. unfold fst. unfold map.
      unfold  fold_left. reflexivity.


    Search (Nat.eqb).
    

    
    intro H. 
    


Qed.

Definition eff1 : singleES := emp.
Definition eff2 : singleES := {{[("A", one)]}}.
Definition eff3 : singleES := waiting "A".

Compute (entailmentShell eff3 eff2).

Compute (entailmentShell eff2 eff3).


Compute (entailmentShell (kleene eff2) (kleene eff2)).

*)
