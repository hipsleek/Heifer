Module AST.

Require Import FunInd.
From Coq Require Import Arith Bool Ascii String ZArith.Int.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Require Import Coq.Program.Wf.
Require Import Coq.Arith.Plus.

Inductive contEff : Type :=
| bot
| emp
| wildcard
| stop
| singleton (s: string)
| not       (s:string)
| cons      (es1: contEff) (es2: contEff)
| disj      (es1: contEff) (es2: contEff)
| kleene    (es: contEff).


Definition hypothesis : Type := list (contEff * contEff).

(*returns a set of hypothesis and the entailment validility*)
Definition result : Type := (hypothesis * bool).

Fixpoint leftHy' (n:nat) (records : hypothesis) : nat :=
match records with 
  | nil => n
  | x::xs => (leftHy' (n-1) xs)
end.


Fixpoint compareEff (eff1 eff2: contEff): bool :=
match eff1, eff2 with
| bot, bot => true
| emp, emp => true
| stop, stop => true
| wildcard, wildcard => true
| singleton s1, singleton s2 => if eqb s1 s2 then true else false
| not s1, not s2 => if eqb s1 s2 then true else false
| cons e1 e2, cons e3 e4 => compareEff e1 e3 && compareEff e2 e4
| disj e1 e2, disj e3 e4 => (compareEff e1 e3 && compareEff e2 e4) ||
                            (compareEff e1 e4 && compareEff e2 e3)
| kleene e1, kleene e2 => compareEff e1 e2
| _,_ => false
end.


Fixpoint normal (eff:contEff) :contEff :=
match eff with
   | cons bot  _  => bot
   | cons _ bot   => bot
   | cons stop _  => emp
   | cons emp e   => normal e
   | cons e emp   => normal e
   | cons e1 e2   =>  
    (
      match normal e1, normal e2 with 
      | emp, e   => e
      | e, emp   => e
      | bot, _   => bot
      | _, bot   => bot
      | stop, e  => emp 
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
      | stop, e  =>  disj emp e
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

Fixpoint reoccurTRS (hy:hypothesis) (lhs rhs: contEff) : bool :=
match hy with
| [] => false
| (lhs', rhs')::xs => if compareEff (normal lhs) (normal lhs') &&  compareEff (normal rhs) (normal rhs') then true else reoccurTRS xs lhs rhs
end.

Fixpoint nullable (eff:contEff): bool :=
match eff with
| bot          => false
| emp          => true
| singleton _  => false
| not   _      => false 
| stop         => true
| wildcard     => false
| disj e1 e2   => nullable e1 || nullable e2
| cons e1 e2   => nullable e1 && nullable e2
| kleene _     => true
end.

Inductive fstT : Type := one (s:string) | zero (s:string) | any.

Fixpoint fst (eff:contEff): list fstT  :=
match eff with
| bot          => []
| emp          => []
| singleton i  => [(one i)]
| wildcard     => [any]
| stop         => []
| not i        => [(zero i)] 
| disj e1 e2   => fst e1 ++ fst e2
| cons e1 e2   => if nullable e1 then fst e1 ++ fst e2
                  else fst e1
| kleene e     => fst e
end.

Definition entailFst (f1 f2 : fstT) : bool :=
  match f1, f2 with 
  | one s1, one s2 => eqb s1 s2 
  | zero s1, zero s2 => eqb s1 s2 
  | _, any => true
  | _, _ => false 
  end.


Fixpoint derivitive (eff:contEff) (f:fstT) : contEff :=
match eff with
| bot          => bot
| emp          => bot
| singleton i  => match entailFst f (one i)  with
                  | true => emp 
                  | flase => bot
end
| not   i      => match entailFst f (zero i) with
                  | true => emp 
                  | false =>bot
end 
| wildcard     => emp 
| stop         => bot
| cons e1 e2   => match nullable e1 with
                  | true => disj (cons (derivitive e1 f) e2)  (derivitive e2 f)
                  | flase => cons (derivitive e1 f) e2
end
| disj e1 e2   => disj (derivitive e1 f) (derivitive e2 f)
| kleene e     => cons (derivitive e f) eff
end.



Definition neg (v:bool): bool :=
match v with
| true => false
| false => true
end.


Local Open Scope nat_scope.

Fixpoint entailment (n:nat) (hy:hypothesis) (lhs rhs: contEff): bool :=
  match n with 
  | O => true  
  | S n' =>
    (
      match nullable lhs, nullable rhs with 
      | true , false => false 
      | _, _ =>  
        (
          match reoccurTRS hy lhs rhs with 
          | true => true 
          | false => 
    let fst := fst lhs in
    let subTrees := List.map (fun f =>
        let der1 := normal (derivitive lhs f) in
        let der2 := normal (derivitive rhs f) in
        entailment (n') ((lhs, rhs) :: hy) der1 der2
        ) fst in
    List.fold_left (fun acc a => acc && a) subTrees true
          end
        )
      end
    )
  end.

Definition entailmentShell (n:nat) (lhs rhs: contEff) : bool :=
  entailment n [] lhs rhs.


Lemma bot_entails_everything:
  forall (rhs: contEff) (n:nat),
    entailment (S n) [] bot rhs = true.
Proof.
  intro rhs.
  intros. unfold entailment. fold entailment.
  unfold nullable. unfold reoccurTRS. unfold derivitive. unfold normal.
  unfold fst. unfold map. unfold fold_left. reflexivity.
Qed.

Lemma emp_entails_nullable:
  forall (rhs: contEff) (n:nat) (hy:hypothesis),
    nullable rhs = true ->
    entailment (S n) [] emp rhs = true.
Proof. 
  intro rhs.
  intros. unfold entailment. fold entailment. unfold nullable. fold nullable.
  destruct (nullable rhs) as [].
  - unfold reoccurTRS. unfold derivitive. unfold normal.
    unfold fst. unfold map. unfold fold_left. reflexivity.
  - discriminate H.
Qed.
   
Lemma wildcard_entails_rhs_imply_nullable_rhs:
  forall (rhs: contEff) (n:nat),
    entailment (S (S n)) [] wildcard rhs = true ->
      nullable (normal (derivitive rhs any)) = true.
Proof. 
  intros rhs n. 
  unfold entailment. fold entailment. unfold nullable. fold nullable.
  unfold reoccurTRS. unfold derivitive. fold derivitive. unfold normal. fold normal.
  unfold fst. unfold map. unfold fold_left. 
  Search (true && _ = _).
  rewrite andb_true_l.
  unfold nullable. fold nullable. unfold compareEff. fold compareEff.
  rewrite andb_false_l.
  destruct (nullable (normal (derivitive rhs any))) as [].
  - intro. reflexivity.
  - intro. discriminate H.
Qed.
  

Theorem soundnessTRS: 
  forall (lhs: contEff) (n:nat)  (rhs: contEff),
    entailment (S n) [] lhs rhs = true -> 
    forall (f:fstT), entailment (S n) [] (derivitive lhs f) (derivitive rhs f) = true .
Proof.
  intro lhs. induction lhs.
  - intros. unfold derivitive. fold derivitive. 
    exact (bot_entails_everything (derivitive rhs f) n).
  - intros. unfold derivitive. fold derivitive.  
    exact (bot_entails_everything (derivitive rhs f) n).
  - intros. unfold derivitive. fold derivitive.   
    
  
  
  unfold entailment. fold entailment.
    unfold nullable. unfold reoccurTRS. unfold derivitive. unfold normal.
    unfold fst. unfold map. unfold fold_left. reflexivity.
  
  
  induction n.
    + unfold entailment. reflexivity.
    + fold derivitive.  unfold entailment. fold entailment. 
  
  - intros. 
    
    unfold derivitive. unfold entailment. reflexivity.

  - intro rhs. induction rhs. 
      * unfold derivitive. intros. induction n. + unfold entailment. reflexivity. + 
      
       fold  entailment. 
        unfold entailment. reflexivity.  .  
      * unfold derivitive. induction n.  unfold entailment. reflexivity.  unfold entailment. reflexivity.  
      * unfold derivitive. unfold entailment. reflexivity. 
      * unfold derivitive. unfold entailment. reflexivity. 
      * unfold derivitive. unfold entailment. reflexivity. 
      * unfold derivitive. unfold entailment. reflexivity. 
      * unfold derivitive. unfold entailment. reflexivity. 
      * unfold derivitive. unfold entailment. reflexivity. 
      * unfold derivitive. unfold entailment. reflexivity. 
    + intros. induction rhs.
      * unfold derivitive. unfold entailment. reflexivity. 
      * unfold derivitive.
       unfold entailment. reflexivity. 
      * unfold derivitive. unfold entailment. reflexivity. 
      * unfold derivitive. unfold entailment. reflexivity. 
      * induction f.
        -- 
      * unfold derivitive. unfold entailment. reflexivity. 
      * unfold derivitive. unfold entailment. reflexivity. 
      * unfold derivitive. unfold entailment. reflexivity. 
      * unfold derivitive. unfold entailment. reflexivity. 
      * unfold derivitive. unfold entailment. reflexivity. 


  - induction lhs.
    + intros. unfold derivitive. unfold entailment. reflexivity.
    + intros. unfold derivitive. unfold entailment. reflexivity.
    + intros. unfold derivitive. unfold entailment. reflexivity.
    + intros. unfold derivitive. unfold entailment. reflexivity.
    + intros. unfold derivitive. unfold entailment. reflexivity.
    + intros. unfold derivitive. unfold entailment. reflexivity.
    + intros. unfold derivitive. unfold entailment. reflexivity.
    + intros. unfold derivitive. unfold entailment. reflexivity.
    + intros. unfold derivitive. unfold entailment. reflexivity.
  - induction lhs.
    + intros. induction f.
      * unfold derivitive. fold derivitive. 
       unfold entailment. fold entailment.
    (intro f; unfold derivitive; unfold entailment; reflexivity ).
       
      

Qed.


Definition eff1 : contEff := emp.
Definition eff2 : contEff := {{[("A", one)]}}.
Definition eff3 : contEff := waiting "A".

Compute (entailmentShell eff3 eff2).

Compute (entailmentShell eff2 eff3).


Compute (entailmentShell (kleene eff2) (kleene eff2)).



