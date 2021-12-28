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
| singleton i  => if entailFst f (one i) then emp else bot
| not   i      => if entailFst f (zero i) then emp else bot 
| wildcard     => emp 
| stop         => bot
| cons e1 e2   => if nullable e1 then disj (cons (derivitive e1 f) e2)  (derivitive e2 f)
                  else cons (derivitive e1 f) e2
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
  if nullable lhs && neg (nullable rhs) then false
  else if reoccurTRS hy lhs rhs then true
  else
    let fst := fst lhs in
    let subTrees := List.map (fun f =>
        let der1 := normal (derivitive lhs f) in
        let der2 := normal (derivitive rhs f) in
        entailment (n') ((lhs, rhs) :: hy) der1 der2
        ) fst in
    List.fold_left (fun acc a => acc && a) subTrees true
  end.



Definition entailmentShell (lhs rhs: contEff) : bool :=
  entailment 1000 [] lhs rhs.

Definition eff1 : contEff := emp.
Definition eff2 : contEff := {{[("A", one)]}}.
Definition eff3 : contEff := waiting "A".

Compute (entailmentShell eff3 eff2).

Compute (entailmentShell eff2 eff3).


Compute (entailmentShell (kleene eff2) (kleene eff2)).



