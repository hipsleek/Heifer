
Require Import FunInd.
From Coq Require Import Arith Bool Ascii String ZArith.Int.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Require Import Coq.Program.Wf.
Require Import Coq.Arith.Plus.

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

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



Fixpoint fst (eff:singleES): bool :=
match eff with
| bot          => false
| emp          => false
| singleton    => true 
| disj e1 e2   => fst e1 || fst e2
| cons e1 e2   => if nullable e1 then fst e1 || fst e2
                  else fst e1
| kleene e     => fst e
| infity e     => fst e
| omega e      => fst e
end.

Fixpoint derivitive (eff:singleES): singleES :=
match eff with
| bot          => bot
| emp          => bot
| singleton    => emp
| cons e1 e2   => if nullable e1 
                  then disj (cons (derivitive e1) e2)  (derivitive e2)
                  else cons (derivitive e1) e2
| disj e1 e2   => disj (derivitive e1) (derivitive e2)
| kleene e     => cons (derivitive e) eff
| infity e     => cons (derivitive e) eff
| omega e     => cons (derivitive e) eff
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
    (match nullable lhs, nullable rhs with 
    | true , false => false 
    | _, _ =>  
      (match infinitiable lhs, infinitiable rhs with 
      | true, false => false
      | _, _ =>  
        (match reoccurTRS hy lhs rhs with 
        | true => true 
        | false => 
          if fst lhs then 
            let der1 := (derivitive lhs) in
            let der2 := (derivitive rhs) in
            entailment (n') ((lhs, rhs) :: hy) der1 der2
          else true 
        end)
      end)
    end)
  end.
  

Definition entailmentShell (n:nat) (lhs rhs: singleES) : bool :=
  entailment n [] lhs rhs.

Lemma cons_emp_lhs: 
  forall (es:singleES),
    cons emp es = es.
Proof.
Admitted. 

Lemma cons_emp_rhs: 
  forall (es:singleES),
    cons es emp = es.
Proof.
Admitted. 


Lemma cons_bot_lhs: 
  forall (es:singleES),
    cons bot es = bot.
Proof.
Admitted. 

Lemma cons_bot_rhs: 
  forall (es:singleES),
    cons es bot = bot.
Proof.
Admitted. 
 

Lemma disj_bot_lhs: 
  forall (es:singleES),
    disj bot es = es.
Proof.
Admitted. 

Lemma cons_not_bot_each_not_bot:
forall (es1 es2 : singleES), 
compareEff bot (normal (cons es1 es2)) = false ->
compareEff bot (normal es1) = false /\  compareEff bot (normal es2) = false.
Proof.
Admitted.


Lemma disj_not_bot_each_not_bot:
forall (es1 es2 : singleES), 
compareEff bot (normal (disj es1 es2)) = false ->
compareEff bot (normal es1) = false \/  compareEff bot (normal es2) = false.
Proof.
Admitted.



Lemma bot_entails_everything:
  forall (rhs: singleES) , 
    entailment 1 [] bot rhs = true.
Proof.
  intro rhs.
  intros. unfold entailment. fold entailment.
  unfold nullable. unfold reoccurTRS. unfold derivitive. unfold normal.
  unfold fst. unfold map. unfold fold_left. reflexivity.
Qed.

Lemma cons_singleton_rest_entails_bot_leadsto_rest_ential_bot:
  forall (rest: singleES) ,
    (exists n, entailment n [] (rest) bot = false) ->
    exists n, entailment n [] (cons singleton rest) bot = false.
Proof.
Admitted. 

Lemma cons_es1_es2_if_es1_does_not_entail_rhs_then_fail:
  forall (es1 es2 rhs: singleES) ,
    (exists n, entailment n [] es1 rhs = false) ->
    exists n, entailment n [] (cons es1 es2) rhs = false.
Proof.
Admitted. 

Lemma disj_es1_es2_if_es1_does_not_entail_rhs_then_fail:
  forall (es1 es2 rhs: singleES) ,
  (exists n, entailment n [] es1 rhs = false)  \/ (exists n, entailment n [] es2 rhs = false) ->
  exists n, entailment n [] (disj es1 es2) rhs = false.
    
Proof.
Admitted. 




Lemma nothing_entail_bot:
  forall (lhs: singleES), 
    compareEff bot (normal lhs) = false ->
    exists n,
    entailment n [] lhs bot  = false.
Proof.
  intro lhs.
  induction lhs.
  - unfold compareEff. intro H. discriminate H.
  - unfold compareEff. intro. exists 1. unfold entailment. unfold nullable. reflexivity.
  - unfold compareEff. intro. exists 2. 
    fold_unfold_tactic entailment. 
  - intro.  assert (temp:= cons_not_bot_each_not_bot lhs1 lhs2 H).
    destruct temp.
    assert (temp2:=IHlhs2 H1).
    apply (cons_es1_es2_if_es1_does_not_entail_rhs_then_fail lhs1 lhs2 bot).
      exact (IHlhs1 H0).
  - intro.  apply (disj_es1_es2_if_es1_does_not_entail_rhs_then_fail lhs1 lhs2).
    assert (temp:= disj_not_bot_each_not_bot lhs1 lhs2 H). 
    destruct temp.
    + left. exact (IHlhs1 H0).
    + right. exact (IHlhs2 H0).
  - intro. exists 1. fold_unfold_tactic entailment.
  - intro. exists 1. fold_unfold_tactic entailment.
  - intro. exists 1. fold_unfold_tactic entailment.
Qed.  
  



Lemma emp_entails_nullable n:
  forall (rhs: singleES), 
    nullable rhs = true ->
    entailment n [] emp rhs = true.
Proof. 
Admitted. 


Lemma emp_entails_nullable1 n:
  forall (rhs: singleES), 
    entailment n [] emp rhs = true->
    nullable rhs = true.
Proof. 
Admitted. 

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



Lemma emp_cons_lhs_entails_rhs_is_lhs_entails_rhs n:
  forall (lhs rhs : singleES), 
  entailment n [] (cons emp lhs) rhs = true ->
  entailment n [] lhs rhs = true.
Proof.
Admitted. 



Lemma cons_sig_sig_rhs:
forall (rhs:singleES),
exists n : nat,
  entailment n [] (cons singleton singleton) rhs = true ->
  entailment n [] singleton (derivitive rhs one) = true.
Proof.
Admitted.

Lemma only_emp_entails_emp:
forall (lhs:singleES),
   exists n,
   entailment n [] lhs emp = true ->
   lhs = emp.
Proof.
Admitted. 

Lemma  derivitive_of_cond_single_rest_is_rest: 
forall (rest:singleES), 
derivitive (cons singleton rest) one = (cons singleton rest)
.
Proof.
Admitted.

Lemma  derivitive_bot_is_bot: 
(derivitive bot one) = bot
.
Proof.
  Admitted.

Lemma nullable_cons_single_false:
forall (rest:singleES), 
 nullable (cons singleton rest) = false.
 Proof.
  Admitted.



Compute (entailment 1 [] (omega singleton) bot).

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
    + simpl. rewrite (cons_emp_lhs). 
      rewrite (cons_bot_lhs).
      rewrite (disj_bot_lhs). 
      exact (IHlhs2 rhs one).
    + unfold nullable. induction lhs2. 
      * rewrite (cons_bot_rhs). simpl. rewrite (cons_emp_lhs). exact (IHlhs2 rhs one).
      * rewrite (cons_emp_rhs). rewrite cons_emp_rhs. simpl.  exact (IHlhs1 rhs one).
      * simpl. rewrite (cons_emp_lhs).
        induction rhs.
        -- exists 1. simpl. intro. reflexivity.
        -- exists 1. simpl. intro. reflexivity.
        -- exists 3. trivial. 
        -- exists 3. trivial.
        -- exists 3. trivial.
        -- exists 3. trivial.
        -- exists 3. trivial.
        -- exists 3. trivial.
      * simpl.  rewrite cons_emp_lhs. 
        induction rhs.
        -- simpl.  exists 2. intro H. unfold entailment in H.
           unfold nullable in H. rewrite andb_false_l in H.
           unfold infinitiable in H.  fold infinitiable in H.
           rewrite andb_false_l in H.
           unfold reoccurTRS in H. fold reoccurTRS in H. unfold fst in H.
           fold fst in H. unfold nullable in H. fold nullable in H. unfold map in H.
           fold map in H. rewrite (derivitive_of_cond_single_rest_is_rest ((cons lhs2_1 lhs2_2))) in H.
           rewrite derivitive_bot_is_bot in H. 
           rewrite (nullable_cons_single_false (cons lhs2_1 lhs2_2)) in H.
           case_eq (infinitiable (cons singleton (cons lhs2_1 lhs2_2))).
           ++ unfold infinitiable in H. fold infinitiable in H.
              rewrite andb_false_l in H. unfold nullable in H. unfold normal in H.
              




           
      
      admit.
      * simpl. rewrite (cons_emp_lhs). admit.
      * simpl.  rewrite (cons_emp_lhs). admit.
      * simpl.  rewrite (cons_emp_lhs). 
        induction rhs.
        --  simpl. exists 2. unfold entailment. simpl. intro. discriminate H.
        -- simpl. exists 2. simpl. intro. discriminate H.
        --  simpl. exists 2. unfold entailment. unfold nullable. fold nullable.
            rewrite andb_false_l. unfold infinitiable. fold infinitiable. 
            rewrite andb_false_l. unfold reoccurTRS. 

            simpl. 
        
        intro.
        
        exists 2. simpl. intro. discriminate H.



      * simpl. intro. reflexivity.
      * 
      * unfold nullable.  
        intro.  simpl. assert (temp:= emp_cons_lhs_entails_rhs_is_lhs_entails_rhs 2 singleton rhs H).
        assert (temp1:= singlon_entaill_rhs_then_der_rhs_nullable 2 rhs one temp). 
        case_eq(nullable (derivitive rhs one)).
        -- intro. reflexivity.
        -- assert (temp3:= emp_entails_nullable1 2 (derivitive rhs one) temp1).
           rewrite temp3. intro. discriminate H0.
      * unfold nullable.  intro. assert (temp:= emp_cons_lhs_entails_rhs_is_lhs_entails_rhs 2 singleton rhs H).
        assert (temp1:= singlon_entaill_rhs_then_der_rhs_nullable 2 rhs one temp). 
        
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
