Module AST.

Require Import FunInd.
From Coq Require Import Arith Bool Ascii String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Require Import Coq.Program.Wf.
Require Import Coq.Arith.Plus.

Definition numEvent := 10.

Inductive evtSeq : Type :=
| bot
| emp
| underline
| event       (s:string) (arg:nat)
| notEvent    (s:string) (arg:nat)
| placeHolder (s:string) (arg:nat)
| cons        (es1: evtSeq) (es2: evtSeq)
| disj        (es1: evtSeq) (es2: evtSeq)
| kleene      (es: evtSeq).

Definition highOrdSpec : Type := list (string * evtSeq * evtSeq).

Definition contEff : Type := (highOrdSpec * evtSeq).

Inductive value : Set :=
  | unit
  | litnum (n:nat)
  | litbool (b:bool)
  | var    (s:string)
  | func   (f:string) (x:string) (e:expr) (* TODO pre/post *)

with h_return : Set := h_ret (x:string) (e:expr)

with h_effect : Set := h_eff (l x:string) (k:value) (e:expr)

with handler : Set := handle (ret:h_return) (hs:list h_effect)

with expr : Set :=
  | val    (v:value)
  | app    (v1 v2:value)
  | letIn    (x:string) (e1 e2:expr)
  | ifElse (v:value) (e1:expr) (e2:expr)
  | perform (l:string) (v:value)
  | matchWith (e:expr) (h:handler)
.

Coercion litnum : nat >-> value.
Coercion litbool : bool >-> value.
Coercion val : value >-> expr.
Coercion var : string >-> value.

(* v1[v/x] = v2 *)
(* not mutually recursive because we don't substitute under binders *)
Definition subst_val (v1 v : value) (x : string) : value :=
  match v1 with
  | unit => unit
  | litnum n => litnum n
  | litbool b => litbool b
  | func f y e => func f y e
  | var y => if string_dec x y then v else v1
  end.

(* h[v/x] = h1 *)
Fixpoint subst_handler (h:handler) (v : value) (x : string) : handler :=
  match h with
  | handle (h_ret rx re) he =>
    handle (h_ret rx (subst_expr re v x)) (List.map (fun h1 =>
      match h1 with
      | h_eff l s k e => h_eff l s k (subst_expr e v x)
      end) he)
  end

(* e[v/x] = e1 *)
with subst_expr (e : expr) (v : value) (x : string) : expr :=
  match e with
  | val v1 => val (subst_val v1 v x)
  | app v1 v2 => app (subst_val v1 v x) (subst_val v1 v x)
  (* TODO deal with variable capture? *)
  | letIn x e1 e2 => letIn x (subst_expr e1 v x) (subst_expr e2 v x)
  | ifElse v1 e1 e2 => ifElse (subst_val v1 v x) (subst_expr e1 v x) (subst_expr e2 v x)
  | perform l v1 => perform l (subst_val v1 v x)
  | matchWith e1 h => matchWith (subst_expr e1 v x) (subst_handler h v x)
  end.

Definition labels_of_handler (h:handler) : list string :=
  match h with
  | handle _ hs =>
    List.map (fun h1 =>
    match h1 with
    | h_eff l _ _ _ => l
    end
    ) hs
  end.

Definition label_not_in_handler (l:string) (h:handler) : Prop :=
  match h with
  | handle _ hs =>
    ~ In l (labels_of_handler h)
  end.

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.

Module Map := FMapAVL.Make(String_as_OT).

Notation env := (Map.t value).

(* evaluation contexts E *)
Inductive context : Set :=
| e_hole
| e_letIn (x:string) (ctx:context) (e:expr)
| e_matchWith (ctx:context) (h:handler).

Inductive sub_context : context -> expr -> expr -> Prop :=
| ESubHole : forall e,
  sub_context e_hole e e
| ESubLet : forall e1 e2 e3 x ctx,
  sub_context ctx e2 e3 ->
  sub_context (e_letIn x ctx e1) e2 (letIn x e3 e1)
| ESubMatch : forall e1 e2 ctx h,
  sub_context ctx e1 e2 ->
  sub_context (e_matchWith ctx h) e1 (matchWith e2 h).

Local Hint Constructors sub_context : core.

(* 10 is the maximum it can be to work as an arg of ->...? *)
Notation " ctx '[' e1 ']' '==' e2 " := (sub_context ctx e1 e2) (at level 10).

(* evaluation contexts U_l *)
Inductive u_context : string -> Set :=
| u_hole : forall l, u_context l
| u_letIn : forall l (x:string) (ctx:u_context l) (e:expr), u_context l
| u_matchWith : forall l (ctx:u_context l) (h:handler), label_not_in_handler l h ->
  u_context l
.

Fixpoint u_sub_context (l:string) (ctx:u_context l) (e:expr) : expr :=
  match ctx with
  | u_hole _l => e
  | u_letIn l1 x ctx e1 => letIn x (u_sub_context l1 ctx e) e1
  | u_matchWith l1 ctx h pf => matchWith (u_sub_context l1 ctx e) h
  end.

Inductive step : expr -> expr -> Prop :=
| SIfT : forall e1 e2,
  step (ifElse (litbool true) e1 e2) e1
| SIfF : forall e1 e2,
  step (ifElse (litbool false) e1 e2) e1
| SLet : forall v e e1 x,
  subst_expr e v x = e1 ->
  step (letIn x (val v) e) e1
| SApp : forall f v e e1 x,
  subst_expr e v x = e1 ->
  step (app (func f x e) v) e1
| SMatchV : forall v e e1 x hs,
  subst_expr e v x = e1 ->
  step (matchWith (val v) (handle (h_ret x e) hs)) e1
(* shallow handler *)
| SMatchPS : forall v e x hr hs l ctx k hb,
  In (h_eff l x k hb) hs ->
  step
    (matchWith
      (u_sub_context l ctx (perform l v))
      (handle hr hs))
    (subst_expr
      (subst_expr e v x)
      (func "f" "y"
        (u_sub_context l ctx (val (var "y")))
      ) "continue")

(* deep handler *)
| SMatchP : forall v e x hr hs l ctx k hb,
  In (h_eff l x k hb) hs ->
  step
    (matchWith
      (u_sub_context l ctx (perform l v))
      (handle hr hs))
    (subst_expr
      (subst_expr e v x)
      (func "f" "y"
        (matchWith (        (* <- *)
          u_sub_context l ctx (val (var "y"))
        ) (handle hr hs))   (* <- *)
      ) "continue")
.

Local Hint Constructors step : core.
Notation " e1 '-->' e2 " := (step e1 e2) (at level 10).

(* Local Hint Constructors u_sub_context : core. *)

(* 10 is the maximum it can be to work as an arg of ->...? *)
(* Notation " ctx l '[' e1 ']' '==' e2 " := (u_sub_context l ctx e1 e2) (at level 10). *)

Inductive ustep : expr -> expr -> Prop :=
| UStep : forall l U c1 c2 C1 C2,
  c1 --> c2 ->
  (* U l [c1] == C1 -> *)
  (* U l [c2] == C2 -> *)
  u_sub_context l U c1 = C1 ->
  u_sub_context l U c2 = C2 ->
  ustep C1 C2.

Local Hint Constructors ustep : core.

Require Import Coq.Relations.Relation_Operators.
Local Hint Constructors clos_trans : core.
Notation ustep_star := (clos_trans expr ustep).

(* 11 works but 10 doesn't! *)
Notation " e1 '-u->' e2 " := (ustep e1 e2) (at level 11).
Notation " e1 '-u->*' e2 " := (ustep_star e1 e2) (at level 11).

(* some example programs *)

(* Definition func_id := func "f" "x" (val (var "x")). *)

Inductive estep : expr -> expr -> Prop :=
| EStep : forall E c1 c2 C1 C2,
  (* given a step *)
  c1 --> c2 ->
  (* which occurs inside larger exprs C1 and C2 *)
  E[c1] == C1 ->
  E[c2] == C2 ->
  (* C1 can take a step to C2 *)
  estep C1 C2.

Local Hint Constructors estep : core.

Require Import Coq.Relations.Relation_Operators.
Local Hint Constructors clos_trans : core.
Notation estep_star := (clos_trans expr estep).

(* 11 works but 10 doesn't! *)
Notation " e1 '-e->' e2 " := (estep e1 e2) (at level 11).
Notation " e1 '-e->*' e2 " := (estep_star e1 e2) (at level 11).

(* some example programs *)

Definition func_id := func "f" "x" (val (var "x")).

Example ex1 :
  ifElse true 1 2 -e-> 1.
Proof.
  (* debug eauto. *)
  eapply EStep.
  apply SIfT.
  apply ESubHole.
  apply ESubHole.
Qed.

Example ex2 :
  letIn "x" (letIn "y" 1 "y") "x" -e->* 1.
Proof.
  apply (t_trans _ _ _ (letIn "x" 1 "x")).
  - eauto 6.
  - eauto.
Qed.

Example ex3 :
  ifElse true 1 2 -u-> 1.
Proof.
  apply UStep with (l := "l") (U := u_hole "l") (c1 := ifElse true 1 2) (c2 := 1); auto.
Qed.

Example ex4 :
  letIn "x" (letIn "y" 1 "y") "x" -u->* 1.
Proof.
  apply (t_trans _ _ _ (letIn "x" 1 "x")).
  - apply t_step.
    apply UStep with (l := "l") (U := u_letIn "l" "x" (u_hole "l") "x")
      (c1 := letIn "y" 1 "y")
      (c2 := 1); auto.
  - apply t_step.
    apply UStep with (l := "l") (U := u_hole "l")
      (c1 := letIn "x" 1 "x")
      (c2 := 1); auto.
Qed.

(*

differnce: sync - presnet valid for one time cycle 
           async- manuelly turn off the present signals.
*)


(* last argument is the completion code true -> normal, flase -> not completed*)
(*
Definition state : Type := (syncEff * (option instance) * nat).

Definition states : Type := list state.


Notation "'_|_'" := bot (at level 0, right associativity).

Notation "'ϵ'" := emp (at level 0, right associativity).

Notation "+ A" := (A, one) (at level 0, right associativity).

Notation "! A" := (A, zero) (at level 0, right associativity).

Notation "'{{' Eff '}}'" := (singleton Eff) (at level 100, right associativity).

Notation " I1  @  I2 " := (cons I1 I2) (at level 100, right associativity).

Notation " I1  'or'  I2 " := (disj I1 I2) (at level 100, right associativity).

Notation " I1  '//'  I2 " := (parEff I1 I2) (at level 100, right associativity).

Notation "'star' I" := (kleene I) (at level 200, right associativity).



Notation "'nothing'" := nothingE (at level 200, right associativity).

Notation "'pause'" := pauseE (at level 200, right associativity).

Notation "'emit' A" := (emitE A) (at level 200, right associativity).

Notation "'signal' A 'in' E" := (localDelE A E)  (at level 200, right associativity).

Notation "E1 ; E2" := (seqE E1 E2)  (at level 200, right associativity).

Notation "'fork' E1 'par' E2" := (parE E1 E2)  (at level 80, right associativity).

Notation "'present' A 'then' E1 'else' E2" := (ifElseE A E1 E2)  (at level 200, right associativity).
Notation "'loop' E" := (loopE E) (at level 200, right associativity).

(*
Notation "'suspend' E 'when' S" := (suspendE E S) (at level 200, right associativity).
*)

Notation "'async' E 'with' S" := (asyncE E S) (at level 200, right associativity).

Notation "'await' S" := (awaitE S) (at level 200, right associativity).

Notation "'raise' N" := (raiseE N) (at level 200, right associativity).

Notation "'trap' E1 'catchwith' E2" := (trycatchE E1 E2) (at level 200, right associativity).
*)