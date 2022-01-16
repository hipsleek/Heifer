Require Import FunInd.
From Coq Require Import Bool Ascii String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Require Import Lib.conteff.

Module AST.

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
  | app v1 v2 => app (subst_val v1 v x) (subst_val v2 v x)
  (* TODO deal with variable capture? *)
  | letIn x e1 e2 => letIn x (subst_expr e1 v x) (subst_expr e2 v x)
  | ifElse v1 e1 e2 => ifElse (subst_val v1 v x) (subst_expr e1 v x) (subst_expr e2 v x)
  | perform l v1 => perform l (subst_val v1 v x)
  | matchWith e1 h => matchWith (subst_expr e1 v x) (subst_handler h v x)
  end.

(* https://stackoverflow.com/questions/69944163/is-it-possible-to-declare-type-dependent-notation-in-coq *)
Class SubstNotation (A : Type) := sub : A -> value -> string -> A.

(* should bind more tightly than =, at 70 *)
(* conflicts with division *)
(* Notation " e '[' v '/' x ']' " := (sub e v x) (at level 71). *)

(* https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/coqdoc/STLC_Solutions.html *)
(* Notation "[ x ~> v ] e" := (sub e v x) (at level 68). *)

(* https://softwarefoundations.cis.upenn.edu/plf-current/Stlc.html *)
Notation "'[' x ':=' v ']' e" := (sub e v x) (at level 20).

Local Instance SubstExpr : SubstNotation expr := { sub e v x := subst_expr e v x }.
Local Instance SubstValue : SubstNotation value := { sub v1 v x := subst_val v1 v x }.
Local Instance SubstHandler : SubstNotation handler := { sub h v x := subst_handler h v x }.

Definition first_handler_with_label (l:string) (h:handler) : option h_effect :=
  match h with
  | handle _ hs =>
    List.find (fun h1 =>
    match h1 with
    | h_eff l1 _ _ _ => eqb l1 l
    end) hs
  end.

Definition label_not_in_handler (l:string) (h:handler) : Prop :=
  first_handler_with_label l h = None.

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.

Module Map := FMapAVL.Make(String_as_OT).

Notation env := (Map.t value).

(* evaluation contexts E *)
Inductive context : Set :=
| e_hole
| e_letIn (x:string) (ctx:context) (e:expr)
| e_matchWith (ctx:context) (h:handler).

Inductive e_sub : context -> expr -> expr -> Prop :=
| ESubHole : forall e,
  e_sub e_hole e e
| ESubLet : forall e1 e2 e3 x ctx,
  e_sub ctx e2 e3 ->
  e_sub (e_letIn x ctx e1) e2 (letIn x e3 e1)
| ESubMatch : forall e1 e2 ctx h,
  e_sub ctx e1 e2 ->
  e_sub (e_matchWith ctx h) e1 (matchWith e2 h).

Local Hint Constructors e_sub : core.

(* 10 is the maximum it can be to work as an arg of ->...? *)
Notation " ctx '[' e1 ']' '==' e2 " := (e_sub ctx e1 e2) (at level 10).

(* evaluation contexts U_l *)
Inductive u_context : string -> Set :=
| u_hole : forall l, u_context l
| u_letIn : forall l (x:string) (ctx:u_context l) (e:expr), u_context l
| u_matchWith : forall l (ctx:u_context l) (h:handler), label_not_in_handler l h ->
  u_context l
.

Fixpoint u_sub (l:string) (ctx:u_context l) (e:expr) : expr :=
  match ctx with
  | u_hole l => e
  | u_letIn l1 x ctx e1 => letIn x (u_sub l1 ctx e) e1
  | u_matchWith l1 ctx h pf => matchWith (u_sub l1 ctx e) h
  end.

(* Notation " ctx l '[' e ']' " := (u_sub l ctx e) (at level 10). *)

(* Definition a := e_hole ["a"] == "a". *)
(* Definition b := (u_hole "l") "l" ["a"]. *)

(* Notation " ctx '_' l '[' e ']' " := (u_sub l ctx e) (at level 10). *)
(* Notation " ctx '_' l '(' e ')' " := (u_sub l ctx e) (at level 30). *)
(* Notation " '[' e ']' ctx '_' l " := (u_sub l ctx e) (at level 10). *)

(* 10 is the maximum it can be to work as an arg of ->...? *)
(* Notation " ctx l '[' e1 ']' '==' e2 " := (u_sub l ctx e1 e2) (at level 10). *)

Inductive step : expr -> expr -> Prop :=
| SIfT : forall e1 e2,
  step (ifElse (litbool true) e1 e2) e1
| SIfF : forall e1 e2,
  step (ifElse (litbool false) e1 e2) e1
| SLet : forall v e e1 (x:string),
  [x:=v]e = e1 ->
  step (letIn x (val v) e) e1
| SApp : forall f v e e1 x,
  [x:=v]e = e1 ->
  step (app (func f x e) v) e1
| SMatchV : forall v e e1 x hs,
  [x:=v]e = e1 ->
  step (matchWith (val v) (handle (h_ret x e) hs)) e1

| SMatchPShallow : forall v h hr hs l ctx hb e x k,
  h = handle hr hs ->
  Some (h_eff l x k hb) = first_handler_with_label l h ->
  e = ["continue":=func "f" "y" (
    u_sub l ctx "y"
    )] ([x:=v] hb) ->
  step
    (matchWith
      (u_sub l ctx (perform l v))
      h) e

| SMatchPDeep : forall v h hr hs l ctx hb e x k,
  h = handle hr hs ->
  Some (h_eff l x k hb) = first_handler_with_label l h ->
  e = ["continue":=func "f" "y" (
    (matchWith (        (* <- *)
      u_sub l ctx "y"
    ) (handle hr hs))   (* <- *)
    )] ([x:=v] hb) ->
  step
    (matchWith
      (u_sub l ctx (perform l v))
      h) e
.

Local Hint Constructors step : core.
Notation " e1 '-->' e2 " := (step e1 e2) (at level 10).

Inductive istep : expr -> expr -> option string -> Prop :=
  | IEff : forall l ctx v h e,
    step
      (matchWith
        (u_sub l ctx (perform l v))
        h) e ->
    istep
      (matchWith
        (u_sub l ctx (perform l v))
        h) e (Some l)
  | ISilent : forall e1 e2,
      step e1 e2 ->
      istep e1 e2 None
      (* this rule allows us to ignore the effect.
        do we need to have one copy for every other constructor? *)
.

Local Hint Constructors istep : core.
Notation " e1 '-i->' e2 'with' s " := (istep e1 e2 s) (at level 10).

(* Local Hint Constructors u_sub : core. *)

Inductive ustep : expr -> expr -> Prop :=
| UStep : forall l U c1 c2 C1 C2,
  c1 --> c2 ->
  (* U l [c1] == C1 -> *)
  (* U l [c2] == C2 -> *)
  u_sub l U c1 = C1 ->
  u_sub l U c2 = C2 ->
  ustep C1 C2.

Local Hint Constructors ustep : core.

Require Import Coq.Relations.Relation_Operators.
Local Hint Constructors clos_trans : core.
Notation ustep_star := (clos_trans expr ustep).

(* 11 works but 10 doesn't! *)
Notation " e1 '-u->' e2 " := (ustep e1 e2) (at level 11).
Notation " e1 '-u->*' e2 " := (ustep_star e1 e2) (at level 11).

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

(* instrumented semantics *)
Inductive iestep : expr -> expr -> option string -> Prop :=
| IEStep : forall E c1 c2 C1 C2 l,
  (* given a step *)
  c1 -i-> c2 with l ->
  (* which occurs inside larger exprs C1 and C2 *)
  E[c1] == C1 ->
  E[c2] == C2 ->
  (* C1 can take a step to C2 *)
  iestep C1 C2 l.

Local Hint Constructors iestep : core.

Inductive iestep_star : expr -> expr -> list string -> Prop :=
| i_add : forall e1 e2 e3 s s1,
  iestep e1 e2 (Some s) ->
  iestep_star e2 e3 s1 ->
  iestep_star e1 e3 (s :: s1)
| i_silent : forall e1 e2 e3 s1,
  iestep e1 e2 None ->
  iestep_star e2 e3 s1 ->
  iestep_star e1 e3 s1
| i_end : forall e s,
  iestep_star e e s
  .

Local Hint Constructors iestep_star : core.

Notation " e1 '-ie->' e2 'with' t " := (iestep e1 e2 t) (at level 11).
Notation " e1 '-ie->*' e2 'with' t " := (iestep_star e1 e2 t) (at level 11).

Notation spec_env := (Map.t contEff).

Inductive fv : spec_env -> contEff -> expr -> contEff -> Prop :=
| fv_val : forall env p v q,
  fv env p (val v) q
| fv_let : forall env p q es1 e1 e2 x,
  fv env p e1 es1 ->
  fv (Map.add x es1 env) p e2 q ->
  fv env p (letIn x e1 e2) q
  (* TODO requires subtyping, which requires inclusion *)
(* | fv_app :
  fv env p (app v1 v2) q *)
  .

Notation " env '|-' '{' p '}' e '{' q '}'" := (fv env p e q) (at level 11).

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

Example ex5 :
  matchWith (perform "Eff" unit) (handle
    (h_ret "x" unit)
    [h_eff "Eff" "y" "k" (app "continue" 1)])
  -e->* 1.
Proof.
  apply t_trans with (y := (app (func "f" "y" (u_sub "Eff" (u_hole "Eff") "y")) 1)).
  - {
    apply t_step.
    apply EStep with
      (E := e_hole)
      (c1 := matchWith (u_sub "Eff" (u_hole "Eff") (perform "Eff" unit))
        (handle (h_ret "x" unit) [h_eff "Eff" "y" "k" (app "continue" 1)]))
      (c2 := (app (func "f" "y" (u_sub "Eff" (u_hole "Eff") "y")) 1)).
    - eapply SMatchPShallow; repeat (simpl; auto).
    - apply ESubHole.
    - apply ESubHole.
  }
  - apply t_step. simpl. eauto.
Qed.

Example ex6 :
  matchWith (perform "Eff" unit) (handle
    (h_ret "x" unit)
    [h_eff "Eff" "y" "k" (app "continue" 1)])
  -ie->* 1 with ["Eff"].
Proof.
  eapply i_add with (e2 := (app (func "f" "y" (u_sub "Eff" (u_hole "Eff") "y")) 1)).
  - eapply IEStep with (E := e_hole)
      (c1 := matchWith (u_sub "Eff" (u_hole "Eff") (perform "Eff" unit))
        (handle (h_ret "x" unit) [h_eff "Eff" "y" "k" (app "continue" 1)]))
      (c2 := (app (func "f" "y" (u_sub "Eff" (u_hole "Eff") "y")) 1)).
    + eapply IEff.
      eapply SMatchPShallow; auto.
      simpl. reflexivity.
      simpl.
      unfold sub. simpl. reflexivity.
    + apply ESubHole.
    + apply ESubHole.
  - simpl. eapply i_silent with (e2 := 1).
    eauto.
    apply i_end.
Qed.

End AST.