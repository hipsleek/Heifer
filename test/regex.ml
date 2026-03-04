open Heifer.Interactive;;

Options.fail_fast := true;;

axiom ~name:"eta_reduce"
  {| forall f. (fun x -> f x) <: f |}
;;

axiom ~name:"reset_under_bind"
  {| forall f1 f2. reset (f1; r. f2 r) <: reset (f1; r. reset (f2 r)) |}
;;

axiom ~name:"double_reset"
  {| forall f. reset (reset (f)) <: reset (f) |}
;;

axiom ~name:"reset_over_disj"
  {| forall f1 f2. reset (f1 \/ f2) <: reset (f1) \/ reset (f2) |}
;;

declare {|
  matches_prefix_sr r ns =
      (ens r=TREmp; Some ns)
    \/ (ex a. ens r=(TRAtom a); ((ex b ns1. ens ns=b::ns1 /\ a=b; Some ns1) \/ None))
    \/ (ex r1 r2. ens r=(TRSeq r1 r2);
              matches_prefix_sr r1 ns; v.
                ((ens v=None; None)
                \/ (ex rest. ens v=(Some rest); matches_prefix_sr r2 rest)))
    \/ (ex r1 r2. ens r=(TRDisj r1 r2);
              shift k
                (matches_prefix_sr r1 ns; v1. k v1; r3.
                    ((ens r3=None; matches_prefix_sr r2 ns; a. k a)
                    \/ (ex a. ens r3=(Some a); r3))))
|};;

declare {|
  matches_prefix_cps r ns k =
      ens r=TREmp; k (Some ns)
    \/ (ex a. ens r=(TRAtom a); ((ex b ns1. ens ns=b::ns1 /\ a=b; k (Some ns1)) \/ k None))
    \/ (ex r1 r2. ens r=(TRSeq r1 r2);
              matches_prefix_cps r1 ns (fun v ->
                ens v=None; k(None)
                \/ ex rest. ens v=(Some rest); matches_prefix_cps r2 rest k))
    \/ ex r1 r2. ens r=(TRDisj r1 r2);
              matches_prefix_cps r1 ns k; r3.
              ((ens r3=None; matches_prefix_cps r2 ns k) \/ r3)
|};;

Options.show_why3_goal := true;

start_proof {|
  forall r ns k.
    (forall r. reset (k r) <: k r) =>
    reset (matches_prefix_sr r ns; r1. k r1)
    <: matches_prefix_cps r ns k
|};;

forall_intro ();;

revert "k";;
revert "ns";;

induction ~name:"IH" `Regex "r";;

forall_intro ();;

forall_intro ();;

intro_pure "Hksf";;

unfold "matches_prefix_cps";;

unfold "matches_prefix_sr";;

simpl ();;

rewrite "reset_over_disj";;

rewrite "reset_over_disj";;

rewrite "reset_over_disj";;

disj_elim ();;

disj_elim ();;

disj_elim ();;

left ();;

left ();;

left ();;

goal_is {|
   reset (ens r=TREmp; k (Some ns))
<: ens r=TREmp; k (Some ns)
|};;

shift_reset_reduce ();;

rewrite "Hksf";;

refl ();;

(* munge goal to get to atom case *)

left ();;

left ();;

right ();;

(* Atom case *)

goal_is {|
   reset (ex a.
     ens r=TRAtom a;
     ((ex b ns1. ens ns=b::ns1 /\ a=b; k (Some ns1)) \/ k None))
<: (ex a.
     ens r=TRAtom a;
     ((ex b ns1. ens ns=b::ns1 /\ a=b; k (Some ns1)) \/ k None))
|};;

shift_reset_reduce ();;

exists_elim ();;

exists_intro ["a"];;

rewrite "Hksf";;

refl ();;

(* munge goal to get to seq case *)

left ();;

right ();;

(* Seq case *)

goal_is {|
  reset
    (ex r1 r2.
       ens r=TRSeq r1 r2;
       matches_prefix_sr r1 ns; v.
         (ens v=None; k None
          \/ (ex rest. ens v=Some rest; matches_prefix_sr r2 rest; r3. k r3))) <:
    (ex r1 r2.
       ens r=TRSeq r1 r2;
       matches_prefix_cps r1 ns
         (fun v ->
           ens v=None; k None
           \/ (ex rest. ens v=Some rest; matches_prefix_cps r2 rest k)))
|};;

shift_reset_reduce ();;

exists_elim ();;

(* Options.notation := true;; *)

exists_intro ["r1"; "r2"];;

(* TODO why is this provable?? *)
(* ens_pure_intro ();; *)

ens_pure_elim "Hr";;

ens_pure_intro ();;

rewrite "reset_under_bind";;

rewrite "IH";;

prove ();;

simpl ();;

shift_reset_reduce ();;

forall_intro ();;

refl ();;

simpl ();;

congruence ();;

funext ();;

forall_intro ();;

simpl ();;

shift_reset_reduce ();;

goal_is {|
   ens x0=None; reset (k None)
   \/ (ex rest.
         ens x0=Some rest; reset (matches_prefix_sr r2 rest; r3. k r3))
<: ens x0=None; k None
   \/ (ex rest. ens x0=Some rest; matches_prefix_cps r2 rest k)
|};;

congruence ();;

goal_is {|
   (ex rest. ens x0=Some rest; reset (matches_prefix_sr r2 rest; r3. k r3))
<: ex rest. ens x0=Some rest; matches_prefix_cps r2 rest k
|};;

rewrite "IH";;

prove ();;

(* TODO cannot rewrite a forall stmt *)

forall_intro ();;

rewrite "Hksf";;

refl ();;

refl ();;

goal_is {|
   ens x0=None; reset (k None)
<: ens x0=None; k None
|};;

rewrite "Hksf";;
refl ();;

(* munge leading to disj case *)

right ();;

(* disj case *)

goal_is {|
   reset
     (ex r1 r2.
        ens r=TRDisj r1 r2;
        shift k1
          (matches_prefix_sr r1 ns; v1.
             k1 v1; r4.
               (ens r4=None; matches_prefix_sr r2 ns; a. k1 a
                \/ (ex a. ens r4=Some a; r4))); r3.
          k r3)
<: ex r1 r2.
     ens r=TRDisj r1 r2;
     matches_prefix_cps r1 ns k; r3.
       (ens r3=None; matches_prefix_cps r2 ns k \/ r3)
|};;

shift_reset_reduce ();;

exists_elim ();;

exists_intro ["r1"; "r2"];;

ens_pure_elim "Hr";;

ens_pure_intro ();;

(* top level goal on the right is a disj *)

rewrite "reset_under_bind";;

rewrite "IH";;

prove ();;

forall_intro ();;

simpl ();;

rewrite "double_reset";;

refl ();;

axiom ~name:"matches_prefix_cps_cont"
  {| forall r ns k f.
    matches_prefix_cps r ns (fun r1 -> k r1; r2. f r2) <:
      matches_prefix_cps r ns k; r1. f r1
  |}
;;

rewrite ~direction:`Rtl "matches_prefix_cps_cont";;

congruence ();;

funext ();;

forall_intro ();;

simpl ();;

shift_reset_reduce ();;

rewrite "Hksf";;

congruence ();;

funext ();;

forall_intro ();;

simpl ();;

(* match disjuncts *)

goal_is {|
   ens x2=None; reset (matches_prefix_sr r2 ns; a. reset (k a))
   \/ (ex a. ens x2=Some a; x2)
<: ens x2=None; matches_prefix_cps r2 ns k \/ x2
|};;

disj_elim ();;

left ();;

rewrite "IH";;

prove ();;

simpl ();;

forall_intro ();;

rewrite "double_reset";;

refl ();;

rewrite "Hksf";;

rewrite "eta_reduce";;

refl ();;

right ();;

goal_is {|
   (ex a. ens x2=Some a; x2)
<: x2
|};;

simple ();;

qed ();;

(* TODO there's a bug in unification which causes the x not to be filled in *)
(* have ~name:"k_sf_bind"
  {| forall k f.
        reset (k x0; r. f r) <: k x0; r. reset (f r)
  |}
;;
*)

(* TODO specialize cannot be used on lower arity *)
(* TODO parsing of options *)
(* TODO pctx.pp_goal prints existentials without parens *)

(* TODO ens_pure_intro should fail if it does not change the goal *)

(* TODO matching tactics for dealing with situations like this *)

(* TODO not ensures error msg. dump the goal when that happens *)
(* TODO reset the options on start proof *)

(* TODO print goal did not change *)
(* TODO sr reduction inside function bodies *)

(* TODO there's a bug with printing existentials on the left of subsumes, parens are missing *)

(* TODO had to manually put parens around existentials inside subsumes *)