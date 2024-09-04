
open Hipcore
open Hiptypes
open Pretty
open Subst
open Hiplib
open ProversEx

(* k(p,...) :- pi *)
(* type clause = string * string list * pi *)
type clause = pi
(* (pi -> pi) *)

(* forall x. 0 < x *)
type pred = string list * pi

let string_of_pred (_q, pi) =
  (* Format.asprintf "forall %s. %s" (string_of_list Fun.id q) (string_of_pi pi) *)
  (* Format.asprintf "forall %s. %s" (string_of_list Fun.id q)  *)
(string_of_pi pi)

(* let candidates = [
  ["z1"; "z2"], Atomic (LTEQ, Var "z1", Var "z2");
  ["z1"; "z2"], Atomic (LT, Num 0, Var "z2");
  ["z1"; "z2"], Atomic (LTEQ, Num 0, Var "z2")
]

let clauses = [
    "k", ["x"; "v"], (fun k ->
    Imply (Atomic (EQ, Var "c", Rel (LTEQ, Num 0, Var "x")), Imply (Atomic (EQ, Var "c", TTrue), Imply (Atomic (EQ, Var "v", Var "x"), k))));
    "k", ["x"; "v"], (fun k -> Imply (Atomic (EQ, Var "c", Rel (LTEQ, Num 0, Var "x")), Imply (Atomic (EQ, Var "c", TFalse),
    Imply (Atomic (EQ, Var "v", Minus (Num 0, Var "x")), k))));
]

let clauses = [
    "k", ["x"; "v"], Imply (Atomic (EQ, Var "c", Rel (LTEQ, Num 0, Var "x")), Imply (Atomic (EQ, Var "c", TTrue), Imply (Atomic (EQ, Var "v", Var "x"), Predicate ("k", [Var "x"; Var "v"]))));
    "k", ["x"; "v"], Imply (Atomic (EQ, Var "c", Rel (LTEQ, Num 0, Var "x")), Imply (Atomic (EQ, Var "c", TFalse),
    Imply (Atomic (EQ, Var "v", Minus (Num 0, Var "x")), Predicate ("k", [Var "x"; Var "v"]))));
]


let other_clauses = [
    Imply (Atomic (LTEQ, Var "y", Var "z"), Imply (Atomic (EQ, Var "c", Rel (LTEQ, Num 0, Var "z")), Imply (Atomic (EQ, Var "b", Var "c"), Atomic (EQ, Var "b", TTrue))))
] *)

let candidates = [
  ["x"; "y"; "z"; "i"; "temp"], Atomic (EQ, Var "i", Num 0);
  ["x"; "y"; "z"; "i"; "temp"], Not (Atomic (EQ, Var "i", Num 0));
  ["x"; "y"; "z"; "i"; "temp"], Atomic (GTEQ, Var "i", Num 0);
  ["x"; "y"; "z"; "i"; "temp"], Atomic (GT, Var "i", Num 0);
  ["x"; "y"; "z"; "i"; "temp"], Atomic (LT, Var "i", Num 10000);
  ["x"; "y"; "z"; "i"; "temp"], Atomic (LTEQ, Var "i", Num 10000);
  ["x"; "y"; "z"; "i"; "temp"], Not (Atomic (EQ, Var "x", Var "y"));
]

let clauses = [
    (* "inv", ["x"; "y"; "z"; "i"; "temp"], *)
    Imply (conj [Atomic (EQ, Var "x", Num 1); Atomic (EQ, Var "y", Num 2); Atomic (EQ, Var "z", Num 3); Atomic (EQ, Var "i", Num 0)], Predicate ("inv", [Var "x"; Var "y"; Var "z"; Var "i"; Var "temp"]));
    (* "inv", ["x"; "y"; "z"; "i"; "temp"], *)

    Imply (conj [Predicate ("inv", [Var "x"; Var "y"; Var "z"; Var "i"; Var "temp"]); Atomic (LT, Var "i", Num 10000);
    Atomic (EQ, Var "temp1", Var "x");
    Atomic (EQ, Var "x1", Var "y");
    Atomic (EQ, Var "y1", Var "z");
    Atomic (EQ, Var "z1", Var "temp");
    Atomic (EQ, Var "i1", Plus (Var "i", Num 1));
    ], Predicate ("inv", [Var "x1"; Var "y1"; Var "z1"; Var "i1"; Var "temp1"]));
]

let other_clauses = [
]

let replace_predicate name f pi =
  let vis=
    object
      (* (self) *)
      inherit [_] map_spec as super

      method! visit_Predicate _ p args =
        if p = name then
        (* (Format.printf "pred %s@." p; *)
          f args
          (* ) *)
        else super#visit_Predicate () p args
        (* else Predicate (self#visit_string () p, List.map (self#visit_term ()) args) *)
    end
  in vis#visit_pi () pi

(* let expand_candidates cs (_n, ps) =
  cs |> List.concat_map (fun (par, body) ->
  [instantiatePure (List.map2 (fun a b -> a, Var b) par ps) body]) *)

(* k -> fml /\ ... *)
type solution = pi list SMap.t

let verify (cs : clause list) (ps : pred list) : pred list =
  (* return refuted candidates of one constraint *)
  let ev =
  cs |> List.map (fun cb -> 
    let r =
    ps |> List.filter (fun (pp, pb) ->
      (* let body = cb in *)
      (* instantiatePure (List.map2 (fun a b -> a, Var b) pp cp) cb in *)
      (* let head =
        let bs = List.map2 (fun a b -> a, Var b) pp cp in
        (* Format.printf "replacing %s@." (string_of_list (string_of_pair Fun.id string_of_term) bs); *)
        instantiatePure bs pb
      in *)
      let fml = replace_predicate "inv" (fun args ->
        let bs = List.map2 (fun a b ->
          (* Format.printf "%s->%s@."a (string_of_term b); *)
          a, b) pp args in
        (* Format.printf "replacing %s in %s@." (string_of_list (string_of_pair Fun.id string_of_term) bs) (string_of_pi pb); *)
        instantiatePure bs pb
        ) cb in
      let r =
      ProversEx.is_valid True fml
      in
      Format.printf "%s: %b@." (string_of_pi fml) r;
      not r
      )
    in r
    )
  in
  ev |>
  List.find_opt (fun e -> not (e = []))
  |> Option.value ~default:[]

let houdini () =
  (* : pi list SMap.t = *)
    (* let initial =  expand_candidates candidates ("k", ["x"; "v"]) in *)
    (* let initial = expand_candidates candidates ("inv", ["x"; "y"; "z"; "i"; "temp"]) in *)

    let rec loop candidates =
      Format.printf "---\nITERATION@.";
      Format.printf "candidates: %s@." (string_of_list string_of_pred candidates);
      let e = verify clauses candidates in
      Format.printf "rejected: %s@." (string_of_list string_of_pred e);
      match e with
      | [] -> Format.printf "end@."
      | _ :: _ -> loop (List.filter (fun c -> not (List.mem c e)) candidates)
    in
    loop candidates

    (* failwith "ok" *)

(* let () = houdini () *)