open Hiptypes

let (let*) xs f = List.concat_map f xs
let (let+) xs f = List.map f xs
let return x = [x]

let cartesian_product (lists: 'a list list) : 'a list list =
  List.fold_right (fun ls result -> let* x = ls in let* rest = result in return (x::rest)) lists [[]]

let pattern_of_constr ((name, args) : Types.type_constructor) =
  PConstr (name, List.map (fun _ -> PAny) args)

let strip_bound_names =
  let visitor = object
    inherit [_] map_spec
    method! visit_PVar _ _ = PAny
  end in
  visitor#visit_pattern ()

(** Return a set of patterns that match terms of the same type as [pat] such that
    - If a term does not match pat, it matches at least one pattern in this list.
    - If a term matches pat, it does not match any pattern in the list. *)
let rec complement pat =
    match pat with
    | PAny | PVar _ -> []
    | PAlias (pat, name) -> complement pat |> List.map (fun pat -> PAlias (pat, name))
    | PConstr (name, args) ->
      let type_decl, _ = Globals.type_constructor_decl name in begin
      match type_decl.tdecl_kind with
      | Tdecl_record _ -> failwith "record patterns currently not implemented"
      | Tdecl_inductive constrs ->
        let self_complements =
          (* TODO we can make this more efficient by taking argument sets
             with only exactly one `Mismatch 
             this is at the cost of the return set no longer being disjoint *)
          args
          |> List.map (fun arg ->
            let complements = complement arg in
            (`Match arg) :: (List.map (fun pat -> `Mismatch pat) complements))
          |> cartesian_product
          |> List.filter (fun args -> List.exists (function `Mismatch _ -> true | _ -> false) args)
          |> List.map (List.map (function `Mismatch pat | `Match pat -> pat))
          |> List.map (fun args -> PConstr (name, args))
        (* create patterns for all the other constructors *)
        in
        let other_constr_patterns =
          constrs
            |> List.filter (fun (other_name, _) -> name <> other_name)
            |> List.map pattern_of_constr
        in
        other_constr_patterns @ self_complements
      end
    | PConstant _ -> failwith "constant patterns currently not implemented"


(** Find the intersection of all pairs of patterns in [pxs] and [pys]. 
  Only the bound names from patterns in pxs are preserved. *)
let rec intersect (pxs : pattern list) (pys : pattern list) : pattern list =
  let rec intersect_two p1 p2 = match p1, p2 with
    | PAny, other -> return (strip_bound_names other)
    | PVar name, other -> return (PAlias (strip_bound_names other, name))
    | other, (PVar _ | PAny) -> return other
    | PAlias (p, s), other -> 
        let* overlap = intersect_two p other in
        return (PAlias (overlap, s))
    | other, PAlias (p, _) -> intersect_two other p
    | PConstr (name1, args1), PConstr (name2, args2) when name1 = name2 ->
        let* args = 
          List.combine args1 args2
          |> List.map (fun (arg1, arg2) -> intersect [arg1] [arg2])
          |> cartesian_product
        in
        return (PConstr (name1, args))
    | _, _ -> []
  in
  let* px = pxs in
  let* py = pys in
  intersect_two px py

let exclude pat excluded =
  let open Pretty in
  let open Debug in
  let@_ = span (fun r -> 
    debug ~at:5 ~title:"excluded patterns"
    "excluded at inputs %s %s -> %s \n" (string_of_pattern pat) (string_of_list string_of_pattern excluded)
    (string_of_result (string_of_list string_of_pattern) r))
  in
  List.fold_left intersect [pat] (List.map complement excluded)

  (** Generates a pure formula corresponding to [pat_term]
  matching under the pattern. The corresponding list is
  the free variables in the formula. *)
let pi_of_pattern pat_term pat : string list * pi =
  let conjuncts = ref [] in
  let free_vars = ref [] in
  let add_free_var v = free_vars := v::!free_vars in
  let add_conjunct pi = conjuncts := pi::!conjuncts in
  let new_term_name () = let v = Variables.fresh_variable ~v:"pat" () in add_free_var v; v in
  let rec inner pat =
    match pat with
    | PAny ->
        let v = new_term_name () in
        Var v
    | PVar v ->
        add_free_var v;
        Var v
    | PConstr (name, args) ->
        Construct (name, List.map inner args)
    | PConstant c ->
        let v = new_term_name () in
        add_conjunct (Atomic (EQ, Var v, Const c));
        Var v
    | PAlias (p, v) ->
        let inner_term = inner p in
        add_conjunct (Atomic (EQ, Var v, inner_term));
        Var v
  in
  add_conjunct (Atomic (EQ, pat_term, inner pat));
  !free_vars, Syntax.conj !conjuncts

let setup_tests () = 
  let open Globals in
  define_type {
    tdecl_name = "test_type";
    tdecl_params = [];
    tdecl_kind = Tdecl_inductive [
      "A", [];
      "B", [Int];
      "D", [TConstr ("test_type", []); TConstr ("test_type", [])]
    ]
  };
  define_type {
    tdecl_name = "nat";
    tdecl_params = [];
    tdecl_kind = Tdecl_inductive [
      "Z", [];
      "S", [TConstr ("nat", [])]
    ]
  }

let%expect_test "complement" =
  setup_tests ();
  let output pats = String.concat " | " (List.map Pretty.string_of_pattern pats) |> print_string in

  output (complement (PConstr ("B", [PAny])));
  [%expect{| A() | D(_, _) |}];

  output (complement (PConstr ("D", [PConstr ("B", [PAny]); PConstr ("A", [])])));
  [%expect{| A() | B(_) | D(B(_), B(_)) | D(B(_), D(_, _)) | D(A(), A()) | D(A(), B(_)) | D(A(), D(_, _)) | D(D(_, _), A()) | D(D(_, _), B(_)) | D(D(_, _), D(_, _)) |}];

  output (complement (PConstr ("S", [PAlias (PConstr ("S", [PAny]), "s")])));
  [%expect{| Z() | S((Z()) as s) |}];
;;
  
let%expect_test "intersect" =
  setup_tests ();
  let output pats = String.concat " | " (List.map Pretty.string_of_pattern pats) |> print_string in

  output (intersect [PConstr ("D", [PVar "a"; PVar "b"])] [PConstr ("B", [PVar "x"]); PConstr ("D", [PAny; PConstr ("D", [PAny; PVar "d"])])]);
  [%expect{| D((_) as a, (D(_, _)) as b) |}];

  output (intersect [PConstr ("B", [PAny])] [PConstr ("D", [PAny; PAny])]);
  [%expect{| |}];

  output (intersect [PConstr ("D", [PConstr ("D", [PVar "z"; PAny]); PAny])] 
    [PConstr ("D", [PAny; PConstr ("D", [PAny; PVar "y"])])]);
  [%expect{| D(D(z, _), D(_, _)) |}];
;;

let%expect_test "exclude" =
  setup_tests ();
  let output pats = String.concat " | " (List.map Pretty.string_of_pattern pats) |> print_string in

  output (exclude (PConstr ("D", [PAny; PAny])) [PConstr ("A", []); PConstr ("D", [PConstr ("B", [PAny]); PAny])]);
  [%expect{| D(A(), _) | D(D(_, _), _) |}];

  output (exclude (PConstr ("B", [PAny])) []);
  [%expect{| B(_) |}];

  output (exclude (PConstr ("S", [PAlias (PConstr ("Z", []), "s")])) [PConstr ("Z", []); PConstr ("S", [PAlias (PConstr ("S", [PAny]), "s")])]);
  [%expect{| S((Z()) as s) |}];
;;


