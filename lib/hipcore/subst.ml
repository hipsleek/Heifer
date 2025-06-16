open Hiptypes
open Syntax
open Pretty

let free_vars, free_vars_term, free_vars_heap, free_vars_pure =
  let visitor =
    object (_)
      inherit [_] reduce_spec as super
      method zero = SSet.empty
      method plus = SSet.union

      method! visit_Exists () x f =
        let b = super#visit_Exists () x f in
        SSet.remove x b

      method! visit_ForAll () x f =
        let b = super#visit_ForAll () x f in
        SSet.remove x b

      method! visit_TLambda () h ps sp b =
        let b = super#visit_TLambda () h ps sp b in
        List.fold_right (fun c t -> SSet.remove c t) ps b

      method! visit_Bind () x f1 f2 =
        let b = super#visit_Bind () x f1 f2 in
        SSet.remove x b

      method! visit_HigherOrder () f v =
        let b = super#visit_HigherOrder () f v in
        SSet.add f b

      method! visit_Var () x = SSet.singleton x
    end
  in
  ( (fun f -> visitor#visit_staged_spec () f),
    (fun t -> visitor#visit_term () t),
    (fun h -> visitor#visit_kappa () h),
    fun p -> visitor#visit_pi () p )

let%expect_test "free vars" =
  let test s = Format.printf "%s@." (Pretty.string_of_sset s) in

  free_vars (HigherOrder ("x", [Var "z"])) |> test;
  [%expect {| {x, z} |}];

  free_vars (ens ~p:(eq (v "res") (num 1)) ()) |> test;
  [%expect {| {res} |}]

let rec find_binding x bindings =
  match bindings with
  | [] -> Var x
  | (name, v) :: xs -> if String.equal name x then v else find_binding x xs

(* replaces free variables *)
let subst_free_vars bs staged =
  let subst_visitor free =
    object (self)
      inherit [_] map_spec

      (* most of the work done by this visitor is done here *)
      method! visit_Var bindings v = find_binding v bindings

      (* we allow substituting into function names too *)
      method! visit_HigherOrder bindings f v =
        let v1 = self#visit_list self#visit_term bindings v in
        match find_binding f bindings with
        | Var f1 -> HigherOrder (f1, v1)
        | _ -> failwith "invalid"

      (* the remaining cases handle capture-avoidance in binders *)
      method! visit_Shift bindings nz k body =
        let k1, body1 =
          if SSet.mem k free then
            let y = Variables.fresh_variable ~v:k () in
            (y, self#visit_staged_spec [(k, Var y)] body)
          else (k, body)
        in
        let bs = List.filter (fun (b, _) -> b <> k1) bindings in
        Shift (nz, k1, self#visit_staged_spec bs body1)

      method! visit_Exists bindings x f =
        let x1, f1 =
          if SSet.mem x free then
            let y = Variables.fresh_variable ~v:x () in
            (y, self#visit_staged_spec [(x, Var y)] f)
          else (x, f)
        in
        let bs = List.filter (fun (b, _) -> b <> x1) bindings in
        Exists (x1, self#visit_staged_spec bs f1)

      method! visit_ForAll bindings x f =
        let x1, f1 =
          if SSet.mem x free then
            let y = Variables.fresh_variable ~v:x () in
            (y, self#visit_staged_spec [(x, Var y)] f)
          else (x, f)
        in
        let bs = List.filter (fun (b, _) -> b <> x1) bindings in
        ForAll (x1, self#visit_staged_spec bs f1)

      method! visit_Bind bindings x f1 f2 =
        let x1, f2 =
          if SSet.mem x free then
            let y = Variables.fresh_variable ~v:x () in
            (y, self#visit_staged_spec [(x, Var y)] f2)
          else (x, f2)
        in
        let bs = List.filter (fun (b, _) -> b <> x1) bindings in
        Bind (x1, self#visit_staged_spec bs f1, self#visit_staged_spec bs f2)

      method! visit_TLambda bindings name params sp body =
        let params1, sp1, body1 =
          List.fold_right
            (fun p (ps, sp, body) ->
              if SSet.mem p free then
                let y = Variables.fresh_variable ~v:p () in
                ( p :: ps,
                  self#visit_option self#visit_staged_spec [(p, Var y)] sp,
                  self#visit_option self#visit_core_lang [(p, Var y)] body )
              else (p :: ps, sp, body))
            params ([], sp, body)
        in
        let bs =
          List.filter (fun (b, _) -> not (List.mem b params1)) bindings
        in
        TLambda
          ( name,
            params1,
            self#visit_option self#visit_staged_spec bs sp1,
            self#visit_option self#visit_core_lang bs body1 )

      method! visit_CLambda bindings params sp body =
        let params1, sp1, body1 =
          List.fold_right
            (fun p (ps, sp, body) ->
              if SSet.mem p free then
                let y = Variables.fresh_variable ~v:p () in
                ( p :: ps,
                  self#visit_option self#visit_staged_spec [(p, Var y)] sp,
                  self#visit_core_lang [(p, Var y)] body )
              else (p :: ps, sp, body))
            params ([], sp, body)
        in
        let bs =
          List.filter (fun (b, _) -> not (List.mem b params1)) bindings
        in
        CLambda
          ( params1,
            self#visit_option self#visit_staged_spec bs sp1,
            self#visit_core_lang bs body1 )
    end
  in
  let free = List.map snd bs |> List.map free_vars_term |> SSet.concat in
  (subst_visitor free)#visit_staged_spec bs staged

let%expect_test "subst" =
  Variables.reset_counter 0;
  let test bs f1 =
    let f2 = subst_free_vars bs f1 in
    Format.printf "(%s)%s = %s@." (string_of_staged_spec f1)
      (string_of_list
         (fun (x, t) -> Format.asprintf "%s/%s" (string_of_term t) x)
         bs)
      (string_of_staged_spec f2)
  in

  test [("z", v "a")] (HigherOrder ("x", [v "z"]));
  [%expect {| (x(z))[a/z] = x(a) |}];

  test [("x", v "y")] (HigherOrder ("x", [v "z"]));
  [%expect {| (x(z))[y/x] = y(z) |}];

  (* capture-avoidance *)
  test
    [("x", v "y")]
    (seq
       [
         ens ~p:(eq (v "x") (v "x")) ();
         Exists ("x", ens ~p:(eq (v "x") (num 1)) ());
       ]);
  [%expect {| (ens x=x; ex x. (ens x=1))[y/x] = ens y=y; ex x. (ens x=1) |}];

  test [("x", v "z")] (Exists ("z", ens ~p:(eq (v "z") (v "x")) ()));
  [%expect {| (ex z. (ens z=x))[z/x] = ex z0. (ens z0=z) |}]
