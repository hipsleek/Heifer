(* open Why3
open Core.Syntax

let term_to_why3 (t : term) =
  match t with
  | TUnit -> Term.t_tuple []
  | TTrue | TFalse | TNil | TVar _ | TInt _ | TFun _ | TTuple _
  | TBinop (_, _, _)
  | TUnop (_, _) ->
    failwith "todo"

let rec pi_to_why3 (p : prop) =
  (* Format.printf "pi %s@." (Pretty.string_of_pi pi); *)
  match p with
  | PAtom t -> term_to_why3 t (* | PConj (a, b) -> Term.t_false *)
  | PConj (a, b) ->
    Term.t_and (pi_to_why3 a) (pi_to_why3 b)
    (* | Or (a, b) -> Term.t_or (pi_to_why3 env a) (pi_to_why3 env b)
    | Imply (a, b) -> Term.t_implies (pi_to_why3 env a) (pi_to_why3 env b)
    | Not a -> Term.t_not (pi_to_why3 env a) *)
  | PImplies (_, _) | PSubsumes (_, _) -> failwith ""

(* let rec term_to_why3 env (t : term) =
    (* Format.printf "term %s@." (Pretty.string_of_term t); *)
    match t.term_desc with
    | Const ValUnit -> (Term.t_tuple [], Unit)
    | Const (Num i) ->
      Theories.(needed int env.theories);
      (Term.t_nat_const i, Int)
    | TLambda (_, _, _, _) ->
      Theories.(needed int env.theories);
      failwith "not updated" (* (Term.t_nat_const (Subst.hash_lambda t), Int) *)
    | Var v when SMap.mem v env.tenv ->
      let ty1 = SMap.find v env.tenv (* |> Option.value ~default:Int *) in
      let ty = type_to_why3 env ty1 in
      let name =
        match SMap.find_opt v env.exists with
        | Some v -> Term.t_var v
        | None ->
          (match SMap.find_opt v env.forall with
          | None ->
            let name = Ident.id_fresh v in
            (* let sym = Term.create_lsymbol name [] (Some ty) in *)
            let sym = Term.create_vsymbol name ty in
            env.forall <- SMap.add v sym env.forall;
            Term.t_var sym
            (* Term.t_app sym [] (Some ty) *)
          | Some vv ->
            (* Term.t_app vv [] (Some ty) *)
            Term.t_var vv)
      in
      (* Format.printf "var %s : %s@." v
         Pretty.(
           string_of_option string_of_type (SMap.find_opt v env.tenv)); *)
      (name, ty1)
    | Var v -> failwith (Format.asprintf "variable %s has no type" v)
    | BinOp (SConcat, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer
          Theories.(get_symbol string "concat" env.theories)
          [a1; b1],
        Int )
    | BinOp (Plus, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer
          Theories.(get_symbol int "infix +" env.theories)
          [a1; b1],
        Int )
    | BinOp (Minus, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer
          Theories.(get_symbol int "infix -" env.theories)
          [a1; b1],
        Int )
    | Rel (EQ, a, b) ->
      let a1, t1 = term_to_why3 env a in
      let b1, t2 = term_to_why3 env b in
      ( (match (t1, t2) with
        | Int, Int ->
          Term.fs_app
            (* Theories.(get_symbol int "infix =" env.theories) *)
            Theories.(get_symbol extras "eqi" env.theories)
            [a1; b1] Ty.ty_bool
        | Bool, Bool ->
          Term.t_app_infer
            Theories.(get_symbol extras "eqb" env.theories)
            [a1; b1]
        | _, _ ->
          failwith
            (Format.asprintf "equality not defined between types %s and %s"
               (Pretty.string_of_type t1) (Pretty.string_of_type t2))),
        Bool )
    | Rel (GT, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer
          Theories.(get_symbol int "infix >" env.theories)
          [a1; b1],
        Bool )
    | Rel (LT, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer
          Theories.(get_symbol int "infix <" env.theories)
          [a1; b1],
        Bool )
    | Rel (GTEQ, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer
          Theories.(get_symbol int "infix >=" env.theories)
          [a1; b1],
        Bool )
    | Rel (LTEQ, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer
          Theories.(get_symbol int "infix <=" env.theories)
          [a1; b1],
        Bool )
    | Const TTrue ->
      Theories.(needed bool env.theories);
      (Term.t_bool_true, Bool)
    | Const TFalse ->
      Theories.(needed bool env.theories);
      (Term.t_bool_false, Bool)
    | BinOp (TAnd, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer Theories.(get_symbol bool "andb" env.theories) [a1; b1],
        Bool )
      (* Term.fs_app  [] Ty.ty_bool *)
      (* Term.t_and (term_to_why3 env a) (term_to_why3 env b) *)
    | BinOp (TOr, a, b) ->
      (* Term.t_and (term_to_why3 env a) (term_to_why3 env b) *)
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer Theories.(get_symbol bool "orb" env.theories) [a1; b1],
        Bool )
    | TNot a ->
      (* Term.t_not (term_to_why3 env a) *)
      let a1, _ = term_to_why3 env a in
      ( Term.t_app_infer Theories.(get_symbol bool "notb" env.theories) [a1],
        Bool )
    | BinOp (TCons, _, _) ->
      (* let a1, _ = term_to_why3 env a in *)
      (* let b1, _ = term_to_why3 env b in *)
      (* let open Pretty in *)
      (* Format.printf "cons %s %s @." (string_of_term a) (string_of_term b); *)
      (* ( Term.t_app *)
      (*     Theories.(get_symbol list "Cons" env.theories) *)
      (*     [a1; b1] *)
      (*     (Some (type_to_why3 env List_int)), *)
      (*   List_int ) *)
      (* inferring types leads to issues reconciling types between systems *)
        failwith "TODO type inference on cons symbol"
      (* Term.t_app_infer
         (get_theory_symbol env.list_theory "Cons")
         [term_to_why3 env a; term_to_why3 env b] *)
    | Const Nil ->
      (* Term.t_app_infer (get_theory_symbol env.list_theory "Nil") [] *)
      (* ( Term.t_app *)
      (*     Theories.(get_symbol list "Nil" env.theories) *)
      (*     [] *)
      (*     (Some (type_to_why3 env List_int)), *)
      (*   List_int ) *)
        failwith "TODO type inference on nil symbol"
    | TApp (s, args) when Globals.is_pure_fn_defined s ->
      let args1 = List.map (term_to_why3 env) args |> List.map fst in
      let defn = Globals.pure_fn s
      (* |> Hipcore.Typedhip.Untypehip.untype_pure_fn_def *)
      in
      let ret_typ = type_to_why3 env defn.pf_ret_type in
      (* Format.printf "app %s@." s; *)
      ( Term.t_app (SMap.find s env.fn_names) args1 (Some ret_typ),
        defn.pf_ret_type )
    | TApp (s, _) -> failwith (Format.asprintf "unknown function term %s" s)
    | BinOp (TPower, _, _) -> failwith "TPower nyi"
    | BinOp (TTimes, _, _) -> failwith "TTimes nyi"
    | BinOp (TDiv, _, _) -> failwith "TDiv nyi"
    | TTuple _ -> failwith "TTupple nyi"
    | Const (TStr _) -> failwith "TStr nyi"
    | Construct _ -> failwith "constructors not yet supported"

  let rec pi_to_why3 env (pi : pi) =
    (* Format.printf "pi %s@." (Pretty.string_of_pi pi); *)
    match pi with
    | True -> Term.t_true
    | False -> Term.t_false
    | Atomic (EQ, a, b) ->
      let a1, t1 = term_to_why3 env a in
      let b1, t2 = term_to_why3 env b in
      (match (t1, t2) with
      | Bool, Bool ->
        (* Term.t_app_infer Theories.(get_symbol extras "eqb" env.theories) [a1; b1] *)
        Term.t_equ a1 b1
      | _, _ ->
        (* this seems to be ok *)
        Term.t_equ a1 b1)
    | Atomic (GT, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      Term.t_app_infer Theories.(get_symbol int "infix >" env.theories) [a1; b1]
    | Atomic (LT, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      Term.t_app_infer Theories.(get_symbol int "infix <" env.theories) [a1; b1]
    | Atomic (GTEQ, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      Term.t_app_infer
        Theories.(get_symbol int "infix >=" env.theories)
        [a1; b1]
    | Atomic (LTEQ, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      Term.t_app_infer
        Theories.(get_symbol int "infix <=" env.theories)
        [a1; b1]
    | And (a, b) -> Term.t_and (pi_to_why3 env a) (pi_to_why3 env b)
    | Or (a, b) -> Term.t_or (pi_to_why3 env a) (pi_to_why3 env b)
    | Imply (a, b) -> Term.t_implies (pi_to_why3 env a) (pi_to_why3 env b)
    | Not a -> Term.t_not (pi_to_why3 env a)
    | Predicate (_, _) -> failwith "nyi Predicate"
    | Subsumption (_, _) -> pi_to_why3 env True *) *)
