open Core.Syntax
open Bindlib

let rec make_applications_nary t =
  match t with
  | True | Unit | False | Nil | Emp | Var _ | Symbol _ | Int _ | ONone -> t
  | Apply (f, a) ->
      let rec flatten t =
        match t with
        | Apply (f, a) ->
            let f1, a1 = flatten f in
            (f1, a :: a1)
        | _ -> (t, [])
      in
      let f1, a1 = flatten f in
      let args_list = List.concat (List.rev (a :: a1)) in
      Apply (make_applications_nary f1, List.map make_applications_nary args_list)
  | Tuple ts -> Tuple (List.map make_applications_nary ts)
  | Binop (op, t1, t2) -> Binop (op, make_applications_nary t1, make_applications_nary t2)
  | OSome t -> OSome (make_applications_nary t)
  | Unop (op, t) -> Unop (op, make_applications_nary t)
  | Conj (t1, t2) -> Conj (make_applications_nary t1, make_applications_nary t2)
  | Disj (t1, t2) -> Disj (make_applications_nary t1, make_applications_nary t2)
  | Implies (t1, t2) -> Implies (make_applications_nary t1, make_applications_nary t2)
  | Wand (t1, t2) -> Wand (make_applications_nary t1, make_applications_nary t2)
  | Subsumes (t1, t2) -> Subsumes (make_applications_nary t1, make_applications_nary t2)
  | PointsTo (t1, t2) -> PointsTo (make_applications_nary t1, make_applications_nary t2)
  | SepConj (t1, t2) -> SepConj (make_applications_nary t1, make_applications_nary t2)
  | Requires t -> Requires (make_applications_nary t)
  | Ensures t -> Ensures (make_applications_nary t)
  | Sequence (t1, t2) -> Sequence (make_applications_nary t1, make_applications_nary t2)
  | Reset t -> Reset (make_applications_nary t)
  | Fun b ->
      let vars, body = Bindlib.unmbind b in
      let body' = make_applications_nary body in
      let b' = Bindlib.unbox (Bindlib.bind_mvar vars (box_term body')) in
      Fun b'
  | Forall b ->
      let vars, body = Bindlib.unmbind b in
      let body' = make_applications_nary body in
      let b' = Bindlib.unbox (Bindlib.bind_mvar vars (box_term body')) in
      Forall b'
  | Exists b ->
      let vars, body = Bindlib.unmbind b in
      let body' = make_applications_nary body in
      let b' = Bindlib.unbox (Bindlib.bind_mvar vars (box_term body')) in
      Exists b'
  | Shift b ->
      let var, body = Bindlib.unbind b in
      let body' = make_applications_nary body in
      let b' = Bindlib.unbox (Bindlib.bind_var var (box_term body')) in
      Shift b'
  | Bind (s, b) ->
      let s' = make_applications_nary s in
      let var, body = unbind b in
      let body' = make_applications_nary body in
      let b' = unbox (bind_var var (box_term body')) in
      Bind (s', b')

let rec convert_apps_to_options t =
  match t with
  | True | Unit | False | Nil | Emp | Var _ | Int _ | ONone | OSome _ -> t
  | Symbol { sym_name = "None" } -> ONone
  | Symbol _ -> t
  | Apply (Symbol { sym_name = "Some" }, [arg]) -> OSome (convert_apps_to_options arg)
  | Apply (f, args) -> Apply (convert_apps_to_options f, List.map convert_apps_to_options args)
  | Tuple ts -> Tuple (List.map convert_apps_to_options ts)
  | Binop (op, t1, t2) -> Binop (op, convert_apps_to_options t1, convert_apps_to_options t2)
  | Unop (op, t) -> Unop (op, convert_apps_to_options t)
  | Conj (t1, t2) -> Conj (convert_apps_to_options t1, convert_apps_to_options t2)
  | Disj (t1, t2) -> Disj (convert_apps_to_options t1, convert_apps_to_options t2)
  | Implies (t1, t2) -> Implies (convert_apps_to_options t1, convert_apps_to_options t2)
  | Wand (t1, t2) -> Wand (convert_apps_to_options t1, convert_apps_to_options t2)
  | Subsumes (t1, t2) -> Subsumes (convert_apps_to_options t1, convert_apps_to_options t2)
  | PointsTo (t1, t2) -> PointsTo (convert_apps_to_options t1, convert_apps_to_options t2)
  | SepConj (t1, t2) -> SepConj (convert_apps_to_options t1, convert_apps_to_options t2)
  | Requires t -> Requires (convert_apps_to_options t)
  | Ensures t -> Ensures (convert_apps_to_options t)
  | Sequence (t1, t2) -> Sequence (convert_apps_to_options t1, convert_apps_to_options t2)
  | Reset t -> Reset (convert_apps_to_options t)
  | Fun b ->
      let vars, body = Bindlib.unmbind b in
      let body' = convert_apps_to_options body in
      let b' = Bindlib.unbox (Bindlib.bind_mvar vars (box_term body')) in
      Fun b'
  | Forall b ->
      let vars, body = Bindlib.unmbind b in
      let body' = convert_apps_to_options body in
      let b' = Bindlib.unbox (Bindlib.bind_mvar vars (box_term body')) in
      Forall b'
  | Exists b ->
      let vars, body = Bindlib.unmbind b in
      let body' = convert_apps_to_options body in
      let b' = Bindlib.unbox (Bindlib.bind_mvar vars (box_term body')) in
      Exists b'
  | Shift b ->
      let var, body = Bindlib.unbind b in
      let body' = convert_apps_to_options body in
      let b' = Bindlib.unbox (Bindlib.bind_var var (box_term body')) in
      Shift b'
  | Bind (s, b) ->
      let s' = convert_apps_to_options s in
      let var, body = unbind b in
      let body' = convert_apps_to_options body in
      let b' = unbox (bind_var var (box_term body')) in
      Bind (s', b')

let postprocess t = t |> make_applications_nary |> convert_apps_to_options
