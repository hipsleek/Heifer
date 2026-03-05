open Core_lang
open Core.Syntax

let resolve_to_primitive f args =
  match (f, args) with
  | Core_lang.Var op, [arg1; arg2] ->
      (match op with
      | "+" -> Some (Mk.binop Plus arg1 arg2)
      | "-" -> Some (Mk.binop Minus arg1 arg2)
      | "*" | "*." ->
          (* there is no separation logic in core lang, so this seems okay *)
          Some (Mk.binop Times arg1 arg2)
      | "=" -> Some (Mk.binop Eq arg1 arg2)
      | "<>" -> Some (Mk.binop Neq arg1 arg2)
      | "<" -> Some (Mk.binop Lt arg1 arg2)
      | "<=" -> Some (Mk.binop Le arg1 arg2)
      | ">" -> Some (Mk.binop Gt arg1 arg2)
      | ">=" -> Some (Mk.binop Ge arg1 arg2)
      | "::" -> Some (Mk.binop Cons arg1 arg2)
      | _ -> None)
  | Var op, [arg] ->
      (match op with
      | "not" -> Some (Mk.unop Not arg)
      | "~-" | "-" -> Some (Mk.unop Neg arg)
      | _ -> None)
  | _ -> None

let rec convert_box (env : (string * term Bindlib.var) list) (t : expr) : term Bindlib.box =
  match t with
  | Var x ->
      (match List.assoc_opt x env with
      | Some v -> Mk.var v
      | None -> Mk.symbol { sym_name = x })
  | Int i -> Mk.int i
  | Fun (xs, body) ->
      let vars = Array.map (fun x -> Bindlib.new_var (fun v -> Var v) x) (Array.of_list xs) in
      let env' = List.combine xs (Array.to_list vars) @ env in
      let body' = convert_box env' body in
      Mk.fun_ (Bindlib.bind_mvar vars body')
  | Apply (f, args) ->
      let f_box = convert_box env f in
      let args_box = List.map (convert_box env) args in
      resolve_to_primitive f args_box
      |> Option.value ~default:(Mk.apply f_box (Bindlib.box_list args_box))
  | Let (x, t1, t2) ->
      let v = Bindlib.new_var (fun v -> Var v) x in
      let t1' = convert_box env t1 in
      let t2' = convert_box ((x, v) :: env) t2 in
      Mk.bind t1' (Bindlib.bind_var v t2')
  | Sequence (t1, t2) -> Mk.sequence (convert_box env t1) (convert_box env t2)
  | Shift (k, body) ->
      let v = Bindlib.new_var (fun v -> Var v) k in
      let body' = convert_box ((k, v) :: env) body in
      Mk.shift (Bindlib.bind_var v body')
  | Reset t1 -> Mk.reset (convert_box env t1)
  | WithSpec (t, _spec, _name) -> convert_box env t
  | Match _ | If _ | Perform _ | Resume _ ->
      failwith "conversion to Syntax.term not yet supported for this construct"

let apply (t : expr) : term = Bindlib.unbox (convert_box [] t)
