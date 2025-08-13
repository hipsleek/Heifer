
type typ =
  (* The order of constructors is important:
    - base types
    - type constructors
    - type variables
    This is because type unification reduces a type to its "simplest form" given constraints,
    and constructors earlier in the list are treated as "simpler". *)
  (* dynamic type that can unify with anything else. this is an escape hatch for extensions that cannot be typed under the standard ocaml type system *)
  | Any
  | Unit
  | Int
  | Bool
  | TyString
  | Lamb
  (* TODO do we need a Poly variant for generics? *)
  | Arrow of typ * typ
  | TConstr of string * typ list
  | TVar of string (* this is last, so > concrete types *)

[@@deriving show { with_path = false }, ord]

type type_constructor = string * typ list
type record_field = {
  field_name: string;
  field_type: typ;
}
type type_decl_kind =
  | Tdecl_inductive of type_constructor list
  | Tdecl_record of record_field list
type type_declaration = {
  tdecl_name: string;
  tdecl_params: typ list;
  tdecl_kind: type_decl_kind
}

(** Given a type declaration, and a constructor name, return
    the constructor's type as a pair of type parameters, and argument types.
    Return None if the constructor is not found, or if the type is not inductive. *)
let constructor_of_type_decl constr_name type_decl =
  match type_decl.tdecl_kind with
  | Tdecl_inductive constructors -> List.find_opt (fun (name, _) -> name = constr_name) constructors
    |> Option.map (fun (_name, args) -> (type_decl.tdecl_params, args))
  | _ -> None

(** Given a list of substitutions [(TVar s, t)], make these substitutions
    in another type t. *)
let rec instantiate_type_variables (vars: (typ * typ) list) (t : typ) : typ =
  match t with
  | TVar _ -> List.assoc_opt t vars |> Option.value ~default:t
  | TConstr (name, args) -> TConstr (name, List.map (instantiate_type_variables vars) args)
  | t -> t

let min_typ a b = if compare_typ a b <= 0 then a else b

let is_concrete_type t = match t with TVar _ -> false | _ -> true

let rec free_type_vars t =
  match t with
  | TVar v -> [v]
  | TConstr (_, args) -> (List.concat_map free_type_vars args)
  | Arrow (t1, t2) -> (free_type_vars t1) @ (free_type_vars t2)
  | _ -> []

let concrete_types = [Unit; Int; Bool; Lamb]

let new_type_var : ?name:string -> unit -> typ =
  let counter = ref 0 in begin
  fun ?(name="") () ->
    counter := !counter + 1;
    TVar (if name = "" then "tv" ^ string_of_int !counter else name)
  end
  (* fun ?(name=) _ -> TVar name *)

module TMap = Map.Make (struct
  type t = typ

  let compare = compare_typ

end)


open Common

module U = Utils.Union_find

module TEnv = struct
  type t = typ U.elem TMap.t ref

  (** [Cyclic_type t1 t2] is raised when, during type unification, t1's value
      is found to rely on t2. *)
  exception Cyclic_type of typ * typ

  let create () =
    (* TODO this may break, since we now need to lazily create entries for concrete
    types as they are added to the list. *)
    TMap.empty

  let get_or_create m k =
    match TMap.find_opt k !m with
    | None ->
      let r = U.make k in
      m := TMap.add k r !m;
      r
    | Some v ->
      v

  let equate m t1 t2 =
    let t1r = get_or_create m t1 in
    let t2r = get_or_create m t2 in
    U.merge min_typ t1r t2r

  (** Attempt to resolve all type variables in t. (i.e. performs all
   unifications possible.) *)
  let simplify (m : t) t : typ =
    let rec inner ?(expanded = SMap.empty) t =
      match t with
      | TVar s ->
        let simplified = TMap.find_opt t !m
        |> Option.map U.get
        |> Option.value ~default:t in
        if simplified = t
        then simplified
        else if SMap.mem s expanded
        then raise (Cyclic_type (t, simplified))
        (* Add s to the do-not-expand list, to prevent a cyclic expansion of s. *)
        else inner ~expanded:(SMap.add s t expanded) simplified
      | TConstr (constr, args) -> 
          (* recurse into the constructor's arguments *)
          TConstr (constr, List.map (inner ~expanded:expanded) args)
      | Arrow (src, dst) ->
          Arrow (inner ~expanded:expanded src, inner ~expanded:expanded dst)
      | _ -> t
    in
    inner t

  (** Fully resolve all type variables in t. Returns None
    if some variables cannot be resolved.*)
  let rec concretize (m : t) t = 
    match t with
    | TVar _ -> 
      let equality = TMap.find_opt t !m |> Option.map U.get in
      Option.bind equality (fun equality ->
        match equality with
        (* If this is still a type variable, we have no concrete type for this variable. *)
        | TVar _ -> None
        (* Otherwise, this may still be, e.g. a constructor with type variables inside, so
           recursively concretize this type. *)
        | _ -> (concretize m equality))
    | TConstr (constr, args) -> 
        (* recurse into the constructor's arguments *)
        let concrete_args = List.map (concretize m) args in
        let concrete_args = List.fold_right (fun arg acc -> match arg, acc with
            | _, None | None, _ -> None
            | Some arg, Some acc -> Some (arg::acc)) concrete_args (Some [])
        in
        concrete_args |> Option.map (fun args -> TConstr (constr, args))
    | Arrow (src, dst) ->
        let (let*) f o = Option.bind f o in
        let* src = concretize m src in
        let* dst = concretize m dst in
        Some (Arrow (src, dst))
    | _ -> Some t

  (** Check if t is a fully concrete type. *)
  let has_concrete_type m t = concretize m t |> Option.is_some
end

(** Check if a type [src] can unify with type [dst]. *)
let rec can_unify_with src dst =
  match src, dst with
  | _, TVar _ | _, Any
  | TVar _, _ | Any, _ -> true
  | t1, t2 when t1 = t2 -> true
  | Arrow (a1, b1), Arrow (a2, b2) ->
    can_unify_with a1 a2 && can_unify_with b2 b1
  | TConstr (name1, args1), TConstr (name2, args2) when name1 = name2 ->
      List.length args1 = List.length args2
      && List.for_all2 can_unify_with args1 args2
  | _, _ -> false

type abs_typ_env = {
  (* formula variable -> type, which may be a variable *)
  vartypes: typ SMap.t;
  (* types of type variables so far *)
  equalities : TEnv.t;
}

let create_abs_env () =
  {
    vartypes = SMap.empty;
    equalities = ref (TEnv.create ()) ;
  }

let simplify_vartypes env =
  {env with vartypes = SMap.map (TEnv.simplify env.equalities) env.vartypes}

(* concrete type environment, where every variable has a concrete type *)
type typ_env = typ SMap.t
(* A map giving type variables possibly-concrete types *)

(* Definitions of a pure function's type *)
type pure_fn_type_def = {
  pft_name: string;
  pft_logic_path: string list;
  pft_logic_name: string;
  pft_params: typ list;
  pft_ret_type: typ;
}
