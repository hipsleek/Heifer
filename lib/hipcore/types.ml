(**
  Representation of types used in terms and the core language. *)

type typ = 
  | Unit
  | List_int
  | TConstr of string * typ list
  | Int
  | Bool
  | TyString
  | Lamb
  (* TODO do we need a Poly variant for generics? *)
  | Arrow of typ * typ
  | TVar of string (* this is last, so > concrete types *)
[@@deriving show { with_path = false }, ord]

type type_decl_kind =
  (* Inductive data type; each element of the list corresponds to a constructor. *)
  Tdecl_inductive of (string * typ list) list

type type_decl = {
  typ_name: string; (* name of type *)
  typ_params: typ list; (* list of type variables used in the declaration *)
  typ_kind: type_decl_kind
}

let min_typ a b = if compare_typ a b <= 0 then a else b

let is_concrete_type = function TVar _ -> false | _ -> true

let concrete_types = [Unit; List_int; Int; Bool; Lamb]

module U = struct
  include UnionFind

  let merge f a b = ignore (merge f a b)
end

module TMap = Map.Make (struct
  type t = typ

  let compare = compare_typ

end)

(* A map giving type variables possibly-concrete types *)
module TEnv = struct

  type t = typ U.elem TMap.t ref

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

  let concretize m t = TMap.find t !m |> U.get

  let has_concrete_type m t =
    match TMap.find_opt t !m with
    | None -> false
    | Some r -> is_concrete_type (U.get r)

end

type abs_typ_env = {
  (* formula variable -> type, which may be a variable *)
  vartypes: typ Common.SMap.t;
  (* types of type variables so far *)
  equalities : TEnv.t;
}

let create_abs_env () =
  {
    vartypes = Common.SMap.empty;
    equalities = ref (TEnv.create ()) ;
  }

(* concrete type environment, where every variable has a concrete type *)
type typ_env = typ Common.SMap.t

