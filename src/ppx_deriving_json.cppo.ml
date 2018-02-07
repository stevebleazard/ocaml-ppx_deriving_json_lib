#if OCAML_VERSION < (4, 03, 0)
#define Type_Nonrecursive
#define Pconst_string Const_string
#define Pcstr_tuple(x) x
#else
#define Type_Nonrecursive Nonrecursive
#endif

#if OCAML_VERSION >= (4, 06, 0)
#define Rtag(label, attrs, has_empty, args) \
        Rtag({ txt = label }, attrs, has_empty, args)
#endif


open Longident
open Location
open Asttypes
open Parsetree
open Ast_helper
open Ast_convenience

let raise_errorf = Ppx_deriving.raise_errorf

let argn = Printf.sprintf "arg%d"

let attr_int_encoding ~deriver attrs =
  match Ppx_deriving.attr ~deriver "encoding" attrs |>
        Ppx_deriving.Arg.(get_attr ~deriver (enum ["string"; "number"])) with
  | Some "string" -> `String
  | Some "number" | None -> `Int
  | _ -> assert false

let attr_int_encoding_as_string ~deriver attrs =
  match attr_int_encoding ~deriver attrs with
  | `String -> "String"
  | `Int    -> "Intlit"

let attr_string ~deriver name default attrs =
  match Ppx_deriving.attr ~deriver name attrs |>
        Ppx_deriving.Arg.(get_attr ~deriver string) with
  | Some x -> x
  | None   -> default

let attr_key  = attr_string "key"
let attr_name = attr_string "name"

let attr_default ~deriver attrs =
  Ppx_deriving.attr ~deriver "default" attrs |>
  Ppx_deriving.Arg.(get_attr ~deriver expr)

let parse_options ~deriver options =
  let strict = ref true in
  let fields = ref false in
  options |> List.iter (fun (name, expr) ->
    match name with
    | "strict" -> strict := Ppx_deriving.Arg.(get_expr ~deriver bool) expr
    | "fields" -> fields := Ppx_deriving.Arg.(get_expr ~deriver bool) expr
    | _ -> raise_errorf ~loc:expr.pexp_loc "%s does not support option %s" deriver name);
  (!strict, !fields)


module type Json_deriver = sig
  val name : string
  val suffix_to : string
  val suffix_of : string
  val value_type : core_type
  val is_value_type : core_type -> bool
  val runtime_module : string
  val fields_module : string
  val encode_float_function: attributes -> expression
  val encode_int_function : attributes -> expression
  val encode_int32_function : attributes -> expression
  val encode_int64_function : attributes -> expression
  val encode_nativeint_function : attributes -> expression
  val decode_float_function : attributes -> (pattern * expression) list
  val decode_int_function : attributes -> (pattern * expression) list
  val decode_int32_function : attributes -> (pattern * expression) list
  val decode_int64_function : attributes -> (pattern * expression) list
  val decode_nativeint_function : attributes -> (pattern * expression) list
end


module Register (Deriver : Json_deriver) : sig end = struct

let deriver = Deriver.name

let rec ser_expr_of_typ typ =
  let typ_attrs = typ.ptyp_attributes in
  match typ with
  | [%type: unit]            -> [%expr fun x -> `Null]
  | [%type: int]             -> Deriver.encode_int_function typ_attrs
  | [%type: float]           -> Deriver.encode_float_function typ_attrs
  | [%type: bool]            -> [%expr fun x -> `Bool x]
  | [%type: string]          -> [%expr fun x -> `String x]
  | [%type: bytes]           -> [%expr fun x -> `String (Bytes.to_string x)]
  | [%type: char]            -> [%expr fun x -> `String (String.make 1 x)]
  | [%type: [%t? typ] ref]   -> [%expr fun x -> [%e ser_expr_of_typ typ] !x]
  | [%type: [%t? typ] list]  -> [%expr fun x -> `List (List.map [%e ser_expr_of_typ typ] x)]
  | [%type: int32] | [%type: Int32.t] -> Deriver.encode_int32_function typ_attrs
  | [%type: int64] | [%type: Int64.t] -> Deriver.encode_int64_function typ_attrs
  | [%type: nativeint] | [%type: Nativeint.t] -> Deriver.encode_nativeint_function typ_attrs
  | [%type: [%t? typ] array] ->
    [%expr fun x -> `List (Array.to_list (Array.map [%e ser_expr_of_typ typ] x))]
  | [%type: [%t? typ] option] ->
    [%expr function None -> `Null | Some x -> [%e ser_expr_of_typ typ] x]
  | typ when Deriver.is_value_type typ -> [%expr fun x -> x]
  | { ptyp_desc = Ptyp_constr ({ txt = lid }, args) } ->
    let fwd = app (Exp.ident (mknoloc (Ppx_deriving.mangle_lid (`Suffix Deriver.suffix_to) lid)))
        (List.map ser_expr_of_typ args)
    in
    (* eta-expansion is necessary for let-rec *)
    [%expr fun x -> [%e fwd] x]

  | { ptyp_desc = Ptyp_tuple typs } ->
    [%expr fun [%p ptuple (List.mapi (fun i _ -> pvar (argn i)) typs)] ->
           `List ([%e
                      list (List.mapi (fun i typ -> app (ser_expr_of_typ typ) [evar (argn i)]) typs)])];
  | { ptyp_desc = Ptyp_variant (fields, _, _); ptyp_loc } ->
    let cases =
      fields |> List.map (fun field ->
        match field with
        | Rtag(label, attrs, true (*empty*), []) ->
          Exp.case (Pat.variant label None)
                   [%expr `List [`String [%e str (attr_name ~deriver label attrs)]]]
        | Rtag(label, attrs, false, [{ ptyp_desc = Ptyp_tuple typs }]) ->
          Exp.case (Pat.variant label (Some (ptuple (List.mapi (fun i _ -> pvar (argn i)) typs))))
                   [%expr `List ((`String [%e str (attr_name ~deriver label attrs)]) :: [%e
                      list (List.mapi
                        (fun i typ -> app (ser_expr_of_typ typ) [evar (argn i)]) typs)])]
        | Rtag(label, attrs, false, [typ]) ->
          Exp.case (Pat.variant label (Some [%pat? x]))
                   [%expr `List [`String [%e str (attr_name ~deriver label attrs)];
                                 [%e ser_expr_of_typ typ] x]]
        | Rinherit ({ ptyp_desc = Ptyp_constr (tname, _) } as typ) ->
          Exp.case [%pat? [%p Pat.type_ tname] as x]
                   [%expr [%e ser_expr_of_typ typ] x]
        | _ ->
          raise_errorf ~loc:ptyp_loc "%s cannot be derived for %s"
                       deriver (Ppx_deriving.string_of_core_type typ))
    in
    Exp.function_ cases
  | { ptyp_desc = Ptyp_var name } ->
    [%expr ([%e evar ("poly_"^name)] : _ -> [%t Deriver.value_type])]
  | { ptyp_desc = Ptyp_alias (typ, name) } ->
    [%expr fun x -> [%e evar ("poly_"^name)] x; [%e ser_expr_of_typ typ] x]
  | { ptyp_loc } ->
    raise_errorf ~loc:ptyp_loc "%s cannot be derived for %s"
                 deriver (Ppx_deriving.string_of_core_type typ)

(* http://desuchan.net/desu/src/1284751839295.jpg *)
let rec desu_fold ~path f typs =
  typs |>
  List.mapi (fun i typ -> i, app (desu_expr_of_typ ~path typ) [evar (argn i)]) |>
  List.fold_left (fun x (i, y) ->
    [%expr [%e y] >>= fun [%p pvar (argn i)] -> [%e x]])
    [%expr Result.Ok [%e f (List.mapi (fun i _ -> evar (argn i)) typs)]]
and desu_expr_of_typ ~path typ =
  let error = [%expr Result.Error [%e str (String.concat "." path)]] in
  let decode' cases =
    Exp.function_ (
      List.map (fun (pat, exp) -> Exp.case pat exp) cases @
      [Exp.case [%pat? _] error])
  in
  let decode pat exp = decode' [pat, exp] in
  let typ_attrs = typ.ptyp_attributes in
  match typ with
  | [%type: unit]   -> decode [%pat? `Null] [%expr Result.Ok ()]
  | [%type: int]    -> decode' (Deriver.decode_int_function typ_attrs)
  | [%type: float]  -> decode' (Deriver.decode_float_function typ_attrs)
  | [%type: bool]   -> decode [%pat? `Bool x]   [%expr Result.Ok x]
  | [%type: string] -> decode [%pat? `String x] [%expr Result.Ok x]
  | [%type: bytes]  -> decode [%pat? `String x] [%expr Result.Ok (Bytes.of_string x)]
  | [%type: char]   ->
    decode [%pat? `String x] [%expr if String.length x = 1 then Result.Ok x.[0] else [%e error]]
  | [%type: int32] | [%type: Int32.t] -> decode' (Deriver.decode_int32_function typ_attrs)
  | [%type: int64] | [%type: Int64.t] -> decode' (Deriver.decode_int64_function typ_attrs)
  | [%type: nativeint] | [%type: Nativeint.t] -> decode' (Deriver.decode_nativeint_function typ_attrs)
  | [%type: [%t? typ] ref]   ->
    [%expr fun x -> [%e desu_expr_of_typ ~path:(path @ ["contents"]) typ] x >|= ref]
  | [%type: [%t? typ] option] ->
    [%expr function
           | `Null -> Result.Ok None
           | x     -> [%e desu_expr_of_typ ~path typ] x >>= fun x -> Result.Ok (Some x)]
  | [%type: [%t? typ] list]  ->
    decode [%pat? `List xs]
           [%expr map_bind [%e desu_expr_of_typ ~path typ] [] xs]
  | [%type: [%t? typ] array] ->
    decode [%pat? `List xs]
      [%expr map_bind [%e desu_expr_of_typ ~path typ] [] xs >|= Array.of_list]
  | typ when Deriver.is_value_type typ -> [%expr fun x -> Result.Ok x]
  | { ptyp_desc = Ptyp_tuple typs } ->
    decode [%pat? `List [%p plist (List.mapi (fun i _ -> pvar (argn i)) typs)]]
           (desu_fold ~path tuple typs)
  | { ptyp_desc = Ptyp_variant (fields, _, _); ptyp_loc } ->
    let inherits, tags = List.partition (function Rinherit _ -> true | _ -> false) fields in
    let tag_cases = tags |> List.map (fun field ->
      match field with
      | Rtag(label, attrs, true (*empty*), []) ->
        Exp.case [%pat? `List [`String [%p pstr (attr_name ~deriver label attrs)]]]
                 [%expr Result.Ok [%e Exp.variant label None]]
      | Rtag(label, attrs, false, [{ ptyp_desc = Ptyp_tuple typs }]) ->
        Exp.case [%pat? `List ((`String [%p pstr (attr_name ~deriver label attrs)]) :: [%p
                    plist (List.mapi (fun i _ -> pvar (argn i)) typs)])]
                 (desu_fold ~path (fun x -> (Exp.variant label (Some (tuple x)))) typs)
      | Rtag(label, attrs, false, [typ]) ->
        Exp.case [%pat? `List [`String [%p pstr (attr_name ~deriver label attrs)]; x]]
                 [%expr [%e desu_expr_of_typ ~path typ] x >>= fun x ->
                        Result.Ok [%e Exp.variant label (Some [%expr x])]]
      | Rinherit ({ ptyp_desc = Ptyp_constr (tname, _) } as typ) ->
        Exp.case [%pat? [%p Pat.type_ tname] as x]
                 [%expr [%e desu_expr_of_typ ~path typ] x]
      | _ ->
        raise_errorf ~loc:ptyp_loc "%s cannot be derived for %s"
                     deriver (Ppx_deriving.string_of_core_type typ))
    and inherits_case =
      let toplevel_typ = typ in
      inherits
      |> List.map (function Rinherit typ -> typ | _ -> assert false)
      |> List.fold_left (fun expr typ -> [%expr
        match [%e desu_expr_of_typ ~path typ] json with
        | (Result.Ok result) -> Result.Ok (result :> [%t toplevel_typ])
        | Result.Error _ -> [%e expr]]) error
      |> Exp.case [%pat? _]
    in
    [%expr fun (json : [%t Deriver.value_type]) ->
      [%e Exp.match_ [%expr json] (tag_cases @ [inherits_case])]]
  | { ptyp_desc = Ptyp_constr ({ txt = lid }, args) } ->
     let fwd = app (Exp.ident (mknoloc (Ppx_deriving.mangle_lid (`Suffix Deriver.suffix_of) lid)))
             (List.map (desu_expr_of_typ ~path) args) in
     (* eta-expansion is necessary for recursive groups *)
     [%expr fun x -> [%e fwd] x]
  | { ptyp_desc = Ptyp_var name } ->
    [%expr ([%e evar ("poly_"^name)] : [%t Deriver.value_type] -> _ error_or)]
  | { ptyp_desc = Ptyp_alias (typ, name) } ->
    [%expr fun x -> [%e evar ("poly_"^name)] x; [%e desu_expr_of_typ ~path typ] x]
  | { ptyp_loc } ->
    raise_errorf ~loc:ptyp_loc "%s cannot be derived for %s"
                 deriver (Ppx_deriving.string_of_core_type typ)

let wrap_runtime decls =
  Ppx_deriving.sanitize ~module_:(Lident Deriver.runtime_module) decls

let ser_type_of_decl ~options ~path type_decl =
  ignore (parse_options ~deriver options);
  let typ = Ppx_deriving.core_type_of_type_decl type_decl in
  let polymorphize = Ppx_deriving.poly_arrow_of_type_decl
                       (fun var -> [%type: [%t var] -> [%t Deriver.value_type]]) type_decl in
  polymorphize [%type: [%t typ] -> [%t Deriver.value_type]]

let ser_str_of_record varname labels =
  let fields =
    labels |> List.mapi (fun i { pld_name = { txt = name }; pld_type; pld_attributes } ->
      let field  = Exp.field (evar varname) (mknoloc (Lident name)) in
      let result = [%expr [%e str (attr_key ~deriver name pld_attributes)],
                    [%e ser_expr_of_typ pld_type] [%e field]] in
      match attr_default ~deriver (pld_type.ptyp_attributes @ pld_attributes) with
      | None ->
          [%expr [%e result] :: fields]
      | Some default ->
          [%expr if [%e field] = [%e default] then fields else [%e result] :: fields])
  in
  let assoc =
    List.fold_left
      (fun expr field -> [%expr let fields = [%e field] in [%e expr]])
      [%expr `Assoc fields] fields
  in
  [%expr let fields = [] in [%e assoc]]


let ser_str_of_type ~options ~path ({ ptype_loc = loc } as type_decl) =
  ignore (parse_options ~deriver options);
  let polymorphize = Ppx_deriving.poly_fun_of_type_decl type_decl in
  let typ = Ppx_deriving.core_type_of_type_decl type_decl in
  match type_decl.ptype_kind with
  | Ptype_open -> begin
    let to_json_name = Ppx_deriving.mangle_type_decl (`Suffix Deriver.suffix_to) type_decl in
    let mod_name = Ppx_deriving.mangle_type_decl
      (`PrefixSuffix ("M", Deriver.suffix_to)) type_decl
    in
    match type_decl.ptype_manifest with
    | Some ({ ptyp_desc = Ptyp_constr ({ txt = lid }, args) } as manifest) ->
      let ser = ser_expr_of_typ manifest in
      let lid = Ppx_deriving.mangle_lid (`PrefixSuffix ("M", Deriver.suffix_to)) lid in
      let orig_mod = Mod.ident (mknoloc lid) in
      ([Str.module_ (Mb.mk (mknoloc mod_name) orig_mod)],
       [Vb.mk (pvar to_json_name)
              (polymorphize [%expr ([%e ser] : [%t typ] -> [%t Deriver.value_type])])],
       [])
    | Some _ ->
      raise_errorf ~loc "%s: extensible type manifest should be a type name" deriver
    | None ->
      let poly_vars = List.rev
          (Ppx_deriving.fold_left_type_decl (fun acc name -> name :: acc) [] type_decl)
      in
      let polymorphize_ser  = Ppx_deriving.poly_arrow_of_type_decl
        (fun var -> [%type: [%t var] -> [%t Deriver.value_type]]) type_decl
      in
      let ty = Typ.poly (List.map Location.mknoloc poly_vars) (polymorphize_ser [%type: [%t typ] -> [%t Deriver.value_type]]) in
      let default_fun =
        let type_path = String.concat "." (path @ [type_decl.ptype_name.txt]) in
        let message =
          Printf.sprintf "%s: Maybe a [@@deriving %s] is missing when extending the type %s"
            Deriver.suffix_to
            deriver
            type_path
        in
        let e_message = Exp.constant (Pconst_string (message, None)) in
        [%expr fun _ ->
          invalid_arg [%e e_message]]
      in
      let poly_fun = polymorphize default_fun in
      let poly_fun =
        (Ppx_deriving.fold_left_type_decl (fun exp name -> Exp.newtype (Location.mknoloc name) exp) poly_fun type_decl)
      in
      let mod_name = "M_"^to_json_name in
      let typ = Type.mk ~kind:(Ptype_record [Type.field ~mut:Mutable (mknoloc "f") ty])
                              (mknoloc ("t_" ^ Deriver.suffix_to))
      in
      let record = Vb.mk (pvar "f") (Exp.record [lid "f", poly_fun] None) in
      let flid = lid (Printf.sprintf "%s.f" mod_name) in
      let field = Exp.field (Exp.ident flid) (flid) in
      let mod_ =
        Str.module_ (Mb.mk (mknoloc mod_name)
                    (Mod.structure [
          Str.type_ Type_Nonrecursive [typ];
          Str.value Nonrecursive [record];
        ]))
      in
      ([mod_],
       [Vb.mk (pvar to_json_name) [%expr fun x -> [%e field] x]],
       [])
  end
  | kind ->
    let serializer =
      match kind, type_decl.ptype_manifest with
      | Ptype_open, _ -> assert false
      | Ptype_abstract, Some manifest -> ser_expr_of_typ manifest
      | Ptype_variant constrs, _ ->
        constrs
        |> List.map (fun { pcd_name = { txt = name' }; pcd_args; pcd_attributes } ->
          let json_name = attr_name ~deriver name' pcd_attributes in
          match pcd_args with
          | Pcstr_tuple([]) ->
            Exp.case
              (pconstr name' [])
              [%expr `List [`String [%e str json_name]]]
          | Pcstr_tuple(args) ->
            let arg_exprs =
              List.mapi (fun i typ -> app (ser_expr_of_typ typ) [evar (argn i)]) args
            in
            Exp.case
              (pconstr name' (List.mapi (fun i _ -> pvar (argn i)) args))
              [%expr `List ((`String [%e str json_name]) :: [%e list arg_exprs])]
#if OCAML_VERSION >= (4, 03, 0)
          | Pcstr_record labels ->
            let arg_expr = ser_str_of_record (argn 0) labels in
            Exp.case
              (pconstr name' [pvar(argn 0)])
              [%expr `List ((`String [%e str json_name]) :: [%e list[arg_expr]])]
#endif
          )
        |> Exp.function_
      | Ptype_record labels, _ ->
        [%expr fun x -> [%e ser_str_of_record "x" labels]]
      | Ptype_abstract, None ->
        raise_errorf ~loc "%s cannot be derived for fully abstract types" deriver
    in
    let ty = ser_type_of_decl ~options ~path type_decl in
    let fv = Ppx_deriving.free_vars_in_core_type ty in
    let poly_type = Typ.force_poly @@ Typ.poly (List.map Location.mknoloc fv) @@ ty in
    let var_s = Ppx_deriving.mangle_type_decl (`Suffix Deriver.suffix_to) type_decl in
    let var = pvar var_s in
    (* CR-someday xclerc: once available, it would be better to disable warnings on the
       bindings rather than globally (i.e. let[@warning "..."] x = ...), and use the
       same mechanism in order to get rid of the `let _ = ...` trick.
       This applies to all occurrences below. *)
    ([],
     [Vb.mk ~attrs:[mkloc "ocaml.warning" !Ast_helper.default_loc, PStr [%str "-39"]]
        (Pat.constraint_ var poly_type)
        (polymorphize [%expr ([%e wrap_runtime serializer])])],
     [Str.value Nonrecursive [Vb.mk [%expr [%e pvar "_"]] [%expr [%e evar var_s]]] ]
     )

let ser_str_of_type_ext ~options ~path ({ ptyext_path = { loc }} as type_ext) =
  ignore (parse_options ~deriver options);
  let serializer =
    let pats =
      List.fold_right (fun { pext_name = { txt = name' }; pext_kind; pext_attributes } acc_cases ->
        match pext_kind with
        | Pext_rebind _ ->
          (* nothing to do, since the constructor must be handled in original
             constructor declaration *)
          acc_cases
        | Pext_decl (pext_args, _) ->
          let json_name = attr_name ~deriver name' pext_attributes in
          let case =
            match pext_args with
            | Pcstr_tuple([]) ->
              Exp.case
                (pconstr name' [])
                [%expr `List [`String [%e str json_name]]]
            | Pcstr_tuple(args) ->
              let arg_exprs =
                List.mapi (fun i typ -> app (ser_expr_of_typ typ) [evar (argn i)]) args
              in
              Exp.case
                (pconstr name' (List.mapi (fun i _ -> pvar (argn i)) args))
                [%expr `List ((`String [%e str json_name]) :: [%e list arg_exprs])]
#if OCAML_VERSION >= (4, 03, 0)
            | Pcstr_record _ ->
              raise_errorf ~loc "%s: record variants are not supported in extensible types" deriver
#endif
          in
          case :: acc_cases) type_ext.ptyext_constructors []
    in
    let fallback_case =
      Exp.case [%pat? x]
               [%expr [%e Ppx_deriving.poly_apply_of_type_ext type_ext [%expr fallback]] x]
    in
    Exp.function_ (pats @ [fallback_case])
  in
  let mod_name =
    let mod_lid =
      Ppx_deriving.mangle_lid
        (`PrefixSuffix ("M", Deriver.suffix_to)) type_ext.ptyext_path.txt
    in
    String.concat "." (Longident.flatten mod_lid)
  in
  let polymorphize = Ppx_deriving.poly_fun_of_type_ext type_ext in
  let serializer = polymorphize (wrap_runtime serializer) in
  let flid = lid (Printf.sprintf "%s.f" mod_name) in
  let set_field = Exp.setfield (Exp.ident flid) flid serializer in
  let field = Exp.field (Exp.ident flid) (flid) in
  let body = [%expr let fallback = [%e field] in [%e set_field]] in
  [Str.value ?loc:None Nonrecursive [Vb.mk (Pat.construct (lid "()") None) body]]

let error_or typ =
  Ast_helper.Typ.constr
    (mknoloc (Ldot (Lident Deriver.runtime_module, "error_or")))
    [typ]

let desu_type_of_decl_poly ~options ~path type_decl type_ =
  ignore (parse_options ~deriver options);
  let polymorphize = Ppx_deriving.poly_arrow_of_type_decl
                       (fun var -> [%type: [%t Deriver.value_type] -> [%t error_or var]]) type_decl in
  polymorphize type_

let desu_type_of_decl ~options ~path type_decl =
  let typ = Ppx_deriving.core_type_of_type_decl type_decl in
  desu_type_of_decl_poly ~options ~path type_decl [%type: [%t Deriver.value_type] -> [%t error_or typ]]


let desu_str_of_record ~is_strict ~error ~path wrap_record labels =
  let top_error = error path in
  let record =
    List.fold_left
      (fun expr i ->
        [%expr [%e evar (argn i)] >>= fun [%p pvar (argn i)] -> [%e expr]]
      )
      ( let r =
          Exp.record (labels |>
            List.mapi (fun i { pld_name = { txt = name } } ->
              mknoloc (Lident name), evar (argn i)))
            None in
        [%expr Result.Ok [%e wrap_record r] ] )
      (labels |> List.mapi (fun i _ -> i)) in
  let default_case = if is_strict then top_error else [%expr loop xs _state] in
  let cases =
    (labels |> List.mapi (fun i { pld_name = { txt = name }; pld_type; pld_attributes } ->
        let path = path @ [name] in
        let thunks = labels |> List.mapi (fun j _ ->
             if i = j then app (desu_expr_of_typ ~path pld_type) [evar "x"] else evar (argn j)) in
        Exp.case [%pat? ([%p pstr (attr_key ~deriver name pld_attributes)], x) :: xs]
          [%expr loop xs [%e tuple thunks]])) @
    [Exp.case [%pat? []] record;
     Exp.case [%pat? _ :: xs] default_case]
  and thunks =
    labels |> List.map (fun { pld_name = { txt = name }; pld_type; pld_attributes } ->
      match attr_default ~deriver (pld_type.ptyp_attributes @ pld_attributes) with
      | None   -> error (path @ [name])
      | Some x -> [%expr Result.Ok [%e x]])
  in
  [%expr
    function
    | `Assoc xs ->
      let rec loop xs ([%p ptuple (List.mapi (fun i _ -> pvar (argn i)) labels)] as _state) =
        [%e Exp.match_ [%expr xs] cases]
      in loop xs [%e tuple thunks]
    | _ -> [%e top_error]]


let desu_str_of_type ~options ~path ({ ptype_loc = loc } as type_decl) =
  let (is_strict, _) = parse_options ~deriver options in
  let path = path @ [type_decl.ptype_name.txt] in
  let error path = [%expr Result.Error [%e str (String.concat "." path)]] in
  let top_error = error path in
  let polymorphize = Ppx_deriving.poly_fun_of_type_decl type_decl in
  let typ = Ppx_deriving.core_type_of_type_decl type_decl in
  match type_decl.ptype_kind with
  | Ptype_open -> begin
    let of_json_name = Ppx_deriving.mangle_type_decl (`Suffix Deriver.suffix_of) type_decl in
    let mod_name = Ppx_deriving.mangle_type_decl
      (`PrefixSuffix ("M", Deriver.suffix_of)) type_decl
    in
    match type_decl.ptype_manifest with
    | Some ({ ptyp_desc = Ptyp_constr ({ txt = lid }, args) } as manifest) ->
      let desu = desu_expr_of_typ ~path manifest in
      let lid = Ppx_deriving.mangle_lid (`PrefixSuffix ("M", Deriver.suffix_of)) lid in
      let orig_mod = Mod.ident (mknoloc lid) in
      let poly_desu = polymorphize [%expr ([%e wrap_runtime desu] : [%t Deriver.value_type] -> _)] in
      ([Str.module_ (Mb.mk (mknoloc mod_name) orig_mod)],
       [Vb.mk (pvar of_json_name) poly_desu],
       [])
    | Some _ ->
      raise_errorf ~loc "%s: extensible type manifest should be a type name" deriver
    | None ->
      let poly_vars = List.rev
        (Ppx_deriving.fold_left_type_decl (fun acc name -> name :: acc) [] type_decl)
      in
      let polymorphize_desu = Ppx_deriving.poly_arrow_of_type_decl
        (fun var -> [%type: [%t Deriver.value_type] -> [%t error_or var]]) type_decl in
      let ty = Typ.poly (List.map Location.mknoloc poly_vars)
        (polymorphize_desu [%type: [%t Deriver.value_type] -> [%t error_or typ]])
      in
      let default_fun = Exp.function_ [Exp.case [%pat? _] top_error] in
      let poly_fun = polymorphize default_fun in
      let poly_fun =
        (Ppx_deriving.fold_left_type_decl (fun exp name -> Exp.newtype (Location.mknoloc name) exp) poly_fun type_decl)
      in
      let mod_name = "M_"^Deriver.suffix_of in
      let typ = Type.mk ~kind:(Ptype_record [Type.field ~mut:Mutable (mknoloc "f") ty])
                        (mknoloc ("t" ^ Deriver.suffix_of)) in
      let record = Vb.mk (pvar "f") (Exp.record [lid "f", poly_fun] None) in
      let flid = lid (Printf.sprintf "%s.f" mod_name) in
      let field = Exp.field (Exp.ident flid) flid in
      let mod_ =
        Str.module_ (Mb.mk (mknoloc mod_name)
                    (Mod.structure [
          Str.type_ Type_Nonrecursive [typ];
          Str.value Nonrecursive [record];
        ]))
      in
      ([mod_],
       [Vb.mk (pvar of_json_name) [%expr fun x -> [%e field] x]],
       [])
  end
  | kind ->
    let desurializer =
      match kind, type_decl.ptype_manifest with
      | Ptype_open, _ -> assert false
      | Ptype_abstract, Some manifest ->
        desu_expr_of_typ ~path manifest
      | Ptype_variant constrs, _ ->
        let cases = List.map (fun { pcd_name = { txt = name' }; pcd_args; pcd_attributes } ->
          match pcd_args with
          | Pcstr_tuple(args) ->
            Exp.case
              [%pat? `List ((`String [%p pstr (attr_name ~deriver name' pcd_attributes)]) ::
                                     [%p plist (List.mapi (fun i _ -> pvar (argn i)) args)])]
              (desu_fold ~path (fun x -> constr name' x) args)
#if OCAML_VERSION >= (4, 03, 0)
          | Pcstr_record labels ->
            let wrap_record r = constr name' [r] in
            let sub =
              desu_str_of_record ~is_strict ~error ~path wrap_record labels in
            Exp.case
              [%pat? `List ((`String [%p pstr (attr_name ~deriver name' pcd_attributes)]) ::
                              [%p plist [pvar (argn 0)]])]
              [%expr [%e sub] [%e evar (argn 0)] ]
#endif
          ) constrs
        in
        Exp.function_ (cases @ [Exp.case [%pat? _] top_error])
      | Ptype_record labels, _ ->
        desu_str_of_record ~is_strict ~error ~path (fun r -> r) labels
      | Ptype_abstract, None ->
        raise_errorf ~loc "%s cannot be derived for fully abstract types" deriver
    in
    let ty = desu_type_of_decl ~options ~path type_decl in
    let fv = Ppx_deriving.free_vars_in_core_type ty in
    let poly_type = Typ.force_poly @@ Typ.poly (List.map Location.mknoloc fv) @@ ty in
    let var_s = Ppx_deriving.mangle_type_decl (`Suffix Deriver.suffix_of) type_decl in
    let var = pvar var_s in
    let var_s_exn = var_s ^ "_exn" in
    let { ptype_params; _ } = type_decl in
    let var_s_exn_args = List.mapi (fun i _ -> argn i |> evar) ptype_params in
    let var_s_exn_args = var_s_exn_args @ [evar "x"] in
    let var_s_exn_fun =
      let rec loop = function
      | [] -> wrap_runtime ([%expr match  [%e app (evar var_s) var_s_exn_args] with Result.Ok x -> x | Result.Error err -> raise (Failure err)])
      | hd::tl -> lam (pvar hd) (loop tl)
      in
      loop ((List.mapi (fun i _ -> argn i) ptype_params) @ ["x"])
    in
    ([],
     [Vb.mk ~attrs:[mkloc "ocaml.warning" !Ast_helper.default_loc, PStr [%str "-39"]]
            (Pat.constraint_ var poly_type)
            (polymorphize [%expr ([%e wrap_runtime desurializer])]) ],
     [Str.value Nonrecursive [Vb.mk [%expr [%e pvar "_"]] [%expr [%e evar var_s]]]
     ;Str.value Nonrecursive [Vb.mk [%expr [%e pvar var_s_exn]] var_s_exn_fun]
     ;Str.value Nonrecursive [Vb.mk [%expr [%e pvar "_"]] [%expr [%e evar var_s_exn]]]
     ])

let desu_str_of_type_ext ~options ~path ({ ptyext_path = { loc } } as type_ext) =
  ignore(parse_options ~deriver options);
  let desurializer =
    let pats =
      List.fold_right (fun { pext_name = { txt = name' }; pext_kind; pext_attributes } acc_cases ->
        match pext_kind with
        | Pext_rebind _ ->
          (* nothing to do since it must have been handled in the original
             constructor declaration *)
          acc_cases
        | Pext_decl (pext_args, _) ->
          let case =
            match pext_args with
            | Pcstr_tuple(args) ->
              Exp.case
                [%pat? `List ((`String [%p pstr (attr_name ~deriver name' pext_attributes)]) ::
                                       [%p plist (List.mapi (fun i _ -> pvar (argn i)) args)])]
                (desu_fold ~path (fun x -> constr name' x) args)
#if OCAML_VERSION >= (4, 03, 0)
            | Pcstr_record _ ->
              raise_errorf ~loc "%s: record variants are not supported in extensible types" deriver
#endif
          in
          case :: acc_cases)
        type_ext.ptyext_constructors []
    in
    let any_case = Exp.case (Pat.var (mknoloc "x"))
      (app (Ppx_deriving.poly_apply_of_type_ext type_ext [%expr fallback])
       [[%expr x]])
    in
    (pats @ [any_case]) |> Exp.function_
  in
  let mod_name =
    let mod_lid =
      Ppx_deriving.mangle_lid
        (`PrefixSuffix ("M", Deriver.suffix_of)) type_ext.ptyext_path.txt
    in
    String.concat "." (Longident.flatten mod_lid)
  in
  let polymorphize = Ppx_deriving.poly_fun_of_type_ext type_ext in
  let desurializer = wrap_runtime (polymorphize desurializer) in
  let flid = lid (Printf.sprintf "%s.f" mod_name) in
  let set_field = Exp.setfield (Exp.ident flid) flid desurializer in
  let field = Exp.field (Exp.ident flid) flid in
  let body = [%expr let fallback = [%e field] in [%e set_field]] in
  [Str.value ?loc:None Nonrecursive [Vb.mk (Pat.construct (lid "()") None) body]]

let ser_sig_of_type ~options ~path type_decl =
  let to_json =
    Sig.value (Val.mk (mknoloc (Ppx_deriving.mangle_type_decl (`Suffix Deriver.suffix_to) type_decl))
                      (ser_type_of_decl ~options ~path type_decl))
  in
  match type_decl.ptype_kind with
  | Ptype_open ->
    let mod_name = Ppx_deriving.mangle_type_decl
      (`PrefixSuffix ("M", Deriver.suffix_to)) type_decl
    in
    let poly_vars = List.rev
      (Ppx_deriving.fold_left_type_decl (fun acc name -> name :: acc) [] type_decl)
    in
    let typ = Ppx_deriving.core_type_of_type_decl type_decl in
    let polymorphize_ser  = Ppx_deriving.poly_arrow_of_type_decl
      (fun var -> [%type: [%t var] -> [%t Deriver.value_type]]) type_decl
    in
    let ty = Typ.poly (List.map Location.mknoloc poly_vars) (polymorphize_ser [%type: [%t typ] -> [%t Deriver.value_type]]) in
    let typ = Type.mk ~kind:(Ptype_record
       [Type.field ~mut:Mutable (mknoloc "f") ty]) (mknoloc ("t" ^ Deriver.suffix_to))
    in
    let record = Val.mk (mknoloc "f") (Typ.constr (lid ("t" ^ Deriver.suffix_to)) []) in
    let mod_ =
      Sig.module_ (Md.mk (mknoloc mod_name)
                  (Mty.signature [
        Sig.type_ Type_Nonrecursive [typ];
        Sig.value record;
      ]))
    in
    [mod_; to_json]
  | _ -> [to_json]


let ser_sig_of_type_ext ~options ~path type_ext = []

let desu_sig_of_type ~options ~path type_decl =
  let of_json =
    Sig.value (Val.mk (mknoloc (Ppx_deriving.mangle_type_decl (`Suffix Deriver.suffix_of) type_decl))
                      (desu_type_of_decl ~options ~path type_decl))
  in
  let typ = Ppx_deriving.core_type_of_type_decl type_decl in
  let of_json_exn =
    Sig.value (Val.mk (mknoloc (Ppx_deriving.mangle_type_decl (`Suffix (Deriver.suffix_of ^ "_exn")) type_decl))
                      (desu_type_of_decl_poly ~options ~path type_decl [%type: [%t Deriver.value_type] -> [%t typ]]))
  in
  match type_decl.ptype_kind with
  | Ptype_open ->
    let mod_name = Ppx_deriving.mangle_type_decl
      (`PrefixSuffix ("M", Deriver.suffix_of)) type_decl
    in
    let poly_vars = List.rev
      (Ppx_deriving.fold_left_type_decl (fun acc name -> name :: acc) [] type_decl)
    in
    let typ = Ppx_deriving.core_type_of_type_decl type_decl in
    let polymorphize_desu = Ppx_deriving.poly_arrow_of_type_decl
      (fun var -> [%type: [%t Deriver.value_type] -> [%t error_or var]]) type_decl in
    let ty = Typ.poly (List.map Location.mknoloc poly_vars)
      (polymorphize_desu [%type: [%t Deriver.value_type] -> [%t error_or typ]])
    in
    let typ = Type.mk ~kind:(Ptype_record
       [Type.field ~mut:Mutable (mknoloc "f") ty]) (mknoloc ("t" ^ Deriver.suffix_of))
    in
    let record = Val.mk (mknoloc "f") (Typ.constr (lid ("t" ^ Deriver.suffix_of)) []) in
    let mod_ =
      Sig.module_ (Md.mk (mknoloc mod_name)
                  (Mty.signature [
        Sig.type_ Type_Nonrecursive [typ];
        Sig.value record;
      ]))
    in
    [mod_; of_json]
  | _ -> [of_json; of_json_exn]

let desu_sig_of_type_ext ~options ~path type_ext = []

let json_str_fields ~options ~path ({ ptype_loc = loc } as type_decl) =
  let (_, want_fields) =  parse_options ~deriver options in
  match want_fields, type_decl.ptype_kind with
  | false, _ | true, Ptype_open -> []
  | true, kind ->
    match kind, type_decl.ptype_manifest with
    | Ptype_record labels, _ ->
      let fields =
        labels |> List.map (fun { pld_name = { txt = name }; pld_type; pld_attributes } ->
          [%expr [%e str (attr_key ~deriver name pld_attributes)]])
      in
      let flist = List.fold_right (fun n acc -> [%expr [%e n] :: [%e  acc]])
        fields [%expr []]
      in
        [
          Str.module_ (Mb.mk (mknoloc (Ppx_deriving.mangle_type_decl (`Prefix Deriver.fields_module) type_decl))
                      (Mod.structure [
            Str.value Nonrecursive [Vb.mk [%expr [%e pvar "keys"]] [%expr [%e flist]]]
          ; Str.value Nonrecursive [Vb.mk [%expr [%e pvar "_"]] [%expr [%e evar "keys"]]]
          ]))
        ]
    | _ -> []

let json_sig_fields ~options ~path ({ ptype_loc = loc } as type_decl) =
  let (_, want_fields) =  parse_options ~deriver options in
  match want_fields, type_decl.ptype_kind with
  | false, _ | true, Ptype_open -> []
  | true, kind ->
    match kind, type_decl.ptype_manifest with
    | Ptype_record _, _ ->
      [
        Sig.module_ (Md.mk (mknoloc (Ppx_deriving.mangle_type_decl (`Prefix Deriver.fields_module) type_decl))
                    (Mty.signature [
          Sig.value (Val.mk (mknoloc "keys") [%type: string list]) ]))
      ]
    | _ -> []

let str_of_type ~options ~path type_decl =
  let (ser_pre, ser_vals, ser_post) = ser_str_of_type ~options ~path type_decl in
  let (desu_pre, desu_vals, desu_post) = desu_str_of_type ~options ~path type_decl in
  let fields_post = json_str_fields ~options ~path type_decl in
  (ser_pre @ desu_pre, ser_vals @ desu_vals, ser_post @ desu_post @ fields_post)

let str_of_type_to_json ~options ~path type_decl =
  let (ser_pre, ser_vals, ser_post) = ser_str_of_type ~options ~path type_decl in
  let fields_post = json_str_fields ~options ~path type_decl in
  (ser_pre, ser_vals, ser_post @ fields_post)

let str_of_type_of_json ~options ~path type_decl =
  let (desu_pre, desu_vals, desu_post) = desu_str_of_type ~options ~path type_decl in
  let fields_post = json_str_fields ~options ~path type_decl in
  (desu_pre, desu_vals, desu_post @ fields_post)

let str_of_type_ext ~options ~path type_ext =
  let ser_vals = ser_str_of_type_ext ~options ~path type_ext in
  let desu_vals = desu_str_of_type_ext ~options ~path type_ext in
  ser_vals @ desu_vals

let sig_of_type ~options ~path type_decl =
  (ser_sig_of_type ~options ~path type_decl) @
  (desu_sig_of_type ~options ~path type_decl) @
  (json_sig_fields ~options ~path type_decl)

let sig_of_type_to_json ~options ~path type_decl =
  (ser_sig_of_type ~options ~path type_decl) @
  (json_sig_fields ~options ~path type_decl)

let sig_of_type_of_json ~options ~path type_decl =
  (desu_sig_of_type ~options ~path type_decl) @
  (json_sig_fields ~options ~path type_decl)

let sig_of_type_ext ~options ~path type_ext =
  (ser_sig_of_type_ext ~options ~path type_ext) @
  (desu_sig_of_type_ext ~options ~path type_ext)

let structure f ~options ~path type_ =
  let (pre, vals, post) = f ~options ~path type_ in
  match vals with
  | [] -> pre @ post
  | _  -> pre @ [Str.value ?loc:None Recursive vals] @ post

let on_str_decls f ~options ~path type_decls =
  let unzip3 l =
    List.fold_right (fun (v1, v2, v3) (a1,a2,a3) -> (v1::a1, v2::a2, v3::a3)) l ([],[],[])
  in
  let (pre, vals, post) = unzip3 (List.map (f ~options ~path) type_decls) in
  (List.concat pre, List.concat vals, List.concat post)

let on_sig_decls f ~options ~path type_decls =
  List.concat (List.map (f ~options ~path) type_decls)

let () =
  Ppx_deriving.(register
   (create deriver
    ~type_decl_str:(structure (on_str_decls str_of_type))
    ~type_ext_str:str_of_type_ext
    ~type_decl_sig:(on_sig_decls sig_of_type)
    ~type_ext_sig:sig_of_type_ext
    ()
   ));
  Ppx_deriving.(register
   (create Deriver.suffix_to
    ~core_type:ser_expr_of_typ
    ~type_decl_str:(structure (on_str_decls str_of_type_to_json))
    ~type_ext_str:ser_str_of_type_ext
    ~type_decl_sig:(on_sig_decls sig_of_type_to_json)
    ~type_ext_sig:ser_sig_of_type_ext
    ()
  ));
  Ppx_deriving.(register
   (create Deriver.suffix_of
    ~core_type:(fun typ -> wrap_runtime (desu_expr_of_typ ~path:[] typ))
    ~type_decl_str:(structure (on_str_decls str_of_type_of_json))
    ~type_ext_str:desu_str_of_type_ext
    ~type_decl_sig:(on_sig_decls sig_of_type_of_json)
    ~type_ext_sig:desu_sig_of_type_ext
    ()
  ))

end

