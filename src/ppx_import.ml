open Longident
open Asttypes
open Parsetree
open Ast_mapper
open Ast_helper
open Types
open Ident

let raise_errorf ?sub ?if_highlight ?loc message =
  message |> Printf.kprintf (fun str ->
    let err = Location.error ?sub ?if_highlight ?loc str in
    raise (Location.Error err))

let replace_loc loc =
  { default_mapper with location = fun _ _ -> loc }

let locate_sig ~loc lid =
  let cu, path =
    match lid with
    | Lident _ -> !Location.input_name, []
    | Lapply _ -> assert false
    | Ldot (lid, _) ->
      match Longident.flatten lid with
      | cu :: path -> cu, path
      | _ -> assert false
  in
  let cmi_paths =
    !Config.load_path |>
    List.map (fun dir ->
      [Filename.concat dir (cu ^ ".cmi");
       Filename.concat dir ((String.uncapitalize_ascii cu) ^ ".cmi")]) |>
    List.flatten
  in
  let cmi =
    try
      cmi_paths |>
      List.find (fun intf ->
        Sys.file_exists intf) |>
      Cmi_format.read_cmi
    with Not_found ->
      raise_errorf ~loc "[%%import]: cannot locate module %s" cu
  in
  List.fold_left (fun sig_items path_item ->
      let rec loop sig_items =
        match sig_items with
        | Sig_module ({ name }, { md_type = Mty_signature sig_items }, _) :: _
              when name = path_item ->
          sig_items
        | Sig_modtype ({ name }, { mtd_type = Some (Mty_signature sig_items) }) :: _
              when name = path_item ->
          sig_items
        | _ :: sig_items ->
          loop sig_items
        | [] ->
          raise_errorf ~loc "[%%import]: cannot locate module %s"
                            (String.concat "." (cu :: path))
      in
      loop sig_items)
    cmi.Cmi_format.cmi_sign path

let locate_tsig_item f ~loc sig_items lid =
  let elem = Longident.last lid in
  let rec loop sig_items =
    match sig_items with
    | item :: sig_items ->
      (match f elem item with Some x -> x | None -> loop sig_items)
    | [] -> raise_errorf ~loc "[%%import]: cannot locate type %s"
                              (String.concat "." (Longident.flatten lid))
  in
  loop sig_items

let locate_ttype_decl =
  locate_tsig_item (fun elem ->
    function
    | Sig_type ({ name }, type_decl, _) when name = elem -> Some type_decl
    | _ -> None)

let locate_tmodtype_decl =
  locate_tsig_item (fun elem ->
    function
    | Sig_modtype ({ name }, type_decl) when name = elem -> Some type_decl
    | _ -> None)

let rec longident_of_path path =
  match path with
  | Path.Pident { name } -> Lident name
  | Path.Pdot (path, name, _) -> Ldot (longident_of_path path, name)
  | Path.Papply (lhs, rhs) -> Lapply (longident_of_path lhs, longident_of_path rhs)

module H = Hashtbl.Make (struct type t = type_expr let equal t1 t2 = t1 == t2 let hash t = t.id end)

let fresh_var, refresh_var_scope =
  let counter = ref ~-1 in
  (fun () ->
    incr counter;
    "tv__" ^ string_of_int !counter),
  (fun () -> counter := -1)

let rec core_type_of_type_expr =
  let rec has_row_field te =
    match te.desc with
    | Tfield (_, _, _, ts) -> has_row_field ts
    | Tnil                 -> false
    | Tvar _               -> true
    | _                    -> assert false
  in
  let rec has_row_var te =
    match te.desc with
    | Tvar _                -> true
    | Tnil                  -> false
    | Tvariant { row_more } -> has_row_var row_more
    | _                     -> assert false
  in
  fun ~equality_cache ~subst ?(varsubst=[]) ->
    let core_type_of_type_expr t = core_type_of_type_expr ~equality_cache ~subst ~varsubst t in
    let named ~mk path args =
      let lid  = longident_of_path path in
      let args = (List.map core_type_of_type_expr args) in
      begin match List.assoc lid subst with
        | { ptyp_desc = Ptyp_constr (lid, _) } as typ ->
          { typ with ptyp_desc = (mk lid args).ptyp_desc }
        | _ -> assert false
        | exception Not_found ->
          mk { txt = lid; loc = !default_loc } args
      end
    in
    let subst_var v = try List.assoc v varsubst with Not_found -> v in
    fun type_expr ->
      let cache_result ~is_polymorphic r =
        if not is_polymorphic then r
        else
          let v = fresh_var () in
          H.add equality_cache type_expr v;
          Typ.alias r v
      in
      match type_expr.desc with
      | Tvar None | Tvar (Some "_") -> Typ.any ()
      | Tvar (Some var) -> Typ.var (subst_var var)
      | Tarrow (label, lhs, rhs, _) ->
        Typ.arrow label (core_type_of_type_expr lhs) (core_type_of_type_expr rhs)
      | Ttuple xs ->
        Typ.tuple (List.map core_type_of_type_expr xs)
      | Tconstr (path, args, _) -> named ~mk:Typ.constr path args
      | Tvariant { row_more }
        when has_row_var row_more && H.mem equality_cache type_expr ->
        Typ.var (H.find equality_cache type_expr)
      | Tvariant { row_fields; row_closed; row_more } ->
        let poly = ref None in
        let fields =
          row_fields |> List.map (fun (label, row_field) ->
              let rec mapper =
                function
                | Rpresent None -> Rtag (label, [], true, [])
                | Rpresent (Some ttyp) ->
                  Rtag (label, [], false, [core_type_of_type_expr ttyp])
                | Reither (_, _, _, { contents = Some rf }) -> mapper rf
                | Reither (flag, ttys, _, _) ->
                  poly := Some [];
                  Rtag (label, [], flag, List.map core_type_of_type_expr ttys)
                | _ -> assert false
              in
              mapper row_field)
        in
        let ptyp = Typ.variant fields (if row_closed then Closed else Open) !poly in
        let rec finish row_more =
          match row_more.desc with
          | Tvar (Some "_" | None)
          | Tnil
          | Tconstr (_, [], { contents = Mnil }) -> ptyp
          | Tvar (Some v) when v <> "_"          -> Typ.alias ptyp (subst_var v)
          | Tvariant { row_more }                -> finish row_more
          | _                                    ->
            raise_errorf "Unknown row variable description: %s" (Format.asprintf "%a" Printtyp.type_expr row_more)
        in
        cache_result ~is_polymorphic:(has_row_var row_more) @@ finish row_more
      | Tobject (fds, _)
        when has_row_field fds && H.mem equality_cache type_expr ->
        Typ.var (H.find equality_cache type_expr)
      | Tobject (fds, { contents = Some (path, args) }) ->
        cache_result ~is_polymorphic:(has_row_field fds) @@ named ~mk:Typ.class_ path @@ List.tl args
      | Tobject (fds, { contents = None }) ->
        let rec fields t =
          match t.desc with
          | Tfield (s, Fpresent, t, ts)     ->
            let varopt, ts = fields ts in
            varopt, (s, [], core_type_of_type_expr t) :: ts
          | Tnil                            -> None, []
          | Tvar None
          | Tvar (Some "_")                 -> Some None, []
          | Tvar (Some v)                   -> Some (Some (subst_var v)), []
          | _                               -> assert false
        in
        let r =
          match fields fds with
          | None,          fields      -> Typ.object_ fields Closed
          | Some None,     fields      -> Typ.object_ fields Open
          | Some (Some v), fields      -> Typ.alias (Typ.object_ fields Open) v
        in
        cache_result ~is_polymorphic:(has_row_field fds) r
      | Tpoly (ty, tys) ->
        let tys =
          List.map
            (fun ty ->
               ty |>
               core_type_of_type_expr |>
               function
               | { ptyp_desc = Ptyp_var s; _ } -> s
               | _ ->
                 raise_errorf "Unsupported type description: \
                               constrained explicit polymorphism, e.g. 'a. ([> ] as 'a)")
            tys
        in
        Typ.poly tys (core_type_of_type_expr ty)
      | Tpackage _ -> raise_errorf "Unsupported type description: package, e.g. (module S)"
      | Tnil | Tfield _ | Tlink _ | Tsubst _ | Tunivar _ -> assert false

let ptype_decl_of_ttype_decl =
  let equality_cache = H.create 32 in
  let refresh_var_scope () =
    H.clear equality_cache;
    refresh_var_scope ()
  in
  fun ?params ?manifest ~subst ptype_name ttype_decl ->
    refresh_var_scope ();
    let ptype_params, (varsubst, cstrs) =
      match params with
      | Some params when List.(length params = length ttype_decl.type_params) ->
        params,
        let varsubst =
          List.fold_left2
            (fun acc orig (subst, _) ->
               match orig.desc, subst.ptyp_desc with
               | Tvar (Some v), Ptyp_var v' -> (v, v') :: acc
               | _ -> acc)
            []
            ttype_decl.type_params params
        in
        varsubst,
        List.fold_left2
          (fun acc orig (subst', _) ->
             match orig.desc, subst'.ptyp_desc with
             | Tvar _, _           -> acc
             | _,      Ptyp_var v' ->
               (v', core_type_of_type_expr ~equality_cache ~subst ~varsubst orig, subst'.ptyp_loc) :: acc
             | _ -> acc)
          []
          ttype_decl.type_params params
      | Some params ->
        raise_errorf ~loc:ptype_name.loc
          "A type with %d parameter(s) can't be imported as type `%s' with %d parameter(s)"
          (List.length ttype_decl.type_params) ptype_name.txt (List.length params)
      | None ->
        List.map2 (fun param variance ->
            core_type_of_type_expr ~equality_cache ~subst param,
            Invariant (* TODO *))
          ttype_decl.type_params ttype_decl.type_variance,
        ([], [])
    in
    let core_type_of_type_expr = core_type_of_type_expr ~equality_cache ~subst ~varsubst in
    let ptype_kind =
      match ttype_decl.type_kind with
      | Type_abstract -> Ptype_abstract
      | Type_open -> Ptype_open
      | Type_record (labels, _) ->
        Ptype_record (labels |> List.map (fun ld ->
            { pld_name       = { txt = ld.ld_id.name; loc = ld.ld_loc };
              pld_mutable    = ld.ld_mutable;
              pld_type       = core_type_of_type_expr ld.ld_type;
              pld_loc        = ld.ld_loc;
              pld_attributes = ld.ld_attributes; }))
      | Type_variant constrs ->
        Ptype_variant (constrs |> List.map (fun cd ->
            refresh_var_scope ();
            { pcd_name       = { txt = cd.cd_id.name; loc = cd.cd_loc };
              pcd_args       =
                (match cd.cd_args with
                 | Cstr_tuple typs -> Pcstr_tuple (List.map core_type_of_type_expr typs)
                 | Cstr_record lds ->
                   Pcstr_record
                     (List.map
                        (fun { ld_id = { name = txt };
                               ld_mutable = pld_mutable;
                               ld_type;
                               ld_loc = pld_loc;
                               ld_attributes = pld_attributes } ->
                          { pld_name = { txt; loc = pld_loc };
                            pld_mutable;
                            pld_type = core_type_of_type_expr ld_type;
                            pld_loc;
                            pld_attributes })
                        lds));
              pcd_res        = (match cd.cd_res with Some x -> Some (core_type_of_type_expr x)
                                                   | None -> None);
              pcd_loc        = cd.cd_loc;
              pcd_attributes = cd.cd_attributes; }))
    and ptype_manifest =
      match ttype_decl.type_manifest with
      | Some typ -> Some (core_type_of_type_expr typ)
      | None -> manifest
    in
    { ptype_name; ptype_params; ptype_kind; ptype_manifest;
      ptype_cstrs      = List.map (fun (v, ct, loc) -> Typ.var v, ct, loc) cstrs;
      ptype_private    = Public;
      ptype_attributes = ttype_decl.type_attributes;
      ptype_loc        = ttype_decl.type_loc; }

let subst_of_manifest { ptyp_attributes; ptyp_loc } =
  let rec subst_of_expr expr =
    match expr with
    | [%expr [%e? { pexp_desc = Pexp_ident ({ txt = src }) }] :=
             [%e? { pexp_desc = Pexp_ident (dst); pexp_attributes; pexp_loc }]] ->
      [src, { ptyp_loc = pexp_loc; ptyp_attributes = pexp_attributes;
              ptyp_desc = Ptyp_constr (dst, []) }]
    | [%expr [%e? { pexp_desc = Pexp_ident ({ txt = src }) }] :=
             [%e? { pexp_desc = Pexp_ident (dst); pexp_attributes; pexp_loc }]; [%e? rest]] ->
      (src, { ptyp_loc = pexp_loc; ptyp_attributes = pexp_attributes;
              ptyp_desc = Ptyp_constr (dst, []) }) :: subst_of_expr rest
    | { pexp_loc } ->
      raise_errorf ~loc:pexp_loc "Invalid [@with] syntax"
  in
  match Ast_convenience.find_attr "with" ptyp_attributes with
  | None -> []
  | Some (PStr [{ pstr_desc = Pstr_eval (expr, []) }]) ->
    subst_of_expr expr
  | Some _ ->
    raise_errorf ~loc:ptyp_loc "Invalid [@with] syntax"

let type_declaration mapper type_decl =
  match type_decl with
  | { ptype_attributes; ptype_name; ptype_params = params; ptype_manifest = Some {
        ptyp_desc = Ptyp_extension ({ txt = "import"; loc }, payload) } } ->
    begin match payload with
    | PTyp ({ ptyp_desc = Ptyp_constr ({ txt = lid; loc }, _) } as manifest) ->
      if Ast_mapper.tool_name () = "ocamldep" then
        (* Just put it as manifest *)
        { type_decl with ptype_manifest = Some manifest }
      else
        with_default_loc loc (fun () ->
          let subst = subst_of_manifest manifest in
          let subst = subst @ [Lident (Longident.last lid),
                               Typ.constr { txt = Lident ptype_name.txt; loc = ptype_name.loc } []] in
          let ttype_decl = locate_ttype_decl ~loc (locate_sig ~loc lid) lid in
          let ptype_decl = ptype_decl_of_ttype_decl ~params ~manifest ~subst ptype_name ttype_decl in
          { ptype_decl with ptype_attributes })
    | _ -> raise_errorf ~loc "Invalid [%%import] syntax"
    end
  | _ -> default_mapper.type_declaration mapper type_decl

let rec psig_of_tsig ~subst ?(trec=[]) tsig =
  match tsig with
  | Sig_type ({ name }, ttype_decl, rec_flag) :: rest ->
    let ptype_decl = ptype_decl_of_ttype_decl ~subst (Location.mknoloc name) ttype_decl in
    begin match rec_flag with
    | Trec_not ->
      { psig_desc = Psig_type (Nonrecursive, [ptype_decl]); psig_loc = Location.none } ::
      psig_of_tsig ~subst rest
    | Trec_first | Trec_next ->
      psig_of_tsig ~subst ~trec:(ptype_decl :: trec) rest
    end
  | _ when trec <> [] ->
    { psig_desc = Psig_type (Recursive, trec); psig_loc = Location.none } ::
    psig_of_tsig ~subst tsig
  | Sig_value ({ name }, { val_type; val_kind; val_loc; val_attributes }) :: rest ->
    let pval_prim =
      match val_kind with
      | Val_reg -> []
      | Val_prim p ->
        (Primitive.print
           p
           { Outcometree.
             oval_name = "";
             oval_type = Outcometree.Otyp_abstract;
             oval_prims = [];
             oval_attributes = [] })
        .Outcometree.oval_prims
      | _ -> assert false
    in
    { psig_desc = Psig_value {
        pval_name = Location.mknoloc name; pval_loc = val_loc;
        pval_attributes = val_attributes;
        pval_prim; pval_type = core_type_of_type_expr ~equality_cache:(H.create 32) ~subst val_type; };
      psig_loc = val_loc } ::
    psig_of_tsig ~subst rest
  | [] -> []
  | _ -> assert false

let module_type mapper modtype_decl =
  match modtype_decl with
  | { pmty_attributes; pmty_desc = Pmty_extension ({ txt = "import"; loc }, payload) } ->
    begin match payload with
    | PTyp ({ ptyp_desc = Ptyp_package({ txt = lid; loc } as alias, subst) }) ->
      if Ast_mapper.tool_name () = "ocamldep" then
        (* Just put it as alias *)
        { modtype_decl with pmty_desc = Pmty_alias alias }
      else
        with_default_loc loc (fun () ->
          match locate_tmodtype_decl ~loc (locate_sig ~loc lid) lid with
          | { mtd_type = Some (Mty_signature tsig) } ->
            let subst = List.map (fun ({ txt; }, typ) -> txt, typ) subst in
            let psig  = psig_of_tsig ~subst tsig in
            { modtype_decl with pmty_desc = Pmty_signature psig }
          | { mtd_type = None } ->
            raise_errorf ~loc "Imported module is abstract"
          | _ ->
            raise_errorf ~loc "Imported module is indirectly defined")
    | _ -> raise_errorf ~loc "Invalid [%%import] syntax"
    end
  | _ -> default_mapper.module_type mapper modtype_decl

let () =
  Ast_mapper.register "ppx_import" (fun argv ->
    { default_mapper with type_declaration; module_type; })
