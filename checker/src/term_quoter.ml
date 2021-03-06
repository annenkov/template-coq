(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

open Constr
open Ast0
open Template_coq
open Quoter

let quote_string s =
  let rec aux acc i =
    if i < 0 then acc
    else aux (s.[i] :: acc) (i - 1)
  in aux [] (String.length s - 1)

let unquote_string l =
  let buf = Bytes.create (List.length l) in
  let rec aux i = function
    | [] -> ()
    | c :: cs ->
      Bytes.set buf i c; aux (succ i) cs
  in
  aux 0 l;
  Bytes.to_string buf

module TemplateASTQuoter =
struct
  type t = term
  type quoted_ident = char list
  type quoted_int = Datatypes.nat
  type quoted_bool = bool
  type quoted_name = name
  type quoted_aname = Ast0.aname
  type quoted_relevance = Ast0.relevance
  type quoted_sort = Univ0.universe
  type quoted_cast_kind = cast_kind
  type quoted_kernel_name = char list
  type quoted_inductive = inductive
  type quoted_proj = projection
  type quoted_global_reference = global_reference

  type quoted_sort_family = sort_family
  type quoted_constraint_type = Univ0.constraint_type
  type quoted_univ_constraint = Univ0.univ_constraint
  type quoted_univ_instance = Univ0.Instance.t
  type quoted_univ_constraints = Univ0.constraints
  type quoted_univ_context = Univ0.universe_context
  type quoted_inductive_universes = quoted_univ_context

  type quoted_mind_params = Ast0.rel_declaration list
  type quoted_ind_entry = quoted_ident * t * quoted_bool * quoted_ident list * t list
  type quoted_definition_entry = t * t option * quoted_univ_context
  type quoted_mind_entry = mutual_inductive_entry
  type quoted_mind_finiteness = recursivity_kind
  type quoted_entry = (constant_entry, quoted_mind_entry) sum option

  type quoted_one_inductive_body = one_inductive_body
  type quoted_mutual_inductive_body = mutual_inductive_body
  type quoted_constant_body = constant_body
  type quoted_global_decl = global_decl
  type quoted_global_declarations = global_declarations
  type quoted_program = program

  open Names

  let quote_ident id =
    quote_string (Id.to_string id)

  let quote_relevance r =
    match r with
    | Sorts.Relevant -> Ast0.Relevant
    | Sorts.Irrelevant -> Ast0.Irrelevant

  let quote_aname ann_n =
    let {Context.binder_name = n; Context.binder_relevance = relevance} = ann_n in
    let r = quote_relevance relevance in
    match n with
    | Anonymous -> {Ast0.binder_name = Coq_nAnon; Ast0.binder_relevance = r}
    | Name i -> {Ast0.binder_name = Coq_nNamed (quote_ident i); Ast0.binder_relevance = r}

  let quote_name = function
    | Anonymous -> Coq_nAnon
    | Name i -> Coq_nNamed (quote_ident i)

  let quote_int i =
    let rec aux acc i =
      if i < 0 then acc
      else aux (Datatypes.S acc) (i - 1)
    in aux Datatypes.O (i - 1)

  let quote_bool x = x

  let quote_level l =
    if Univ.Level.is_prop l then Univ0.Level.prop
    else if Univ.Level.is_set l then Univ0.Level.set
    else match Univ.Level.var_index l with
         | Some x -> Univ0.Level.Var (quote_int x)
         | None -> Univ0.Level.Level (quote_string (Univ.Level.to_string l))

  let quote_universe s : Univ0.universe =
    (* hack because we can't recover the list of level*int *)
    (* todo : map on LSet is now exposed in Coq trunk, we should use it to remove this hack *)
    let levels = Univ.LSet.elements (Univ.Universe.levels s) in
    List.map (fun l -> let l' = quote_level l in
                       (* is indeed i always 0 or 1 ? *)
                       let b' = quote_bool (Univ.Universe.exists (fun (l2,i) -> Univ.Level.equal l l2 && i = 1) s) in
                       (l', b'))
             levels

  let quote_sort s =
    quote_universe (Sorts.univ_of_sort s)

  let quote_sort_family s =
    match s with
    | Sorts.InProp -> Ast0.InProp
    | Sorts.InSProp -> Ast0.InSProp
    | Sorts.InSet -> Ast0.InSet
    | Sorts.InType -> Ast0.InType

  let quote_cast_kind = function
    | DEFAULTcast -> Cast
    | REVERTcast -> RevertCast
    | NATIVEcast -> NativeCast
    | VMcast -> VmCast

  let quote_kn kn = quote_string (KerName.to_string kn)
  let quote_inductive (kn, i) = { inductive_mind = kn ; inductive_ind = i }
  let quote_proj ind p a = ((ind,p),a)

  let quote_constraint_type = function
    | Univ.Lt -> Univ0.ConstraintType.Lt
    | Univ.Le -> Univ0.ConstraintType.Le
    | Univ.Eq -> Univ0.ConstraintType.Eq

  let quote_univ_constraint ((l, ct, l') : Univ.univ_constraint) : quoted_univ_constraint =
    ((quote_level l, quote_constraint_type ct), quote_level l')

  let quote_univ_instance (i : Univ.Instance.t) : quoted_univ_instance =
    let arr = Univ.Instance.to_array i in
    CArray.map_to_list quote_level arr

  let quote_univ_constraints (c : Univ.Constraint.t) : quoted_univ_constraints =
    List.map quote_univ_constraint (Univ.Constraint.elements c)

  let quote_univ_context (uctx : Univ.UContext.t) : quoted_univ_context =
    let levels = Univ.UContext.instance uctx  in
    let constraints = Univ.UContext.constraints uctx in
    Univ0.Monomorphic_ctx (quote_univ_instance levels, quote_univ_constraints constraints)

  let quote_abstract_univ_context_aux uctx : quoted_univ_context =
    let levels = Univ.UContext.instance uctx in
    let constraints = Univ.UContext.constraints uctx in
    Univ0.Polymorphic_ctx (quote_univ_instance levels, quote_univ_constraints constraints)

  let quote_abstract_univ_context (uctx : Univ.AUContext.t) =
    let uctx = Univ.AUContext.repr uctx in
    quote_abstract_univ_context_aux uctx

  let quote_inductive_universes = function
    | Entries.Monomorphic_ind_entry ctx -> quote_univ_context (Univ.ContextSet.to_context ctx)
    | Entries.Polymorphic_ind_entry (_,ctx) -> quote_abstract_univ_context_aux ctx
    | Entries.Cumulative_ind_entry (_,ctx) ->
      quote_abstract_univ_context_aux (Univ.CumulativityInfo.univ_context ctx)

  let mkAnon = Coq_nAnon
  let mkName i = Coq_nNamed i

  let mkAAnon r = {Ast0.binder_name = mkAnon; Ast0.binder_relevance = r}
  let mkAName i r = {Ast0.binder_name = mkName i; Ast0.binder_relevance = r}


  let mkRel n = Coq_tRel n
  let mkVar id = Coq_tVar id
  let mkMeta n = Coq_tMeta n
  let mkEvar n args = Coq_tEvar (n,Array.to_list args)
  let mkSort s = Coq_tSort s
  let mkCast c k t = Coq_tCast (c,k,t)

  let mkConst c u = Coq_tConst (c, u)
  let mkProd na t b = Coq_tProd (na, t, b)
  let mkLambda na t b = Coq_tLambda (na, t, b)
  let mkApp f xs = Coq_tApp (f, Array.to_list xs)
  let mkInd i u = Coq_tInd (i, u)
  let mkConstruct (ind, i) u = Coq_tConstruct (ind, i, u)
  let mkLetIn na b t t' = Coq_tLetIn (na,b,t,t')

  let rec seq f t =
    if f < t then
      f :: seq (f + 1) t
    else []

  let mkFix ((a,b),(ns,ts,ds)) =
    let mk_fun xs i =
      { dname = Array.get ns i ;
        dtype = Array.get ts i ;
        dbody = Array.get ds i ;
        rarg = Array.get a i } :: xs
    in
    let defs = List.fold_left mk_fun [] (seq 0 (Array.length a)) in
    let block = List.rev defs in
    Coq_tFix (block, b)

  let mkCoFix (a,(ns,ts,ds)) =
    let mk_fun xs i =
      { dname = Array.get ns i ;
        dtype = Array.get ts i ;
        dbody = Array.get ds i ;
        rarg = Datatypes.O } :: xs
    in
    let defs = List.fold_left mk_fun [] (seq 0 (Array.length ns)) in
    let block = List.rev defs in
    Coq_tFix (block, a)

  let mkCase (ind, npar) nargs p is c brs =
    let info = (ind, npar) in
    let branches = List.map2 (fun br nargs ->  (nargs, br)) brs nargs in
    Coq_tCase (info,p,is,c,branches)
  let mkProj p c = Coq_tProj (p,c)

  let mk_one_inductive_body (id, ty, kel, ctr, proj, relevance) =
    let ctr = List.map (fun (a, b, c) -> ((a, b), c)) ctr in
    { ind_name = id; ind_type = ty;
      ind_kelim = kel; ind_ctors = ctr; ind_projs = proj; ind_relevant = relevance }

  let mk_mutual_inductive_body parms inds uctx =
    {ind_npars = parms; ind_bodies = inds; ind_universes = uctx}

  let mk_constant_body ty tm uctx =
    {cst_type = ty; cst_body = tm; cst_universes = uctx}

  let mk_inductive_decl kn bdy = InductiveDecl (kn, bdy)

  let mk_constant_decl kn bdy = ConstantDecl (kn, bdy)

  let empty_global_declartions = []

  let add_global_decl a b = a :: b

  let mk_program decls tm = (decls, tm)

  let quote_mind_finiteness = function
    | Declarations.Finite -> Finite
    | Declarations.CoFinite -> CoFinite
    | Declarations.BiFinite -> BiFinite

  let quote_mind_params l =
    let map (n,body) =
      match body with
      | Right ty -> LocalAssum (n,ty)
      | Left (b,t) -> LocalDef (n,b,t)
    in List.map map l

  let quote_one_inductive_entry (id, ar, b, consnames, constypes) =
    { mind_entry_typename = id;
      mind_entry_arity = ar;
      mind_entry_template = b;
      mind_entry_consnames = consnames;
      mind_entry_lc = constypes }

  let quote_mutual_inductive_entry (mf, mp, is, univs) =
    { mind_entry_record = None;
      mind_entry_finite = mf;
      mind_entry_params = mp;
      mind_entry_inds = List.map quote_one_inductive_entry is;
      mind_entry_universes = univs;
      mind_entry_private = None }

  let quote_entry e =
    match e with
    | Some (Left (ty, body, ctx)) ->
       let entry = match body with
         | None -> ParameterEntry { parameter_entry_type = ty;
                                    parameter_entry_universes = ctx }
        | Some b -> DefinitionEntry { definition_entry_type = ty;
                                      definition_entry_body = b;
                                      definition_entry_universes = ctx;
                                      definition_entry_opaque = false }
       in Some (Left entry)
    | Some (Right mind_entry) ->
       Some (Right mind_entry)
    | None -> None

  let inspectTerm (t : term) :  (term, quoted_int, quoted_ident, quoted_name, quoted_sort, quoted_cast_kind, quoted_kernel_name, quoted_inductive, quoted_univ_instance, quoted_proj) structure_of_term =
   match t with
  | Coq_tRel n -> ACoq_tRel n
    (* so on *)
  | _ ->  failwith "not yet implemented"




  let unquote_ident (qi: quoted_ident) : Id.t =
    let s = unquote_string qi in
    Id.of_string s

  let unquote_name (q: quoted_name) : Name.t =
    match q with
    | Coq_nAnon -> Anonymous
    | Coq_nNamed n -> Name (unquote_ident n)

  let rec unquote_int (q: quoted_int) : int =
    match q with
    | Datatypes.O -> 0
    | Datatypes.S x -> succ (unquote_int x)

  let unquote_bool (q : quoted_bool) : bool = q

  (* val unquote_sort : quoted_sort -> Sorts.t *)
  (* val unquote_sort_family : quoted_sort_family -> Sorts.family *)
  let unquote_cast_kind (q : quoted_cast_kind) : Constr.cast_kind =
    match q with
    | VmCast -> VMcast
    | NativeCast -> NATIVEcast
    | Cast -> DEFAULTcast
    | RevertCast -> REVERTcast

  let unquote_kn (q: quoted_kernel_name) : Libnames.qualid =
    let s = unquote_string q in
    Libnames.qualid_of_string s

  let unquote_inductive (q: quoted_inductive) : Names.inductive =
    let { inductive_mind = na; inductive_ind = i } = q in
    let comps = CString.split_on_char '.' (unquote_string na) in
    let comps = List.map Id.of_string comps in
    let id, dp = CList.sep_last comps in
    let dp = DirPath.make dp in
    let mind = MutInd.make2 (MPfile dp) (Label.of_id id) in
    (mind, unquote_int i)

  (*val unquote_univ_instance :  quoted_univ_instance -> Univ.Instance.t *)
  let unquote_proj (q : quoted_proj) : (quoted_inductive * quoted_int * quoted_int) =
    let (ind, ps), idx = q in
    (ind, ps, idx)

  let unquote_level (trm : Univ0.Level.t) : Univ.Level.t =
    match trm with
    | Univ0.Level.Coq_lProp -> Univ.Level.prop
    | Univ0.Level.Coq_lSet -> Univ.Level.set
    | Univ0.Level.Level s ->
      let s = unquote_string s in
      let comps = CString.split '.' s in
      let last, dp = CList.sep_last comps in
      let dp = DirPath.make (List.map Id.of_string comps) in
      let idx = int_of_string last in
      Univ.Level.make dp idx
    | Univ0.Level.Var n -> Univ.Level.var (unquote_int n)

  let unquote_level_expr (trm : Univ0.Level.t) (b : quoted_bool) : Univ.Universe.t =
    let l = unquote_level trm in
    let u = Univ.Universe.make l in
    if b then Univ.Universe.super u
    else u

  let unquote_universe evd (trm : Univ0.Universe.t) =
    match trm with
    | [] -> Evd.new_univ_variable (Evd.UnivFlexible false) evd
    | (l,b)::q ->
      evd, List.fold_left (fun u (l,b) ->
          let u' = unquote_level_expr l b in Univ.Universe.sup u u')
        (unquote_level_expr l b) q

  let print_term (u: t) : Pp.t = failwith "print_term in term_quoter.ml not yet implemented"

end



module TemplateASTReifier = Reify(TemplateASTQuoter)

include TemplateASTReifier
