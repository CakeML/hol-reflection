structure reflectionLib = struct
local
  open HolKernel boolLib bossLib lcsymtacs listSimps stringSimps
  open miscLib miscTheory combinTheory pred_setTheory numSyntax pairSyntax stringSyntax listSyntax holSyntaxSyntax
  open setSpecTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory
  open holBoolTheory holConstrainedExtensionTheory
  open reflectionTheory basicReflectionLib

  val concat = List.concat

  val bool_to_inner_tm = ``bool_to_inner``
  val fun_to_inner_tm = ``fun_to_inner``

  val universe_ty = ``:'U``
  val type_ty = ``:type``
  fun to_inner_tm ty =
    mk_comb (
      mk_const ("to_inner0", (universe_ty --> universe_ty --> bool)
                         --> type_ty --> ty --> universe_ty),
      mk_var ("mem", universe_ty --> universe_ty --> bool)
    )

  fun mk_to_inner (ty : hol_type) = case type_view ty of
      Tyapp(thy, "bool", [])        => bool_to_inner_tm
    | Tyapp(thy, "fun",  [ty1,ty2]) => mk_binop fun_to_inner_tm (mk_to_inner ty1, mk_to_inner ty2)
    | _                             => mk_monop (to_inner_tm ty) (type_to_deep ty)

  fun to_inner_prop (ty : hol_type) : term =
    ``wf_to_inner ^(mk_to_inner ty)``

  fun mk_range (ty : hol_type) : term =
    ``range ^(mk_to_inner ty)``

  datatype any_type_view =
    BoolType | FunType of hol_type * hol_type | BaseType of type_view

  fun base_type_view (ty : hol_type) : type_view = case type_view ty of
      Tyapp(thy, "bool", [])        => raise Fail "base_type_view called on bool"
    | Tyapp(thy, "fun",  [ty1,ty2]) => raise Fail "base_type_view called on funtype"
    | view                          => view

  fun any_type_view (ty : hol_type) : any_type_view = case type_view ty of
      Tyapp(thy, "bool", [])        => BoolType
    | Tyapp(thy, "fun",  [ty1,ty2]) => FunType(ty1,ty2)
    | view                          => BaseType view

  fun base_types_of_type (ty : hol_type) : hol_type list = case any_type_view ty of
      BoolType         => []
    | BaseType v       => ty::(case v of Tyvar _ => []
                                       | Tyapp(_,_,args) =>
                                           concat(map base_types_of_type args))
    | FunType(ty1,ty2) => base_types_of_type ty1 @ base_types_of_type ty2

  fun base_type_assums (ty : hol_type) : term list = case base_type_view ty of
      Tyapp(thy, name, args) => [``FLOOKUP tysig ^(string_to_inner name) =
                                     SOME ^(term_of_int (length args))``,
                                 ``tyass ^(string_to_inner name)
                                     ^(mk_list(map mk_range args,universe_ty)) =
                                     ^(mk_range ty)``]
    | Tyvar name             => [``tyval ^(string_to_inner name) = ^(mk_range ty)``]

  val type_assums : hol_type -> term list =
    flatten o map (fn ty => to_inner_prop ty :: base_type_assums ty) o base_types_of_type

  fun typesem_prop (ty : hol_type) : term =
    ``typesem tyass tyval ^(type_to_deep ty) = ^(mk_range ty)``

  local
    val good_context = hd(hyp good_context_tyass_bool)
    val good_context_tyass_fun_simp =
      good_context_tyass_fun |> SIMP_RULE std_ss []
  in
    fun typesem_cert ty =
      let
        val goal = (good_context::(type_assums ty), typesem_prop ty)
        (* set_goal goal *)
      in
        TAC_PROOF(goal,
          rpt(
            (CHANGED_TAC(REWRITE_TAC[typesem_def,listTheory.MAP,ETA_AX]))
            ORELSE
            (CHANGED_TAC(ASM_SIMP_TAC std_ss
              [good_context_tyass_bool,
               good_context_tyass_fun_simp,
               good_context_wf_to_inner_bool_to_inner,
               good_context_wf_to_inner_fun_to_inner]))
            ORELSE match_mp_tac good_context_tyass_fun))
      end
  end

  fun types_of_term (tm : term) : hol_type list = case dest_term tm of
      VAR (name,ty)       => [ty]
    | CONST {Name,Thy,Ty} => [Ty]
    | LAMB (var,body)     => type_of var :: types_of_term body
    | COMB (tm1,tm2)      => types_of_term tm1 @ types_of_term tm2

  val base_types_of_term : term -> hol_type list =
    flatten o (map base_types_of_type) o types_of_term


  fun dest_base_term (tm : term) : lambda = case dest_term tm of
      LAMB (var,body)     => raise Fail "dest_base_term called on lambda"
    | COMB (tm1,tm2)      => raise Fail "dest_base_term called on combination"
    | view                => view


  fun const_tyargs (thy : string) (name : string) (ty : hol_type) : hol_type list =
    let val pty = type_of (first (equal name o fst o dest_const) (thy_consts thy))
        fun str_le (x : string) (y : string) = not ((String.compare (x,y)) = GREATER)
        fun tyvar_to_str (x : hol_type) = tyvar_to_deep (dest_vartype x)
        fun le x y = str_le (fst x) (fst y)
        val sub = map (fn {redex,residue} => (tyvar_to_str redex, residue))
                      (match_type pty ty)
     in map snd (sort le sub)
    end


  fun base_terms_of_term (tm : term) : term list = case dest_term tm of
      VAR (name,ty)       => [tm]
    | CONST {Name,Thy,Ty} => [tm]
    | LAMB (var,body)     => filter (not o equal var) (base_terms_of_term body)
    | COMB (tm1,tm2)      => base_terms_of_term tm1 @ base_terms_of_term tm2

  fun base_term_assums (tm : term) : term list = case dest_base_term tm of
      VAR (name,ty)       => [``tmval (^(string_to_inner name), ^(type_to_deep ty)) =
                                  ^(mk_to_inner ty) ^tm``]
    | CONST {Thy,Name,Ty} => [``FLOOKUP tmsig ^(string_to_inner Name) =
                                  SOME ^(type_to_deep Ty)``,
                              ``tmass ^(string_to_inner Name)
                                      ^(mk_list (map mk_range
                                                   (const_tyargs Thy Name Ty),
                                                 universe_ty)) =
                                  ^(mk_to_inner Ty) ^tm``]

  (* TODO: Remove duplicates here and elsewhere. *)
  fun term_assums (tm : term) : term list =
    flatten (map base_type_assums (base_types_of_term tm)) @
    flatten (map base_term_assums (base_terms_of_term tm))

  type update = {
    sound_update_thm  : thm, (* |- sound_update ctxt upd *)
    constrainable_thm : thm, (* |- constrainable_update upd *)
    tys : hol_type list,
    consts : term list,
    axs : thm list }

  fun find_type_instances toconstrain fromupdate =
    mk_set (
    foldl
      (fn (ty1,acc) =>
        foldl (fn (ty2,acc) =>
                    case total (match_type ty1) ty2 of NONE => acc
                      | SOME s => s::acc)
                 acc
                 toconstrain)
      []
      fromupdate
    )

  fun find_const_instances toconstrain fromupdate =
    mk_set (
    foldl
      (fn (tm1,acc) =>
        foldl (fn (tm2,acc) =>
                    case total (match_term tm1) tm2 of NONE => acc
                      | SOME (_,s) => s::acc)
                 acc
                 toconstrain)
      []
      fromupdate
    )

  local
    val bool_th = wf_to_inner_bool_to_inner |> UNDISCH
    val fun_th = wf_to_inner_fun_to_inner |> UNDISCH
  in
    fun wf_to_inner_mk_to_inner ty =
      case any_type_view ty of
        BoolType => bool_th
      | FunType(x,y) =>
        let
          val th1 = wf_to_inner_mk_to_inner x
          val th2 = wf_to_inner_mk_to_inner y
        in
          MATCH_MP fun_th (CONJ th1 th2)
        end
      | BaseType _ => ASSUME ``wf_to_inner ^(mk_to_inner ty)``
  end

  local
    val distinct_tag_bool_range = prove(
      ``is_set_theory ^mem ⇒
        !x. wf_to_inner ((to_inner x):'a -> 'U) ⇒
        range ((to_inner x):'a -> 'U) ≠ range bool_to_inner``,
      rw[] >>
      imp_res_tac is_extensional >>
      fs[extensional_def] >>
      qexists_tac`to_inner x ARB` >>
      qmatch_abbrev_tac`a ≠ b` >>
      qsuff_tac`~b`>-metis_tac[wf_to_inner_range_thm]>>
      simp[Abbr`a`,Abbr`b`,to_inner_def,range_bool_to_inner] >>
      simp[tag_def]) |> UNDISCH

    val distinct_tag_fun_range = prove(
      ``is_set_theory ^mem ⇒
        !x y z.
        wf_to_inner ((to_inner x):'a -> 'U) ⇒
        wf_to_inner y ⇒
        wf_to_inner z ⇒
        range ((to_inner x):'a -> 'U) ≠ range (fun_to_inner y z)``,
      rw[] >>
      imp_res_tac is_extensional >>
      fs[extensional_def] >>
      qexists_tac`to_inner x ARB` >>
      qmatch_abbrev_tac`a ≠ b` >>
      qsuff_tac`~b`>-metis_tac[wf_to_inner_range_thm]>>
      simp[Abbr`a`,Abbr`b`,to_inner_def,range_fun_to_inner] >>
      simp[tag_def]) |> UNDISCH

    val distinct_tags = prove(
      ``is_set_theory ^mem ⇒
        !x y.
        wf_to_inner ((to_inner x):'a -> 'U) ⇒
        wf_to_inner ((to_inner y):'b -> 'U) ⇒
        x ≠ y ⇒
        range ((to_inner x):'a -> 'U) ≠
        range ((to_inner y):'b -> 'U)``,
      rw[] >>
      imp_res_tac is_extensional >>
      fs[extensional_def] >>
      qexists_tac`to_inner x ARB` >>
      qmatch_abbrev_tac`a ≠ b` >>
      qsuff_tac`~b`>-metis_tac[wf_to_inner_range_thm]>>
      simp[Abbr`a`,Abbr`b`] >>
      spose_not_then strip_assume_tac >>
      imp_res_tac wf_to_inner_finv_right >>
      fs[to_inner_def] >>
      metis_tac[tag_def,pairTheory.PAIR_EQ]) |> UNDISCH

    val distinct_bool_fun = prove(
      ``is_set_theory ^mem ⇒
        !x y.
        wf_to_inner x ⇒
        wf_to_inner y ⇒
        range bool_to_inner ≠ range (fun_to_inner x y )``,
      rw[range_bool_to_inner,range_fun_to_inner] >>
      imp_res_tac is_extensional >>
      fs[extensional_def] >>
      pop_assum kall_tac >>
      rw[mem_boolset] >>
      qexists_tac`True` >> rw[] >>
      spose_not_then strip_assume_tac >>
      imp_res_tac in_funspace_abstract >>
      fs[abstract_def,true_def] >>
      imp_res_tac is_extensional >>
      fs[Once extensional_def] >> rfs[mem_empty] >>
      imp_res_tac wf_to_inner_range_thm >>
      rfs[mem_sub,mem_product] >>
      cheat) |> UNDISCH

    val distinct_fun_fun = prove(
      ``is_set_theory ^mem ⇒
        !d1 r1 d2 r2.
        wf_to_inner d1 ∧
        wf_to_inner r1 ∧
        wf_to_inner d2 ∧
        wf_to_inner r2 ⇒
        pair$, (range d1) (range r1) ≠ (range d2, range r2) ⇒
        range (fun_to_inner d1 r1) ≠ range (fun_to_inner d2 r2)``,
      rw[range_fun_to_inner] >>
      imp_res_tac is_extensional >>
      pop_assum mp_tac >>
      simp[extensional_def] >>
      disch_then kall_tac >- (
        cheat) >>
      cheat) |> UNDISCH

    val ERR = mk_HOL_ERR"reflectionLib""ranges_distinct"
    val ERR_same = ERR"same_types"
  in
    fun ranges_distinct ty1 ty2 =
      case (any_type_view ty1, any_type_view ty2) of
         (BoolType, BoolType) => raise ERR_same
      |  (BoolType, FunType (x,y)) =>
           distinct_bool_fun
           |> ISPECL [mk_to_inner x, mk_to_inner y]
           |> C MP (wf_to_inner_mk_to_inner x)
           |> C MP (wf_to_inner_mk_to_inner y)
      |  (FunType (x,y), BoolType) =>
           distinct_bool_fun
           |> ISPECL [mk_to_inner x, mk_to_inner y]
           |> C MP (wf_to_inner_mk_to_inner x)
           |> C MP (wf_to_inner_mk_to_inner y)
           |> GSYM
      |  (BaseType _, FunType(x,y)) =>
           distinct_tag_fun_range
           |> ISPECL [type_to_deep ty1, mk_to_inner x, mk_to_inner y]
           |> INST_TYPE[alpha|->ty1]
           |> UNDISCH
           |> C MP (wf_to_inner_mk_to_inner x)
           |> C MP (wf_to_inner_mk_to_inner y)
      |  (FunType (x,y), BaseType _) =>
           distinct_tag_fun_range
           |> ISPECL [type_to_deep ty2, mk_to_inner x, mk_to_inner y]
           |> INST_TYPE[alpha|->ty2]
           |> UNDISCH
           |> C MP (wf_to_inner_mk_to_inner x)
           |> C MP (wf_to_inner_mk_to_inner y)
           |> GSYM
      (* val (FunType (x1,y1), FunType (x2,y2)) = it *)
      |  (FunType (x1,y1), FunType (x2,y2)) =>
           let
             val tys = [x1,y1,x2,y2]
             val ranges = map mk_range tys
             val th1 =
               pairTheory.PAIR_EQ
               |> EQ_IMP_RULE |> fst
               |> CONTRAPOS
               |> CONV_RULE(LAND_CONV(REWR_CONV(
                    CONJUNCT1 (SPEC_ALL DE_MORGAN_THM))))
               |> Q.GENL(rev[`x`,`y`,`a`,`b`])
               |> ISPECL ranges
             val th2 =
               if x1 = x2 then
                 if y1 = y2 then raise ERR_same
                 else
                   DISJ2
                   (th1|>concl|>dest_imp|>fst|>dest_disj|>fst)
                   (ranges_distinct y1 y2)
               else
                 DISJ1
                 (ranges_distinct x1 x2)
                 (th1|>concl|>dest_imp|>fst|>dest_disj|>snd)
           in
             distinct_fun_fun
             |> ISPECL (map mk_to_inner tys)
             |> C MP (LIST_CONJ (map wf_to_inner_mk_to_inner tys))
             |> C MP (MP th1 th2)
           end
      |  (BaseType _, BoolType) =>
           distinct_tag_bool_range
           |> ISPEC (type_to_deep ty1)
           |> INST_TYPE[alpha|->ty1]
           |> UNDISCH
      |  (BoolType, BaseType _) =>
           distinct_tag_bool_range
           |> ISPEC (type_to_deep ty2)
           |> INST_TYPE[alpha|->ty2]
           |> UNDISCH
           |> GSYM
      |  (BaseType _, BaseType _) =>
           if ty1 = ty2 then raise ERR_same
           else let
             val tys = map type_to_deep [ty1, ty2]
             (* TODO: purpose-built conversion rather than EVAL? *)
             val th = EVAL(mk_eq(el 1 tys, el 2 tys)) |> EQF_ELIM
           in
             distinct_tags
             |> ISPECL tys
             |> INST_TYPE[alpha|->ty1,beta|->ty2]
             |> funpow 2 UNDISCH
             |> C MP th
           end
  end

  (*
    foldl : ('a * 'b -> b) -> 'b -> 'a list -> 'b
    match_type : hol_type -> hol_type -> (hol_type,hol_type) subst
    type_subst (match_type ty1 ty2) ty1 = ty2
    match_term : term -> term -> (term,term) subst * (hol_type,hol_type) subst
    INST_TYPE : (hol_type,hol_type) subst -> thm -> thm
    mk_set : ''a list -> ''a list
  *)

  fun cs_to_inner tys consts =
    let
      fun subst_to_cs s =
        let
          fun const_to_inner c =
            let
              val ic = inst s c
            in
              mk_comb(mk_to_inner (type_of ic), ic)
            end
          val inner_tys = map (mk_range o type_subst s) tys
          val inner_consts = map const_to_inner consts
        in
          mk_pair(mk_list(inner_tys,universe_ty),
                  mk_list(inner_consts,universe_ty))
        end
      fun subst_to_inner (s:(hol_type,hol_type)subst) =
        let
          fun cmp_to_P c x y = c (x,y) <> GREATER
          val by_name =
            cmp_to_P (inv_img_cmp (dest_vartype o #redex) String.compare)
          val sorted_subst = sort by_name s
          val sorted_vals = map (mk_range o #residue) sorted_subst
        in
          mk_list(sorted_vals,universe_ty)
        end
      fun foldthis (s,f) =
        mk_icomb(combinSyntax.mk_update
          (subst_to_inner s,
           optionSyntax.mk_some(subst_to_cs s)),
                 f)
    in
      foldl foldthis ``K NONE : 'U constraints``
    end

(*
val tys = [mk_list_type alpha]
val consts = [cons_tm]
val substs = [[alpha|->numSyntax.num],[alpha|->bool]]
val (s::_) = substs
val (_::s::_) = substs
cs_to_inner tys consts substs
*)

  (* TODO move *)
  val extends_refl = store_thm("extends_refl",
    ``∀ctxt. ctxt extends ctxt``,
    rw[extends_def])

  val hol_model_def = new_specification("hol_model_def",["hol_model0"],
    holConsistencyTheory.hol_has_model
    |> REWRITE_RULE[GSYM AND_IMP_INTRO]
    |> funpow 2 UNDISCH
    |> Q.SPEC`hol_ctxt`
    |> SIMP_RULE std_ss [extends_refl]
    |> CONJUNCT2
    |> DISCH_ALL
    |> CONV_RULE(RAND_CONV(HO_REWR_CONV(GSYM RIGHT_EXISTS_IMP_THM)))
    |> CONV_RULE(HO_REWR_CONV(GSYM RIGHT_EXISTS_IMP_THM))
    |> Q.GEN`mem`
    |> CONV_RULE(HO_REWR_CONV(SKOLEM_THM)))
  val _ = Parse.overload_on("hol_model",``hol_model0 ^mem``)
  val hol_model_def = save_thm("hol_model_def",
    hol_model_def |> SPEC mem |> funpow 2 UNDISCH)
  (* -- *)

  fun get_int th = th |> concl |> rator |> rand

  fun build_interpretation [] tys consts =
        let
          val tyassums = concat (map base_type_assums tys)
          val tmassums = concat (map base_term_assums consts)
          val assums = list_mk_conj (tyassums @ tmassms)
        in
            want:
            ^(concl hol_model_def) ∧ ^assums

            problem: hol_model doesn't necessarily satisfy assums. need a
            generalised version that allows constraints to be placed on select.
            (also might need to prove anything in the assums about the actual
            primitives)
        end
    | build_interpretation (upd::ctxt) tys consts =
        let
          val instances_to_constrain =
            union (find_type_instances tys (#tys upd))
                  (find_const_instances consts (#consts upd))
          val instantiated_tys =
            concat (map (fn s => map (type_subst s) (#tys upd)) instances_to_constrain)
          val instantiated_consts =
            concat (map (fn s => map (inst s) (#consts upd)) instances_to_constrain)
          val instantiated_axioms =
            concat (map (fn s => map (INST_TYPE s) (#axs upd)) instances_to_constrain)
          val new_tys =
            (* mk_set? *)concat (map base_types_of_term o concl) instantiated_axioms
          val new_consts =
            concat (map base_terms_of_term o concl) instantiated_axioms
          val ith = build_interpretation ctxt
            (union (set_diff tys instantiated_tys) new_tys)
            (union (set_diff consts instantiated_consts) new_consts)
            (* [Note: It is *not* guaranteed that
                (instantiated_tys SUBSET tys) or the analog for consts;
                this is because we may have been *told* to constrain e.g.
                one of the constants of a certain instance of the update,
                but this means that we need to constrain *all* of the
                constants of that update]
             *)
          val itm = get_int (CONJUNCT1 ith)
          val jth = MATCH_MP update_interpretation_def (CONJ (#sound_update_thm upd) (CONJUNCT1 ith))
          val jtm = get_int jth
          val inner_cs = cs_to_inner (#tys upd) (#consts upd) instances_to_constrain
          val ktm = ``constrain_interpretation ^(upd_to_inner upd) ^inner_cs ^jtm``

            concat (map base_type_assums instantiated_tys)

            concat (map base_term_assums instantiated_consts)
        in
        end

(*
  sound_update ctxt upd ⇔
    ∀i. i models (thyof ctxt) ⇒
      ∃i'. equal_on (sigof ctxt) i i' ∧
           i' models (thyof (upd::ctxt))`
*)

(*******************
  val MID_EXISTS_AND_THM = prove(
    ``(?x. P x /\ Q /\ R x) <=> (Q /\ ?x. P x /\ R x)``,
    metis_tac[])
  val eval = SIMP_CONV (std_ss++LIST_ss)
    [typeof_def,codomain_def,typesem_def,
     term_ok_def,WELLTYPED_CLAUSES,
     type_ok_def,type_11]
   THENC SIMP_CONV std_ss [GSYM CONJ_ASSOC,MID_EXISTS_AND_THM]

  val tyass_eq_sym = PROVE[](``∀x y z. (^tyass x y = z) ⇒ (z = ^tyass x y)``)
  val tyval_eq_sym = PROVE[](``∀x z. (^tyval x = z) ⇒ (z = ^tyval x)``)
in

  val get_simpths = mapfilter (QCHANGED_CONV eval) o hyp
  fun simp_asms th = foldl (uncurry (C simplify_assum)) th (get_simpths th)
  val replace_asms =
    repeat (C replace_assum good_context_instance_equality) o
    repeat (C replace_assum good_context_wf_to_inner_bool_to_inner) o
    repeat (C replace_assum good_context_wf_to_inner_fun_to_inner) o
    repeat (C replace_assum good_context_tyass_bool) o
    repeat (C replace_assum good_context_tyass_fun) o
    repeat (C replace_assum good_context_lookup_bool) o
    repeat (C replace_assum good_context_lookup_fun) o
    repeat (C replace_assum tyass_eq_sym) o
    repeat (C replace_assum tyval_eq_sym) o
    repeat (C replace_assum TRUTH)
  fun changed f th =
      assert (not o curry HOLset.equal (hypset th) o hypset)
             (f th)
  val full_simp_asms = repeat (changed (simp_asms o replace_asms))

  val bool_to_inner_tm = ``bool_to_inner``
  val fun_to_inner_tm = ``fun_to_inner``

  val universe_ty = ``:'U``
  val bool_ty = ``:bool``
  val type_ty = ``:type``
  fun to_inner_tm ty = 
    mk_comb (
      mk_const ("to_inner0", (universe_ty --> universe_ty --> bool_ty)
                         --> type_ty --> ty --> universe_ty),
      mk_var ("mem", universe_ty --> universe_ty --> bool_ty)
    )

  fun mk_to_inner (ty : hol_type) = case type_view ty of
      Tyapp(thy, "bool", [])        => bool_to_inner_tm
    | Tyapp(thy, "fun",  [ty1,ty2]) => mk_binop fun_to_inner_tm (mk_to_inner ty1, mk_to_inner ty2)
    | _                             => mk_monop (to_inner_tm ty) (type_to_deep ty)

  (* Take a HOL type {ty} and return a theorem of the form
   * [^good_context, wf_is_inner in_ty1, ..., wf_is_inner in_tyn] |- wf_is_inner ^(mk_to_inner ty),
   * where ty1,...,tyn are types in ty other than
   * bool and function types.
   *)
  fun mk_wf_is_inner_thm ty = case type_view ty of
      Tyapp ("min","bool",[]) => good_context_wf_to_inner_bool_to_inner
    | Tyapp ("min","fun",[ty1,ty2]) =>
         good_context_wf_to_inner_fun_to_inner
         |> ISPECL [mk_to_inner ty1, mk_to_inner ty2]
         |> C MP (CONJ (mk_wf_is_inner_thm ty1)
                             (mk_wf_is_inner_thm ty2))
    | _ => ASSUME ``wf_to_inner ^(mk_to_inner ty)``

  fun type_to_cert ty = case type_view ty of
      Tyapp ("min","bool",[]) => bool_cert_thm
    | Tyapp ("min","fun",[ty1,ty2]) =>
         fun_cert_thm
         |> C MATCH_MP (type_to_cert ty1)
         |> C MATCH_MP (type_to_cert ty2)
    | Tyapp (_,con,args) =>
         tycon_cert_thm (* TODO: get rid of the MAP somehow *)
         |> INST_TYPE [``:'a`` |-> ty]
	 |> INST [``con:string`` |-> string_to_inner con,
		  ``args:type list`` |-> mk_list (map type_to_deep args, ``:type``)]
    | Tyvar v =>
         tyvar_cert_thm
         |> INST_TYPE [``:'a`` |-> ty]
         |> INST [``v:string`` |-> string_to_inner v]

  fun var_to_cert v =
    let
      val v_deep = term_to_deep (assert is_var v)
      val (x_deep,ty_deep) = dest_Var v_deep
      val l = mk_comb(mk_to_inner (type_of v),v)
      val a = mk_eq(mk_comb(tmval,mk_pair(x_deep,ty_deep)),l)
    in
      MATCH_MP Var_thm (ASSUME a) |> SPEC mem
    end

  val instance_tm = Term.inst[alpha|->U]``instance``
  fun mk_instance name ty =
    list_mk_comb(instance_tm,[tmsig,interpretation,name,ty,tyval])

  fun const_to_cert c =
    let
      val c_deep = term_to_deep (assert is_const c)
      val (name_deep,ty_deep) = dest_Const c_deep
      val l = mk_comb(mk_to_inner (type_of c),c)
      val a = mk_eq(mk_instance name_deep ty_deep,l)
      val th = MATCH_MP Const_thm (ASSUME a) |> SPEC mem
    in
      full_simp_asms th
    end

  fun term_to_cert tm =
    case dest_term tm of
      VAR _ => var_to_cert tm
    | CONST _ => const_to_cert tm
    | COMB(t1,t2) =>
      let
        val c1 = term_to_cert t1
        val c2 = term_to_cert t2
        val (dty,rty) = dom_rng (type_of t1)
      in
        MATCH_MP (Comb_thm) (CONJ c1 c2)
        |> C MATCH_MP (mk_wf_is_inner_thm dty)
        |> C MATCH_MP (mk_wf_is_inner_thm rty)
        |> full_simp_asms
      end
    | LAMB(x,b) =>
      let
        val (xd,tyd) = dest_Var(term_to_deep x)
        val bd = term_to_deep b
        val cx = var_to_cert x
        val cb = term_to_cert b
        val ina = cx |> concl |> lhs |> rator
        val inb = cb |> concl |> lhs |> rator
        val th = Abs_thm |> ISPECL[ina,inb,tm,xd,tyd,bd] |> funpow 2 UNDISCH
        val thd = mk_wf_is_inner_thm (type_of x)
        val thr = mk_wf_is_inner_thm (type_of b)
        val th = MATCH_MP th thd
        val th = MATCH_MP th thr
        val hyps = set_diff (mk_set(hyp cb @ hyp th)) (hyp cx)
        val goal = (hyps, th |> concl |> dest_imp |> fst)
        val th1 = TAC_PROOF(goal,
          gen_tac >> strip_tac >>
          CONV_TAC(LAND_CONV(RAND_CONV(BETA_CONV))) >>
          match_mp_tac (MP_CANON (DISCH_ALL cb)) >>
          ASM_SIMP_TAC (std_ss++LIST_ss++STRING_ss)
            [combinTheory.APPLY_UPDATE_THM] >>
          TRY (
            conj_tac >- (
              match_mp_tac good_context_extend_tmval >>
              PROVE_TAC[])) >>
          TRY (
            match_mp_tac good_context_extend_tmval >>
            PROVE_TAC[]) >>
          match_mp_tac EQ_SYM >>
          match_mp_tac (MP_CANON wf_to_inner_finv_right) >>
          PROVE_TAC[good_context_wf_to_inner_bool_to_inner,
                    good_context_wf_to_inner_fun_to_inner])
        val th2 = MP th th1
      in
        th2 |> UNDISCH |> full_simp_asms
      end

  fun find_equation_thms p acc =
    let
      val (l,r) = dest_eq p
      val acc = find_equation_thms l acc
      val acc = find_equation_thms r acc
      val a = equation_def
            |> SPECL[term_to_deep l, term_to_deep r]
            |> SYM
            |> SIMP_RULE (srw_ss())[]
    in
      a::acc
    end handle HOL_ERR _ => acc

  fun prop_to_loeb_hyp p =
    let
      val cert = term_to_cert p
      val equation_intro_rule = PURE_REWRITE_RULE (find_equation_thms p [])
      val th2 = AP_TERM``finv bool_to_inner`` cert
      val th3 =
        wf_to_inner_finv_left
        |> Q.ISPEC`bool_to_inner`
        |> C MATCH_MP good_context_wf_to_inner_bool_to_inner
        |> (fn th => CONV_RULE (LAND_CONV (REWR_CONV th)) th2)
        |> EQ_IMP_RULE |> snd
      val th4 = MATCH_MP finv_bool_to_inner_True th3
      val inst_sig = Q.INST[`tmsig`|->`tmsof(sigof(thyof ctxt))`,
                            `tysig`|->`tysof(sigof(thyof ctxt))`]
      val th5 = th4 |> inst_sig
      val th = Q.SPEC`thyof ctxt` provable_imp_eq_true
             |> SPECL [interpretation,valuation]
             |> funpow 3 UNDISCH
             |> SPEC (th5 |> concl |> rator |> rand |> lhs |> rand)
      val th6 = MATCH_MP mp_lemma (CONJ th5 th)
              |> equation_intro_rule
              |> C simplify_assum (inst_sig (SPEC_ALL good_context_def))
    in
      simp_asms th6
    end

  (*
  local
    val tyval_asms = filter (can (match_term ``^tyval x = range y``)) o hyp
    val mk_wf_to_inner = mk_monop``wf_to_inner``
    val is_set_theory_mem = ``is_set_theory ^mem``
    val is_type_valuation_tm = ``is_type_valuation``
    val update_list_tm = ``$=++``
    val base_tyval_tm = ``base_tyval``
  in
    fun mk_tyval th =
      let
        val asms = tyval_asms th
        fun mk_kv eq =
          let
            val (l,r) = dest_eq eq
          in
            mk_pair(rand l,r)
          end
        val pairs = map mk_kv asms
        val pairs = mk_list(pairs,mk_prod(string_ty,U))
        val tyval = list_mk_icomb(update_list_tm,[base_tyval_tm,pairs])
        val wf_to_inners = map (mk_wf_to_inner o rand o rand) asms
        val goal = (is_set_theory_mem::wf_to_inners,mk_comb(is_type_valuation_tm,tyval))
        val th = TAC_PROOF(goal,
          match_mp_tac is_type_valuation_update_list >>
          conj_tac >- ACCEPT_TAC base_tyval_def >>
          SIMP_TAC (std_ss ++ LIST_ss) [] >>
          rpt conj_tac >>
          match_mp_tac inhabited_range >>
          first_assum ACCEPT_TAC)
      in
        SIMP_RULE std_ss [UPDATE_LIST_THM] th
      end
  end
  *)

  val tmval_asms = filter (can (match_term ``^tmval x = y``)) o hyp

  local
    val empty_tyset = HOLset.empty Type.compare
    val sing_tyset = HOLset.singleton Type.compare
  in
    fun select_types tm =
      case dest_term tm of
        VAR _ => empty_tyset
      | CONST{Name="@",Thy="min",Ty} => sing_tyset (snd(dom_rng Ty))
      | CONST _ => empty_tyset
      | COMB(t1,t2) =>
        HOLset.union (select_types t1,select_types t2)
      | LAMB(_,b) => select_types b
  end

  fun IINST1 var tm th =
    INST_TY_TERM (match_term var tm) th
*******************)
end end
