structure reflectionLib = struct
local
  open HolKernel boolLib bossLib lcsymtacs listSimps stringSimps
  open miscLib miscTheory combinTheory pred_setTheory numSyntax pairSyntax stringSyntax listSyntax holSyntaxSyntax
  open setSpecTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory
  open holBoolTheory
  open reflectionTheory basicReflectionLib

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
    | BaseType _       => [ty]
    | FunType(ty1,ty2) => base_types_of_type ty1 @ base_types_of_type ty2

  fun base_type_assums (ty : hol_type) : term list = case base_type_view ty of
      Tyapp(thy, name, args) => [``FLOOKUP tysig ^(fromMLstring name) = 
                                     SOME ^(term_of_int (length args))``,
                                 ``tyass ^(fromMLstring name) (map mk_range args) = 
                                     ^(mk_range ty)``]
    | Tyvar name             => [``tyval ^(fromMLstring name) = ^(mk_range ty)``]


  val type_assums : hol_type -> term list =
    flatten o map (fn ty => to_inner_prop ty :: base_type_assums ty) o base_types_of_type

  fun typesem_prop (ty : hol_type) : term =
    ``typesem tyass tyval ^(type_to_deep ty) = ^(mk_range ty)``

  (* TODO: typesem_cert *)


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
      VAR (name,ty)       => [``tmval (^(fromMLstring name), ^(type_to_deep ty)) = 
                                  ^(mk_to_inner ty) ^tm``]
    | CONST {Thy,Name,Ty} => [``FLOOKUP tmsig ^(fromMLstring Name) = 
                                  SOME ^(type_to_deep Ty)``,
                              ``tmass ^(fromMLstring Name) 
                                      ^(mk_list (map mk_range 
                                                   (const_tyargs Thy Name Ty),
                                                 ``:'U``)) =
                                  ^(mk_to_inner Ty) ^tm``]

  (* TODO: Remove duplicates here and elsewhere. *)
  fun term_assums (tm : term) : term list =
    flatten (map base_type_assums (base_types_of_term tm)) @
    flatten (map base_term_assums (base_terms_of_term tm))


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
	 |> INST [``con:string`` |-> fromMLstring con,
		  ``args:type list`` |-> mk_list (map type_to_deep args, ``:type``)]
    | Tyvar v => 
         tyvar_cert_thm
         |> INST_TYPE [``:'a`` |-> ty]
         |> INST [``v:string`` |-> fromMLstring v]

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
