structure reflectionLib = struct
local
  open HolKernel boolLib bossLib lcsymtacs listSimps stringSimps
  open miscLib pairSyntax stringSyntax listSyntax holSyntaxSyntax
  open reflectionTheory pred_setTheory setSpecTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory
  open basicReflectionLib

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
    repeat (C replace_assum good_context_is_in_in_fun) o
    repeat (C replace_assum good_context_instance_equality) o
    repeat (C replace_assum good_context_is_in_in_bool) o
    repeat (C replace_assum good_context_lookup_bool) o
    repeat (C replace_assum good_context_lookup_fun) o
    repeat (C replace_assum tyass_eq_sym) o
    repeat (C replace_assum tyval_eq_sym) o
    repeat (C replace_assum TRUTH)
  fun changed f th =
      assert (not o curry HOLset.equal (hypset th) o hypset)
             (f th)
  val full_simp_asms = repeat (changed (simp_asms o replace_asms))

  val in_bool_tm = ``in_bool``
  val in_fun_tm = ``in_fun``

  fun mk_in (ty : hol_type) = case type_view ty of
      Tyapp(thy, "bool", [])        => in_bool_tm
    | Tyapp(thy, "fun",  [ty1,ty2]) => mk_binop in_fun_tm (mk_in ty1, mk_in ty2)
    | _                             => mk_in_var ty

  fun mk_is_in_thm ty = case type_view ty of
      Tyapp ("min","bool",[]) => good_context_is_in_in_bool
    | Tyapp ("min","fun",[ty1,ty2]) =>
         good_context_is_in_in_fun
         |> ISPEC (mk_in ty1)
         |> ISPEC (mk_in ty2)
         |> C MATCH_MP (CONJ (mk_is_in_thm ty1)
                             (mk_is_in_thm ty2))
    | _ => ASSUME ``is_in ^(mk_in ty)``

  fun var_to_cert v =
    let
      val v_deep = term_to_deep (assert is_var v)
      val (x_deep,ty_deep) = dest_Var v_deep
      val l = mk_comb(mk_in (type_of v),v)
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
      val l = mk_comb(mk_in (type_of c),c)
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
        |> C MATCH_MP (mk_is_in_thm dty)
        |> C MATCH_MP (mk_is_in_thm rty)
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
        val thd = mk_is_in_thm (type_of x)
        val thr = mk_is_in_thm (type_of b)
        val th = MATCH_MP th thd
        val th = MATCH_MP th thr
        val goal = (mk_set(hyp cb @ hyp th), th |> concl |> dest_imp |> fst)
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
          match_mp_tac (MP_CANON is_in_finv_right) >>
          PROVE_TAC[good_context_is_in_in_bool,good_context_is_in_in_fun])
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
      val th2 = AP_TERM``finv in_bool`` cert
      val th3 =
        is_in_finv_left
        |> Q.ISPEC`in_bool`
        |> C MATCH_MP good_context_is_in_in_bool
        |> (fn th => CONV_RULE (LAND_CONV (REWR_CONV th)) th2)
        |> EQ_IMP_RULE |> snd
      val th4 = MATCH_MP finv_in_bool_True th3
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

end end
