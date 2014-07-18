open HolKernel Parse boolLib bossLib lcsymtacs
open reflectionLib
val _ = new_theory"reflectionDemo"

val () = show_assums := true

val p = ``0 = 1``
val res1 = prop_to_loeb_hyp p
val p = ``∀y. (λx. F) z``
val res2 = prop_to_loeb_hyp p
val p = ``(∀y. (λx. F) z) ⇔ ¬z``
val res3 = prop_to_loeb_hyp p
val p = ``(λx. ~x) p ⇒ F``
val res4 = prop_to_loeb_hyp p

open miscLib basicReflectionLib miscTheory listSimps stringSimps
open setSpecTheory holSemanticsTheory reflectionTheory pairSyntax listSyntax stringSyntax
open holBoolTheory holBoolSyntaxTheory holSyntaxExtraTheory

val not_thm = prove(
  ``is_set_theory ^mem ⇒
    (Abstract boolset boolset (λx. Boolean (¬finv in_bool x)) =
     Abstract boolset boolset (λp. Boolean (p ≠ True)))``,
  rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[boolean_in_boolset] >>
  simp[mem_boolset,boolean_def] >>
  imp_res_tac is_in_in_bool >>
  qx_gen_tac`x` >>
  `finv in_bool (in_bool (x = True)) = (x = True)` by
    (match_mp_tac is_in_finv_left >> rw[]) >>
  rw[] >> fs[] >> rfs[in_bool_def,boolean_def])

val in_fun_not =
``in_fun in_bool in_bool $~``
  |> SIMP_CONV std_ss [Once in_bool_def,in_fun_def,UNDISCH range_in_bool,UNDISCH not_thm]

val in_bool_false =
  ``in_bool F``
  |> SIMP_CONV std_ss [in_bool_def,boolean_def]

val range_in_fun_ina_in_bool =
range_in_fun |> GEN_ALL |> SPEC mem
  |> Q.ISPECL[`in_bool`,`ina:'a -> 'U`]
  |> SIMP_RULE std_ss [UNDISCH is_in_in_bool,GSYM AND_IMP_INTRO]
  |> UNDISCH |> UNDISCH

val forall_thm = prove(
  ``is_set_theory ^mem ⇒ is_in ina ⇒
    (Abstract (Funspace (range ina) boolset) boolset
       (λP. Boolean (∀x. x <: range ina ⇒ Holds P x)) =
     Abstract (Funspace (range ina) boolset) boolset
       (λx. in_bool ($! (finv (in_fun ina in_bool) x))))``,
  rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[boolean_in_boolset,in_bool_def] >>
  simp[boolean_def,holds_def] >>
  qx_gen_tac`x` >> strip_tac >>
  qmatch_abbrev_tac`(if z1 then True else False) = if z2 then True else False` >>
  qsuff_tac`z1 = z2`>-rw[]>>
  unabbrev_all_tac >>
  `∃f. (x = in_fun ina Boolean (λa. (f (ina a)) = True)) ∧
       (∀a. f (ina a) <: boolset)` by (
    simp[UNDISCH range_in_bool,in_fun_def,GSYM in_bool_def] >>
    qspecl_then[`x`,`range ina`,`boolset`]mp_tac (UNDISCH in_funspace_abstract) >>
    discharge_hyps  >- metis_tac[inhabited_range,mem_boolset] >> rw[] >>
    qexists_tac`f` >> simp[in_bool_def] >>
    reverse conj_tac >- metis_tac[is_in_range_thm] >>
    match_mp_tac (UNDISCH abstract_eq) >>
    simp[boolean_in_boolset] >> rw[] >>
    simp[boolean_def] >> rw[] >>
    imp_res_tac is_in_finv_right >>
    metis_tac[mem_boolset] ) >>
  Q.ISPEC_THEN`in_fun ina Boolean`mp_tac is_in_finv_left >>
  discharge_hyps >- metis_tac[is_in_in_fun,is_in_in_bool,in_bool_def] >>
  strip_tac >> simp[] >>
  rw[EQ_IMP_THM] >- (
    first_x_assum(qspec_then`ina a`mp_tac) >>
    discharge_hyps >- metis_tac[is_in_range_thm] >>
    simp[in_fun_def] >> strip_tac >>
    pop_assum (SUBST1_TAC o SYM) >>
    match_mp_tac EQ_SYM >>
    match_mp_tac apply_abstract_matchable >>
    simp[is_in_range_thm,GSYM in_bool_def,range_in_bool] >>
    simp[in_bool_def,boolean_in_boolset] >>
    Q.ISPEC_THEN`ina`mp_tac is_in_finv_left >> rw[] >>
    rw[boolean_def] >>
    metis_tac[mem_boolset] ) >>
  rw[in_fun_def] >>
  match_mp_tac apply_abstract_matchable >>
  simp[is_in_range_thm,GSYM in_bool_def,range_in_bool] >>
  simp[in_bool_def,boolean_in_boolset] >>
  rw[boolean_def]) |> UNDISCH |> UNDISCH

val in_fun_forall =
  ``in_fun (in_fun ina in_bool) in_bool $!``
  |> SIMP_CONV std_ss [in_fun_def,UNDISCH range_in_bool,range_in_fun_ina_in_bool,GSYM forall_thm]

val range_in_fun_in_bool_in_bool =
range_in_fun |> GEN_ALL |> SPEC mem
  |> Q.ISPECL[`in_bool`,`in_bool`]
  |> SIMP_RULE std_ss [UNDISCH is_in_in_bool]
  |> UNDISCH

val implies_thm1 = prove(
  ``is_set_theory ^mem ∧ p <: boolset ⇒
    (Abstract boolset boolset (λx. in_bool (finv in_bool p ⇒ finv in_bool x)) =
     Abstract boolset boolset (λq. Boolean ((p = True) ⇒ (q = True))))``,
  rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  rw[boolean_in_boolset] >>
  rw[Once in_bool_def,boolean_in_boolset] >>
  rw[boolean_def] >>
  metis_tac[finv_in_bool_eq_true])

val implies_thm = prove(
  ``is_set_theory ^mem ⇒
    (Abstract boolset (Funspace boolset boolset)
      (λy. Abstract boolset boolset (λx. in_bool (finv in_bool y ⇒ finv in_bool x))) =
     Abstract boolset (Funspace boolset boolset)
      (λp. Abstract boolset boolset (λq. Boolean ((p = True) ⇒ (q = True)))))``,
  rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  rw[implies_thm1] >>
  match_mp_tac (UNDISCH abstract_in_funspace) >>
  rw[boolean_in_boolset])

val in_fun_implies =
  ``in_fun in_bool (in_fun in_bool in_bool) $==>``
  |> SIMP_CONV std_ss [in_fun_def,UNDISCH range_in_bool,range_in_fun_in_bool_in_bool,UNDISCH implies_thm]

val base_tyval_tm = ``base_tyval``

val (update_list_tm,mk_update_list,dest_update_list,is_update_list)
  = syntax_fns "misc" 3 dest_triop mk_triop "UPDATE_LIST"

val is_type_valuation_tm = ``is_type_valuation``
val is_set_theory_mem = ``is_set_theory ^mem``

val mk_is_in = mk_monop``is_in``

val tyval_asms = filter (can (match_term ``^tyval x = range y``)) o hyp

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
    val is_ins = map (mk_is_in o rand o rand) asms
    val goal = (is_set_theory_mem::is_ins,mk_comb(is_type_valuation_tm,tyval))
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

val tmval_asms = filter (can (match_term ``^tmval x = y``)) o hyp

val bool_model_models = UNDISCH (SPEC mem bool_model_def)

val res = res4

val tyval_th = mk_tyval res

val bool_model_interpretations =
is_bool_interpretation_def
|> SPEC mem
|> Q.SPEC`bool_model`
|> SIMP_RULE (std_ss++LIST_ss)
  [bool_model_interpretation,interprets_def,
   SIMP_RULE std_ss [models_def] bool_model_models,
   GSYM IMP_CONJ_THM, GSYM FORALL_AND_THM]
|> SPEC (rand(concl tyval_th))
|> C MATCH_MP tyval_th
|> SIMP_RULE (std_ss++LIST_ss++STRING_ss) [combinTheory.APPLY_UPDATE_THM]

val r3 = res |> INST[tyval|->(rand(concl tyval_th))]
val simpths = mapfilter (QCHANGED_CONV (SIMP_CONV (std_ss++LIST_ss++STRING_ss) [combinTheory.APPLY_UPDATE_THM])) (hyp r3)
val phyps = map EQT_ELIM simpths
val r4 = foldl (uncurry PROVE_HYP) r3 phyps
val r5 = Q.INST[`ctxt`|->`mk_bool_ctxt init_ctxt`] r4
val bool_insts =
  bool_sig_instances
  |> Q.GEN`sig`
  |> Q.SPEC`sigof(mk_bool_ctxt init_ctxt)`
  |> SIMP_RULE std_ss []
val is_bool_sig_goal:goal = ([],fst(dest_imp(concl bool_insts)))
val is_bool_sig_th = TAC_PROOF(is_bool_sig_goal,
  match_mp_tac bool_has_bool_sig >>
  ACCEPT_TAC (MATCH_MP theory_ok_sig init_theory_ok |> SIMP_RULE std_ss []))
val is_std_sig_goal:goal = ([],first (can (match_term ``is_std_sig x``)) (hyp r5))
val is_std_sig_th = TAC_PROOF(is_std_sig_goal,
  match_mp_tac is_bool_sig_std >>
  ACCEPT_TAC is_bool_sig_th)
val r6 = PROVE_HYP is_std_sig_th r5
val bool_insts = MATCH_MP bool_insts is_bool_sig_th
val bool_sig = is_bool_sig_def
  |> Q.SPEC`sigof(mk_bool_ctxt init_ctxt)`
  |> SIMP_RULE std_ss [is_bool_sig_th,is_std_sig_th]
val simpths = mapfilter (QCHANGED_CONV (SIMP_CONV (std_ss++LIST_ss++STRING_ss)
  [combinTheory.APPLY_UPDATE_THM,bool_insts,bool_sig,is_instance_refl])) (hyp r6)
val r7 = foldl (uncurry (C simplify_assum)) r6 simpths |> PROVE_HYP TRUTH
val simpths = mapfilter (QCHANGED_CONV (SIMP_CONV (std_ss) [is_valuation_def,tyval_th])) (hyp r7)
val r8 = foldl (uncurry (C simplify_assum)) r7 simpths
val r9 = Q.INST[`tyass`|->`tyaof bool_model`,`tmass`|->`tmaof bool_model`] r8
val simpths = mapfilter (QCHANGED_CONV (SIMP_CONV (std_ss) [bool_model_models,SIMP_RULE std_ss [models_def] bool_model_models])) (hyp r9)
val r10 = foldl (uncurry (C simplify_assum)) r9 simpths |> PROVE_HYP TRUTH
val simpths = mapfilter (QCHANGED_CONV (SIMP_CONV (std_ss++LIST_ss) [bool_model_interpretations,in_fun_not,in_bool_false,
    in_fun_implies,
    Q.INST[`ina`|->`in_A`]in_fun_forall,
    bool_model_interpretation
    |> SIMP_RULE std_ss [is_bool_interpretation_def]
    |> CONJUNCT1
    |> SIMP_RULE std_ss [is_std_interpretation_def,is_std_type_assignment_def]
    |> CONJUNCT1,
    UNDISCH range_in_bool])) (hyp r10)
val r11 = foldl (uncurry (C simplify_assum)) r10 simpths |> PROVE_HYP TRUTH

val constrained_term_valuation_exists = store_thm("constrained_term_valuation_exists",
  ``is_set_theory ^mem ⇒
    ∀tyenv δ τ.  is_type_valuation τ ⇒ is_type_assignment tyenv δ ⇒
    ∀constraints.
    ALL_DISTINCT (MAP FST constraints) ∧
    EVERY (λ(k,v). type_ok tyenv (SND k) ∧
                   v <: typesem δ τ (SND k)) constraints
    ⇒
    ∃σ.
      is_term_valuation tyenv δ τ σ ∧
      EVERY (λ(k,v). σ k = v) constraints``,
  strip_tac >> ntac 3 gen_tac >> ntac 2 strip_tac >> Induct >> simp[] >-
    metis_tac[holSemanticsExtraTheory.term_valuation_exists,is_valuation_def,pairTheory.FST,pairTheory.SND] >>
  qx_gen_tac`p` >>
  `∃k v. p = (k,v)` by metis_tac[pairTheory.pair_CASES] >>
  rw[] >> fs[] >>
  qexists_tac`(k =+ v) σ` >>
  simp[combinTheory.APPLY_UPDATE_THM] >>
  conj_tac >- (
    fs[is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
    rw[] >> fs[] ) >>
  fs[listTheory.EVERY_MEM] >>
  Cases >> simp[] >>
  fs[listTheory.MEM_MAP,Once pairTheory.FORALL_PROD] >>
  rw[] >> metis_tac[])

val is_term_valuation_asm = first (same_const ``is_term_valuation0`` o fst o strip_comb) (hyp r11)
val t1 = is_term_valuation_asm |> rator |> rator |> rator |> rand
val t2 = is_term_valuation_asm |> rator |> rator |> rand
val t3 = is_term_valuation_asm |> rator |> rand

val asms = tmval_asms r11
val tmval_th1 =
constrained_term_valuation_exists
|> UNDISCH
|> SPECL [t1,t2,t3]
|> SIMP_RULE std_ss [tyval_th]
|> C MATCH_MP (
     bool_model_models |> SIMP_RULE std_ss [models_def] |> CONJUNCT2 |> CONJUNCT1
     |> SIMP_RULE std_ss [is_interpretation_def] |> CONJUNCT1)
|> SPEC (asms |> map (fn eq => mk_pair(rand(lhs eq),rhs eq))
         |> C (curry mk_list) (mk_prod(mk_prod(string_ty,``:type``),U)))

val goal = (hyp tmval_th1,fst(dest_imp(concl tmval_th1)))
val tmval_th2 = TAC_PROOF(goal,
  conj_tac >- EVAL_TAC >>
  simp[holSyntaxTheory.type_ok_def,typesem_def,combinTheory.APPLY_UPDATE_THM] >>
  rpt conj_tac >>
  TRY (EVAL_TAC >> NO_TAC) >>
  TRY (simp[
    bool_model_interpretation
    |> SIMP_RULE std_ss [is_bool_interpretation_def] |> CONJUNCT1
    |> SIMP_RULE std_ss [is_std_interpretation_def] |> CONJUNCT1
    |> SIMP_RULE std_ss [is_std_type_assignment_def]
    |> CONJUNCT2] >>
    metis_tac[is_in_in_bool,is_in_range_thm,range_in_bool]) >>
  metis_tac[is_in_range_thm])
val tmval_th3 = MP tmval_th1 tmval_th2
  |> SIMP_RULE (std_ss++LIST_ss)[]

val r12 =
  foldl (uncurry PROVE_HYP) r11 (CONJUNCTS (ASSUME (mk_conj(is_term_valuation_asm,(list_mk_conj asms)))))
val r13 = CHOOSE (tmval, tmval_th3) r12

val _ = save_thm("example",r13)

val _ = export_theory()
