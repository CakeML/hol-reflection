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

open miscLib basicReflectionLib miscTheory listSimps stringSimps
open setSpecTheory holSemanticsTheory reflectionTheory pairSyntax listSyntax stringSyntax
open holBoolTheory holBoolSyntaxTheory holSyntaxExtraTheory holConsistencyTheory

val init_model_def = new_specification("init_model_def",["init_model0"],
    SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] (GEN_ALL init_ctxt_has_model))
val _ = overload_on("init_model",``init_model0 ^mem``)

val bool_ctxt_no_new_axioms =
  ``(∀p. MEM (NewAxiom p) (mk_bool_ctxt init_ctxt) ⇒
         MEM (NewAxiom p) init_ctxt)``
  |> (EVAL THENC (SIMP_CONV std_ss []))
  |> EQT_ELIM

val bool_model_exists =
  extends_consistent
  |> UNDISCH
  |> Q.SPECL[`init_ctxt`,`mk_bool_ctxt init_ctxt`]
  |> C MATCH_MP bool_extends_init
  |> SPEC ``init_model``
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]
  |> C MATCH_MP init_theory_ok
  |> C MATCH_MP (UNDISCH (SPEC mem init_model_def))
  |> C MATCH_MP bool_ctxt_no_new_axioms
  |> DISCH_ALL |> GEN_ALL
  |> SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM]

val bool_model_def = new_specification("bool_model_def",["bool_model0"],
  bool_model_exists)
val _ = overload_on("bool_model",``bool_model0 ^mem``)
val bool_model_models = UNDISCH (SPEC mem bool_model_def)

val bool_theory_ok =
extends_theory_ok
|> Q.SPECL[`init_ctxt`,`mk_bool_ctxt init_ctxt`]
|> SIMP_RULE std_ss [bool_extends_init,init_theory_ok]

val bool_model_interpretation =
bool_has_bool_interpretation
|> UNDISCH
|> Q.SPEC`init_ctxt`
|> Q.SPEC`bool_model`
|> SIMP_RULE std_ss [bool_model_models,bool_theory_ok]

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

val res = res3
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
|> SIMP_RULE (std_ss++LIST_ss) [combinTheory.APPLY_UPDATE_THM]

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
    Q.INST[`ina`|->`in_A`]in_fun_forall,
    bool_model_interpretation
    |> SIMP_RULE std_ss [is_bool_interpretation_def]
    |> CONJUNCT1
    |> SIMP_RULE std_ss [is_std_interpretation_def,is_std_type_assignment_def]
    |> CONJUNCT1,
    UNDISCH range_in_bool])) (hyp r10)
val r11 = foldl (uncurry (C simplify_assum)) r10 simpths |> PROVE_HYP TRUTH

val _ = save_thm("example",r11)

val _ = export_theory()
