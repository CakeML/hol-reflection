open HolKernel Parse boolLib bossLib lcsymtacs
open reflectionLib
val _ = new_theory"reflectionDemo"

val () = show_assums := true

val p = ``0 = 1``
val res1 = prop_to_loeb_hyp p
val p = ``∀y. (λx. F) z``
val res2 = prop_to_loeb_hyp p
val p = ``(∀y. (λx. F) z) ⇔ (¬z ∨ T)``
val res3 = prop_to_loeb_hyp p
val p = ``∀p. (λx. ~(x=x)) p ⇒ ∃x. F``
val res4 = prop_to_loeb_hyp p
val p = ``@x. x ∧ x``
val res5 = prop_to_loeb_hyp p
val p = ``∀(x:ind). F``
val res6 = prop_to_loeb_hyp p

open miscLib basicReflectionLib listSimps stringSimps
open setSpecTheory holSemanticsTheory reflectionTheory pairSyntax listSyntax stringSyntax
open holBoolTheory holBoolSyntaxTheory holSyntaxExtraTheory

val tmval_asms = filter (can (match_term ``^tmval x = y``)) o hyp

val bool_model_models = UNDISCH (SPEC mem bool_model_def)

val bool_insts =
  bool_sig_instances
  |> Q.GEN`sig`
  |> Q.SPEC`sigof(mk_bool_ctxt init_ctxt)`
  |> SIMP_RULE std_ss []
val is_bool_sig_goal:goal = ([],fst(dest_imp(concl bool_insts)))
val is_bool_sig_th = TAC_PROOF(is_bool_sig_goal,
  match_mp_tac bool_has_bool_sig >>
  ACCEPT_TAC (MATCH_MP theory_ok_sig init_theory_ok |> SIMP_RULE std_ss []))
val bool_insts = MATCH_MP bool_insts is_bool_sig_th
val in_fun_forall = in_fun_forall |> DISCH``is_in ina`` |> Q.GEN`ina`
val in_fun_exists = in_fun_exists |> DISCH``is_in ina`` |> Q.GEN`ina`

val res = res4

val tyval_th = mk_tyval res
val bool_model_interpretations = bool_interpretations bool_model_interpretation tyval_th
val r3 = res |> INST[tyval|->(rand(concl tyval_th))]
val simpths = mapfilter (QCHANGED_CONV (SIMP_CONV (std_ss++LIST_ss++STRING_ss) [combinTheory.APPLY_UPDATE_THM])) (hyp r3)
val r4 = foldl (uncurry PROVE_HYP) r3 (map EQT_ELIM simpths)
val r5 = Q.INST[`ctxt`|->`mk_bool_ctxt init_ctxt`] r4
val is_std_sig_goal:goal = ([],first (can (match_term ``is_std_sig x``)) (hyp r5))
val is_std_sig_th = TAC_PROOF(is_std_sig_goal,
  match_mp_tac is_bool_sig_std >>
  ACCEPT_TAC is_bool_sig_th)
val r6 = PROVE_HYP is_std_sig_th r5
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
val forall_insts = filter (can (match_term ``X = in_fun Y in_bool $!``)) (hyp r10)
val exists_insts = filter (can (match_term ``X = in_fun Y in_bool $?``)) (hyp r10)
val forall_insts = map (rand o rator o rand o rator o rator o rhs) forall_insts
val exists_insts = map (rand o rator o rand o rator o rator o rhs) exists_insts
val simpths = mapfilter (QCHANGED_CONV (SIMP_CONV (std_ss++LIST_ss) [bool_model_interpretations,
    in_bool_true,in_bool_false,in_fun_not,in_fun_binop,
    LIST_CONJ (map (fn ina => ISPEC ina in_fun_forall |> UNDISCH) forall_insts),
    LIST_CONJ (map (fn ina => ISPEC ina in_fun_exists |> UNDISCH) exists_insts),
    bool_model_interpretation
    |> SIMP_RULE std_ss [is_bool_interpretation_def]
    |> CONJUNCT1
    |> SIMP_RULE std_ss [is_std_interpretation_def,is_std_type_assignment_def]
    |> CONJUNCT1,
    UNDISCH range_in_bool])) (hyp r10)
val r11 = foldl (uncurry (C simplify_assum)) r10 simpths |> PROVE_HYP TRUTH
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
