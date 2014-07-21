open HolKernel lcsymtacs listSimps miscTheory finite_mapTheory listTheory combinTheory
open miscLib basicReflectionLib reflectionLib holSyntaxSyntax
open holSyntaxTheory holSyntaxExtraTheory holBoolSyntaxTheory holBoolTheory
     setSpecTheory holSemanticsTheory holSemanticsExtraTheory
     holAxiomsSyntaxTheory holAxiomsTheory holConsistencyTheory
     reflectionTheory

type context_state = {
  theory_ok_thm : thm,
  is_infinity_sig_thm : thm,
  models_thm : thm,
  signature_lookups : thm list,
  interpretation_lookups : thm list
  }

(* can't do this in general?
val select_thm = prove(
  ``is_set_theory ^mem ⇒ is_in in_ind ⇒ is_in ina ⇒ good_select select ⇒
    (tmaof (hol_model select in_ind) "@" [range ina] =
     in_fun (in_fun ina in_bool) ina $@)``,
  rw[] >>
  rw[UNDISCH in_fun_select] >>
  qspec_then`select`(assume_tac o funpow 2 CONJUNCT2 o UNDISCH)select_model_models >>
  mp_tac (CONJUNCT2 hol_model_models) >>
  simp[subinterpretation_def] >>
  disch_then(qspec_then`"@"`mp_tac o CONJUNCT2) >>
  CONV_TAC(LAND_CONV(QUANT_CONV(LAND_CONV EVAL))) >>
  simp[PULL_EXISTS,type_ok_def,FLOOKUP_UPDATE] >>
  disch_then(qspec_then`[]`mp_tac) >>
  simp[REV_ASSOCD,type_ok_def] >> disch_then kall_tac >>
  fs[good_select_def] >>
  assume_tac (UNDISCH is_in_in_bool) >>
  CONV_TAC(DEPTH_CONV range_in_fun_conv) >>
  simp[range_in_bool] >>
  match_mp_tac(UNDISCH abstract_eq) >>
  rw[] >- metis_tac[is_in_range_thm]
       >- metis_tac[is_in_range_thm] >>
  first_x_assum(qspecl_then[`range ina`,`Holds x`]mp_tac) >>

  MATCH_MP select_sig_instances
  (is_infinity_sig_hol_ctxt |> SIMP_RULE std_ss [is_infinity_sig_def] |> CONJUNCT1)
  print_find"hol_mod"
  is_select_int
*)

val hol_model_is_interpretation =
  hol_model_models |> SIMP_RULE std_ss [models_def] |> CONJUNCT1 |> CONJUNCT1
val hol_model_is_std = hol_model_models |> SIMP_RULE std_ss [models_def]
  |> CONJUNCT1 |> CONJUNCT2 |> CONJUNCT1
val fun_thm =
  hol_model_is_std |> SIMP_RULE std_ss [is_std_interpretation_def]
  |> CONJUNCT1 |> SIMP_RULE std_ss [is_std_type_assignment_def]
  |> CONJUNCT1 |> SIMP_RULE std_ss [FUN_EQ_THM]
  |> Q.SPEC`[range ina; range inb]`
  |> SIMP_RULE (std_ss++LIST_ss) []
  |> CONV_RULE(RAND_CONV(REWR_CONV(
                           range_in_fun |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
                           |> funpow 3 UNDISCH |> SYM)))
val bool_thm =
  hol_model_is_std |> SIMP_RULE std_ss [is_std_interpretation_def]
  |> CONJUNCT1 |> SIMP_RULE std_ss [is_std_type_assignment_def]
  |> CONJUNCT2 |> SIMP_RULE std_ss [FUN_EQ_THM]
  |> Q.SPEC`[]`
  |> SIMP_RULE (std_ss++LIST_ss) [SYM(UNDISCH range_in_bool)]

val ind_thm = hol_model_models |> funpow 2 CONJUNCT2

val onto_rhs =
  mk_infinity_ctxt_def |> SPEC_ALL |> concl |> rhs
  |> rand |> rand |> rator |> funpow 3 rand
val one_one_rhs =
  mk_infinity_ctxt_def |> SPEC_ALL |> concl |> rhs
  |> funpow 2 rand |> rand |> rator |> funpow 3 rand

val mem = ``mem:'U->'U->bool``

val _ = show_assums := true

val tac1 =
  discharge_hyps_keep >- EVAL_TAC >>
  simp[satisfies_def] >>
  `is_type_valuation (base_tyval =++ [("A",range ina);("B",range inb)])` by (
    match_mp_tac is_type_valuation_update_list >>
    simp[base_tyval_def] >>
    metis_tac[inhabited_range] ) >>
  first_assum (fn th =>
    (constrained_term_valuation_exists
     |> UNDISCH
     |> C MATCH_MP th
     |> mp_tac)) >>
  fs[is_interpretation_def] >>
  first_assum(fn th => disch_then (mp_tac o C MATCH_MP th)) >>
  disch_then(qspec_then`[]`mp_tac) >>
  discharge_hyps >- EVAL_TAC >> strip_tac >>
  qmatch_assum_abbrev_tac`is_type_valuation τ` >>
  disch_then(qspec_then`(τ,σ)`mp_tac) >>
  discharge_hyps_keep >- simp[is_valuation_def] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`termsem tmsig i v (s === t) = True` >>
  qspecl_then[`sigof hol_ctxt`,`i`,`v`,`s`,`t`]mp_tac (UNDISCH termsem_equation) >>
  simp[Abbr`tmsig`] >>
  discharge_hyps >- (
    simp[is_structure_def,is_interpretation_def,Abbr`v`] >>
    conj_asm1_tac >- (
      ACCEPT_TAC (MATCH_MP theory_ok_sig hol_theory_ok |> SIMP_RULE std_ss[])) >>
    fs[theory_ok_def] ) >>
  disch_then(mp_tac o SYM) >>
  simp[boolean_eq_true,Abbr`s`] >>
  simp[termsem_def] >>
  strip_tac >> fs[Abbr`v`] >>
  qmatch_assum_abbrev_tac`instance tmsig i name ty τ = z` >>
  `FLOOKUP tmsig name = SOME ty` by (
    unabbrev_all_tac >> EVAL_TAC ) >>
  qspecl_then[`tmsig`,`i`,`name`]mp_tac instance_def >>
  simp[] >>
  disch_then(qspec_then`[]`mp_tac) >>
  rator_x_assum`instance`mp_tac >>
  match_mp_tac SWAP_IMP >>
  simp[] >> disch_then kall_tac >>
  simp[Abbr`ty`] >> EVAL_STRING_SORT >>
  simp[typesem_def] >>
  `is_std_type_assignment (tyaof i)` by fs[is_std_interpretation_def] >>
  `(τ "A" = range ina) ∧ (τ "B" = range inb)` by (
    simp[Abbr`τ`,UPDATE_LIST_THM,APPLY_UPDATE_THM] )>>
  simp[] >> disch_then kall_tac

val cert = term_to_cert (rhs(concl ONE_ONE_DEF))

val hol_interprets_one_one = prove(``
  is_set_theory ^mem ⇒
  good_select select ⇒
  is_in in_ind ⇒
  is_in ina ⇒ is_in inb ⇒
   (tmaof (hol_model select in_ind) "ONE_ONE" [range ina; range inb] =
    Abstract (range (in_fun ina inb)) (range in_bool)
         (λf. in_bool (ONE_ONE (finv (in_fun ina inb) f))))``,
  rw[] >>
  assume_tac (CONJUNCT1 hol_model_models) >>
  fs[models_def] >>
  assume_tac hol_theory_ok >>
  first_x_assum(qspec_then`Const "ONE_ONE" (typeof ^one_one_rhs) === ^one_one_rhs`mp_tac) >>
  tac1 >>
  qspecl_then[`mem`,`inb`,`ina`,`tmsig`,`tyaof i`,`tmaof i`,`τ`,`σ`,`tysof hol_ctxt`]mp_tac(
    Q.GENL[`tysig`,`tmval`,`tyval`,`tmass`,`tyass`,`tmsig`,`in_A`,`in_B`,`mem`]
      (DISCH_ALL cert)) >>
  simp[AND_IMP_INTRO] >>
  discharge_hyps >- (
    simp[good_context_def,Abbr`tmsig`,Abbr`i`,is_interpretation_def,GSYM CONJ_ASSOC] >>
    conj_tac >- ACCEPT_TAC (MATCH_MP theory_ok_sig hol_theory_ok |> SIMP_RULE std_ss[]) >>
    simp[SIMP_RULE std_ss [] (MATCH_MP bool_sig_instances hol_is_bool_sig)] >>
    simp[SIMP_RULE std_ss [] (MATCH_MP std_sig_instances (MATCH_MP is_bool_sig_std hol_is_bool_sig)),typesem_def] >>
    simp[implies_thm,forall_thm] >>
    conj_tac >- (ACCEPT_TAC (IINST1 ``ina:'a->'U`` ``inb:'b->'U`` equality_thm)) >>
    EVAL_TAC >> simp[] >>
    simp[exists_REV_ASSOCD_thm] ) >>
  Q.PAT_ABBREV_TAC`t' = Abs "f" X Y` >>
  `t' = t` by (
    unabbrev_all_tac >>
    simp[equation_def] ) >>
  pop_assum SUBST1_TAC >>
  simp[in_fun_def] >>
  disch_then(SUBST1_TAC o SYM) >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[in_bool_def,range_in_bool,boolean_in_boolset] >>
  rw[ONE_ONE_DEF]) |> funpow 5 UNDISCH

val cert = term_to_cert (rhs(concl ONTO_DEF))

val hol_interprets_onto = prove(``
  is_set_theory ^mem ⇒
  good_select select ⇒
  is_in in_ind ⇒
  is_in ina ⇒ is_in inb ⇒
     (tmaof (hol_model select in_ind) "ONTO" [range ina; range inb] =
      Abstract (range (in_fun ina inb)) (range in_bool)
          (λf. in_bool (ONTO (finv (in_fun ina inb) f))))``,
  rw[] >>
  assume_tac (CONJUNCT1 hol_model_models) >>
  fs[models_def] >>
  assume_tac hol_theory_ok >>
  first_x_assum(qspec_then`Const "ONTO" (typeof ^onto_rhs) === ^onto_rhs`mp_tac) >>
  tac1 >>
  qspecl_then[`mem`,`inb`,`ina`,`tmsig`,`tyaof i`,`tmaof i`,`τ`,`σ`,`tysof hol_ctxt`]mp_tac(
    Q.GENL[`tysig`,`tmval`,`tyval`,`tmass`,`tyass`,`tmsig`,`in_A`,`in_B`,`mem`]
      (DISCH_ALL cert)) >>
  simp[AND_IMP_INTRO] >>
  discharge_hyps >- (
    simp[good_context_def,Abbr`tmsig`,Abbr`i`,is_interpretation_def,GSYM CONJ_ASSOC] >>
    conj_tac >- ACCEPT_TAC (MATCH_MP theory_ok_sig hol_theory_ok |> SIMP_RULE std_ss[]) >>
    simp[SIMP_RULE std_ss [] (MATCH_MP bool_sig_quant_instances hol_is_bool_sig)] >>
    simp[SIMP_RULE std_ss [] (MATCH_MP std_sig_instances (MATCH_MP is_bool_sig_std hol_is_bool_sig)),typesem_def] >>
    simp[implies_thm,forall_thm,exists_thm] >>
    conj_tac >- (ACCEPT_TAC (IINST1 ``ina:'a->'U`` ``inb:'b->'U`` equality_thm)) >>
    conj_tac >- (ACCEPT_TAC (IINST1 ``ina:'a->'U`` ``inb:'b->'U`` forall_thm)) >>
    EVAL_TAC >> simp[] >>
    simp[exists_REV_ASSOCD_thm] ) >>
  Q.PAT_ABBREV_TAC`t' = Abs "f" X Y` >>
  `t' = t` by (
    unabbrev_all_tac >>
    simp[equation_def] ) >>
  pop_assum SUBST1_TAC >>
  simp[in_fun_def] >>
  disch_then(SUBST1_TAC o SYM) >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[in_bool_def,range_in_bool,boolean_in_boolset] >>
  rw[ONTO_DEF]) |> funpow 5 UNDISCH

val initial_context_state = {
  theory_ok_thm = hol_theory_ok,
  is_infinity_sig_thm = is_infinity_sig_hol_ctxt,
  models_thm = CONJ (CONJUNCT1 hol_model_models)
                    (Q.ISPECL[`hol_ctxt`,`hol_model select in_ind`]subinterpretation_refl),
  signature_lookups =
  [``FLOOKUP (tysof hol_ctxt) "fun"``     |> EVAL
  ,``FLOOKUP (tysof hol_ctxt) "bool"``    |> EVAL
  ,``FLOOKUP (tmsof hol_ctxt) "="``       |> EVAL
  ,``FLOOKUP (tmsof hol_ctxt) "T"``       |> EVAL
  ,``FLOOKUP (tmsof hol_ctxt) "/\\"``     |> EVAL
  ,``FLOOKUP (tmsof hol_ctxt) "==>"``     |> EVAL
  ,``FLOOKUP (tmsof hol_ctxt) "!"``       |> EVAL
  ,``FLOOKUP (tmsof hol_ctxt) "?"``       |> EVAL
  ,``FLOOKUP (tmsof hol_ctxt) "\\/"``     |> EVAL
  ,``FLOOKUP (tmsof hol_ctxt) "F"``       |> EVAL
  ,``FLOOKUP (tmsof hol_ctxt) "~"``       |> EVAL
  ,``FLOOKUP (tmsof hol_ctxt) "@"``       |> EVAL
  ,``FLOOKUP (tysof hol_ctxt) "ind"``     |> EVAL
  ,``FLOOKUP (tmsof hol_ctxt) "ONE_ONE"`` |> EVAL
  ,``FLOOKUP (tmsof hol_ctxt) "ONTO"``    |> EVAL
  ],
  interpretation_lookups =
  [fun_thm
  ,bool_thm
  ,equality_thm
  ,truth_thm
  ,and_thm
  ,implies_thm
  ,forall_thm
  ,exists_thm
  ,or_thm
  ,falsity_thm
  ,not_thm
  ,ind_thm
  ,hol_interprets_one_one
  ,hol_interprets_onto
  ]}

val the_context_state = ref initial_context_state

want a database with:
  theory_ok (thyof current_ctxt)
  is_std_sig (sigof current_ctxt)
  current_interpretation models (thyof current_ctxt)
  for each constant in current_ctxt:
    lookup constant (sigof current_ctxt) = ...
    lookup constant current_interpretation = ... (connect to outer) ...
  the current_interpretation will include select_fun as a variable

open basicReflectionLib stringLib holSyntaxTheory alistTheory optionLib listSyntax relationTheory

val cs = list_compset()
val () = pairLib.add_pair_compset cs
val () = stringLib.add_string_compset cs
val () = optionLib.OPTION_rws cs
val () = computeLib.add_thms[
   CONJUNCT1 ALOOKUP_EQ_FLOOKUP,
   ALOOKUP_def] cs
val () = computeLib.add_thms
  [term_ok_def,type_ok_def,
   WELLTYPED_CLAUSES,typeof_def,
   CLOSED_def,VFREE_IN_def,
   codomain_def,
   consts_of_upd_def, types_of_upd_def, equation_def,
   hol_ctxt_def,mk_infinity_ctxt_def,mk_select_ctxt_def,
   mk_eta_ctxt_def,mk_bool_ctxt_def,init_ctxt_def] cs
val () = computeLib.add_datatype_info cs (valOf(TypeBase.fetch``:type``))
val () = computeLib.add_datatype_info cs (valOf(TypeBase.fetch``:term``))

val exists_equal_thm = prove(
  ``$? ($= x) ⇔ T``,
  `$= x = λz. x = z` by ( simp[FUN_EQ_THM] ) >>
  pop_assum SUBST1_TAC >> simp[])

val tm_def = new_definition("IND_SUC_DEF",``IND_SUC = @(x:ind). x ≠ x``)

fun mk_ConstDef_th theory_ok_th tm_def =
  let
    val old_state = !the_context_state
    val theory_ok_th = #theory_ok_thm old_state
    val name = tm_def |> concl |> lhs |> dest_const |> fst
    val tm = tm_def |> concl |> rhs |> term_to_deep
    val ctxt = theory_ok_th |> concl |> funpow 5 rand
    val updates_th = ConstDef_updates
      |> SPECL [fromMLstring name,tm,ctxt]
    val goal:goal = ([],fst(dest_imp(concl updates_th)))
    val goal_th = TAC_PROOF(goal,
      conj_tac >- ACCEPT_TAC theory_ok_th >>
      conj_tac >- (
        CONV_TAC (computeLib.CBV_CONV cs) >>
        simp[exists_equal_thm,exists_REV_ASSOCD_thm] ) >>
      conj_tac >- EVAL_TAC >>
      conj_tac >- (
        CONV_TAC (computeLib.CBV_CONV cs) >>
        simp[] >> rw[] >>
        rpt(
          Q.PAT_ABBREV_TAC`eq = ((A:string) = B)` >>
          Cases_on`eq`>>fs[markerTheory.Abbrev_def]>>
          rw[]) ) >>
      EVAL_TAC >> simp[])
    val updates_th = MP updates_th goal_th
    val new_ctxt = mk_cons(rand(rator (concl updates_th)),rand(concl updates_th))
    val (new_ctxt_extends_goal:goal) = ([],list_mk_comb(``$extends``,[new_ctxt,ctxt]))
    val new_ctxt_extends = TAC_PROOF(new_ctxt_extends_goal,
      ONCE_REWRITE_TAC[extends_def] >>
      MATCH_MP_TAC RTC_SUBSET >>
      CONV_TAC (RATOR_CONV BETA_CONV) >>
      CONV_TAC BETA_CONV >>
      PROVE_TAC[updates_th] )
    val new_theory_ok =
      MATCH_MP (MATCH_MP extends_theory_ok new_ctxt_extends) theory_ok_th
    val infinity_sig_th = #is_infinity_sig_thm old_state
    (* is_infinity_sig_extends *)
    print_find"new_definition_correct"
    new_specification_correct
    consistent_update_def
    val models_th = #models_thm old_state
    val int_lookups = #interpretation_lookups old_state
    term_to_cert (rhs(concl tm_def))

new_type_definition_correct
  is_infinity_sig_thm : thm,
  models_thm : thm,
  signature_lookups : thm list,
  interpretation_lookups : thm list

  in
  end

val IND_SUC_def = definition"IND_SUC_def"
val name = "IND_SUC"
val tm = term_to_deep(rhs(concl IND_SUC_def))
val theory_ok_th = theory_ok_hol_ctxt

val tm_def = IND_SUC_def

mk_ConstDef_th theory_ok_hol_ctxt IND_SUC_def

mk_ConstDef_th theory_ok_hol_ctxt "IND_SUC" (term_to_deep(rhs(concl IND_SUC_def)))
IND_SUC_def
!the_record

print_find"ConstDef"

val witness_thm =
  ``(thyof (mk_select_ctxt (mk_bool_ctxt init_ctxt)),[]) |-
    Comb

fun mk_TypeDefn_th witness_thm name abs rep =
  let
    val (pred,witness) = dest_Comb(rand(concl witness_thm))

    val ctxt =
``TypeDefn name 
``(thyof ctxt,[]) |- Comb pred witness``
``(TypeDefn name pred abs rep) updates ctxt``
fun mk_TypeDefn 
el 5 (CONJUNCTS updates_rules)

