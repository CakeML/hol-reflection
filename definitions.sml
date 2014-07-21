open HolKernel lcsymtacs listSimps miscTheory finite_mapTheory listTheory
open miscLib reflectionLib holSyntaxSyntax 
open holSyntaxExtraTheory holBoolSyntaxTheory holBoolTheory
     holSemanticsTheory
     holAxiomsSyntaxTheory holAxiomsTheory holConsistencyTheory
     reflectionTheory

type context_state = {
  theory_ok_thm : thm,
  is_infinity_sig_thm : thm,
  models_thm : thm,
  signature_lookups : thm list,
  interpretation_lookups : thm list
  }

val theory_ok_hol_ctxt = prove(
  ``theory_ok (thyof hol_ctxt)``,
  match_mp_tac (MP_CANON extends_theory_ok) >>
  match_exists_tac (concl hol_extends_bool) >>
  simp[hol_extends_bool,bool_theory_ok])

val is_infinity_sig_hol_ctxt = prove(
  ``is_infinity_sig (sigof hol_ctxt)``,
  simp[hol_ctxt_def] >>
  match_mp_tac infinity_has_infinity_sig >>
  match_mp_tac select_has_select_sig >>
  match_mp_tac (MP_CANON is_bool_sig_extends) >>
  qexists_tac`mk_bool_ctxt init_ctxt` >>
  conj_asm2_tac >- (
    match_mp_tac eta_extends >>
    fs[is_bool_sig_def] ) >>
  match_mp_tac bool_has_bool_sig >>
  ACCEPT_TAC (MATCH_MP theory_ok_sig init_theory_ok |> SIMP_RULE std_ss[]))

val interpretations1 = bool_interpretations hol_bool_interpretation
val equality_thm0 = CONJUNCT1 (funpow 0 CONJUNCT2 interpretations1)
val truth_thm0    = CONJUNCT1 (funpow 1 CONJUNCT2 interpretations1)
val and_thm0      = CONJUNCT1 (funpow 2 CONJUNCT2 interpretations1)
val implies_thm0  = CONJUNCT1 (funpow 3 CONJUNCT2 interpretations1)
val forall_thm0   = CONJUNCT1 (funpow 4 CONJUNCT2 interpretations1)
val exists_thm0   = CONJUNCT1 (funpow 5 CONJUNCT2 interpretations1)
val or_thm0       = CONJUNCT1 (funpow 6 CONJUNCT2 interpretations1)
val falsity_thm0  = CONJUNCT1 (funpow 7 CONJUNCT2 interpretations1)
val not_thm0      =           (funpow 8 CONJUNCT2 interpretations1)

val equality_thm =
  equality_thm0 |> Q.SPEC`range ina`
  |> C MATCH_MP (UNDISCH (Q.SPEC`ina` inhabited_range))
  |> CONV_RULE (RAND_CONV (REWR_CONV (SYM in_fun_equals)))
val truth_thm =
  truth_thm0 |> CONV_RULE(RAND_CONV(REWR_CONV(SYM in_bool_true)))
val and_thm =
  and_thm0 |> CONV_RULE(RAND_CONV(REWR_CONV(SYM in_fun_binop)))
val implies_thm =
  implies_thm0 |> CONV_RULE(RAND_CONV(REWR_CONV(SYM in_fun_binop)))
val forall_thm =
  forall_thm0|> Q.SPEC`range ina`
  |> C MATCH_MP (UNDISCH (Q.SPEC`ina` inhabited_range))
  |> CONV_RULE (RAND_CONV (REWR_CONV (SYM in_fun_forall)))
val exists_thm =
  exists_thm0|> Q.SPEC`range ina`
  |> C MATCH_MP (UNDISCH (Q.SPEC`ina` inhabited_range))
  |> CONV_RULE (RAND_CONV (REWR_CONV (SYM in_fun_exists)))
val or_thm =
  or_thm0 |> CONV_RULE(RAND_CONV(REWR_CONV(SYM in_fun_binop)))
val falsity_thm =
  falsity_thm0 |> CONV_RULE(RAND_CONV(REWR_CONV(SYM in_bool_false)))
val not_thm =
  not_thm0 |> CONV_RULE(RAND_CONV(REWR_CONV(SYM in_fun_not)))

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

val ind_thm =
  hol_model_is_interpretation |> SIMP_RULE std_ss [is_interpretation_def]
  |> CONJUNCT1 |> SIMP_RULE std_ss [is_type_assignment_def]
  |> CONV_RULE (RAND_CONV EVAL)
  |> SIMP_RULE std_ss [FEVERY_ALL_FLOOKUP,FLOOKUP_UPDATE]
  |> Q.SPEC`"ind"` |> SIMP_RULE (std_ss++LIST_ss) [LENGTH_NIL]

val initial_context_state = {
  theory_ok_thm = theory_ok_hol_ctxt,
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

val exists_equal_thm = prove(
  ``$? ($= x) ⇔ T``,
  `$= x = λz. x = z` by ( simp[FUN_EQ_THM] ) >>
  pop_assum SUBST1_TAC >> simp[])
val exists_REV_ASSOCD_thm = prove(
  ``∃i. ty = REV_ASSOCD (Tyvar a) i (Tyvar a)``,
  qexists_tac`[ty,Tyvar a]` >>
  EVAL_TAC )

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

val IND_SUC_def = definition"IND_SUC_def"
val name = "IND_SUC"
val tm = term_to_deep(rhs(concl IND_SUC_def))
val theory_ok_th = theory_ok_hol_ctxt

val tm_def = IND_SUC_def

(term_to_cert``ARB``)
hol_ctxt_def
show_assums := true

fun mk_ConstDef_th theory_ok_th tm_def =
  let
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

  in
  end

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

