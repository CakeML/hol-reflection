open HolKernel boolLib bossLib lcsymtacs miscLib
open combinTheory pairTheory listTheory alistTheory pred_setTheory miscTheory
open lcaTheory reflectionTheory reflectionLib
open holSyntaxTheory holSyntaxExtraTheory holSyntaxLib
open holSemanticsTheory holSemanticsExtraTheory
open lcaCtxtTheory

val _ = new_theory"lcaProof"

val _ = Globals.max_print_depth := 15

open holSyntaxLibTheory holBoolSyntaxTheory holBoolTheory setSpecTheory

(* TODO: move *)
val abstract_in_funspace_matchable = prove(
  ``is_set_theory ^mem ⇒
    ∀f s t fs. (∀x. x <: s ⇒ f x <: t) ∧ fs = Funspace s t ⇒ Abstract s t f <: fs``,
  PROVE_TAC[abstract_in_funspace])

val termsem_exists = store_thm("termsem_exists",
  ``is_set_theory ^mem ⇒
    ∀s i v f y b.
    is_valuation (tysof s) (tyaof i) v ∧
    is_interpretation s i ∧
    is_std_interpretation i ∧
    type_ok (tysof s) y ∧ term_ok s b ∧ typeof b = Bool ∧
    is_exists_sig (tmsof s) ∧ is_exists_interpretation (tmaof i) ⇒
    termsem (tmsof s) i v (Exists f y b) =
    Boolean (∃x. x <: typesem (tyaof i) (tyvof v) y ∧
                 termsem (tmsof s) i (tyvof v, ((f,y) =+ x) (tmvof v)) b = True)``,
  rw[termsem_def,is_exists_sig_def,is_exists_interpretation_def] >>
  qspecl_then[`tmsof s`,`i`,`strlit"?"`]mp_tac instance_def >> simp[] >>
  disch_then(qspec_then`[y,Tyvar(strlit"A")]`mp_tac) >>
  simp[holSyntaxLibTheory.REV_ASSOCD] >> disch_then kall_tac >>
  CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV EVAL))) >>
  fs[interprets_def] >>
  first_x_assum(qspec_then`K(typesem (tyaof i) (tyvof v) y)`mp_tac) >>
  discharge_hyps >- (
    simp[is_type_valuation_def] >>
    match_mp_tac(UNDISCH typesem_inhabited) >>
    metis_tac[is_interpretation_def,is_valuation_def] ) >>
  simp[] >> disch_then kall_tac >>
  match_mp_tac apply_abstract_matchable >> simp[] >>
  fs[is_std_interpretation_def] >>
  imp_res_tac typesem_Bool >> simp[] >>
  simp[boolean_in_boolset] >>
  simp[holds_def] >>
  conj_tac >- (
    match_mp_tac (UNDISCH abstract_in_funspace) >> simp[] >> rw[] >>
    match_mp_tac (UNDISCH termsem_typesem_matchable) >>
    simp[] >> qexists_tac`s` >> simp[] >>
    fs[is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
    rw[] >> rw[] ) >>
  AP_TERM_TAC >>
  AP_TERM_TAC >>
  simp[FUN_EQ_THM] >>
  gen_tac >>
  qmatch_abbrev_tac`A ∧ B ⇔ A ∧ C` >>
  `A ⇒ (B ⇔ C)` suffices_by metis_tac[] >>
  unabbrev_all_tac >> strip_tac >>
  AP_THM_TAC >> AP_TERM_TAC >>
  match_mp_tac apply_abstract_matchable >> simp[] >>
  match_mp_tac (UNDISCH termsem_typesem_matchable) >>
  simp[] >> qexists_tac`s` >> simp[] >>
  fs[is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> rw[] )

val termsem_forall = store_thm("termsem_forall",
  ``is_set_theory ^mem ⇒
    ∀s i v f y b.
    is_valuation (tysof s) (tyaof i) v ∧
    is_interpretation s i ∧
    is_std_interpretation i ∧
    type_ok (tysof s) y ∧ term_ok s b ∧ typeof b = Bool ∧
    is_forall_sig (tmsof s) ∧ is_forall_interpretation (tmaof i) ⇒
    termsem (tmsof s) i v (Forall f y b) =
    Boolean (∀x. x <: typesem (tyaof i) (tyvof v) y ⇒
                 termsem (tmsof s) i (tyvof v, ((f,y) =+ x) (tmvof v)) b = True)``,
  rw[termsem_def,is_forall_sig_def,is_forall_interpretation_def] >>
  qspecl_then[`tmsof s`,`i`,`strlit"!"`]mp_tac instance_def >> simp[] >>
  disch_then(qspec_then`[y,Tyvar(strlit"A")]`mp_tac) >>
  simp[holSyntaxLibTheory.REV_ASSOCD] >> disch_then kall_tac >>
  CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV EVAL))) >>
  fs[interprets_def] >>
  first_x_assum(qspec_then`K(typesem (tyaof i) (tyvof v) y)`mp_tac) >>
  discharge_hyps >- (
    simp[is_type_valuation_def] >>
    match_mp_tac(UNDISCH typesem_inhabited) >>
    metis_tac[is_interpretation_def,is_valuation_def] ) >>
  simp[] >> disch_then kall_tac >>
  match_mp_tac apply_abstract_matchable >> simp[] >>
  fs[is_std_interpretation_def] >>
  imp_res_tac typesem_Bool >> simp[] >>
  simp[boolean_in_boolset] >>
  simp[holds_def] >>
  conj_tac >- (
    match_mp_tac (UNDISCH abstract_in_funspace) >> simp[] >> rw[] >>
    match_mp_tac (UNDISCH termsem_typesem_matchable) >>
    simp[] >> qexists_tac`s` >> simp[] >>
    fs[is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
    rw[] >> rw[] ) >>
  AP_TERM_TAC >>
  AP_TERM_TAC >>
  simp[FUN_EQ_THM] >>
  gen_tac >>
  qmatch_abbrev_tac`A ⇒ B ⇔ A ⇒ C` >>
  `A ⇒ (B ⇔ C)` suffices_by metis_tac[] >>
  unabbrev_all_tac >> strip_tac >>
  AP_THM_TAC >> AP_TERM_TAC >>
  match_mp_tac apply_abstract_matchable >> simp[] >>
  match_mp_tac (UNDISCH termsem_typesem_matchable) >>
  simp[] >> qexists_tac`s` >> simp[] >>
  fs[is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> rw[] )

val termsem_and = store_thm("termsem_and",
  ``is_set_theory ^mem ⇒
    ∀s i v p1 p2.
    is_valuation (tysof s) (tyaof i) v ∧
    is_interpretation s i ∧
    is_std_type_assignment (tyaof i) ∧
    term_ok s p1 ∧ term_ok s p2 ∧
    typeof p1 = Bool ∧ typeof p2 = Bool ∧
    is_and_sig (tmsof s) ∧ is_and_interpretation (tmaof i) ⇒
    termsem (tmsof s) i v (And p1 p2) =
    Boolean (termsem (tmsof s) i v p1 = True ∧
             termsem (tmsof s) i v p2 = True)``,
  rw[termsem_def,is_and_sig_def,is_and_interpretation_def] >>
  qspecl_then[`tmsof s`,`i`,`strlit"/\\"`]mp_tac instance_def >> simp[] >>
  disch_then(qspec_then`[]`mp_tac) >>
  simp[] >> disch_then kall_tac >>
  CONV_TAC(LAND_CONV(LAND_CONV(LAND_CONV(RAND_CONV EVAL)))) >>
  fs[interprets_def] >>
  first_x_assum(qspec_then`K boolset`mp_tac) >>
  discharge_hyps >- (
    simp[is_type_valuation_def] >>
    metis_tac[boolean_in_boolset]) >>
  simp[] >> disch_then kall_tac >>
  simp[Boolrel_def] >>
  qmatch_abbrev_tac`Abstract b fbb f ' a1 ' a2 = c` >>
  `Abstract b fbb f ' a1 = f a1` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem_matchable) >>
      simp[] >>
      qexists_tac`s` >> simp[] >>
      imp_res_tac typesem_Bool >> simp[] ) >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[boolean_in_boolset] ) >>
  simp[Abbr`f`] >>
  match_mp_tac apply_abstract_matchable >> simp[] >>
  unabbrev_all_tac >> simp[] >>
  conj_tac >- (
    match_mp_tac (UNDISCH termsem_typesem_matchable) >>
    simp[] >>
    qexists_tac`s` >> simp[] >>
    imp_res_tac typesem_Bool >> simp[] ) >>
  simp[boolean_in_boolset] )

val termsem_implies = store_thm("termsem_implies",
  ``is_set_theory ^mem ⇒
    ∀s i v p1 p2.
    is_valuation (tysof s) (tyaof i) v ∧
    is_interpretation s i ∧
    is_std_type_assignment (tyaof i) ∧
    term_ok s p1 ∧ term_ok s p2 ∧
    typeof p1 = Bool ∧ typeof p2 = Bool ∧
    is_implies_sig (tmsof s) ∧ is_implies_interpretation (tmaof i) ⇒
    termsem (tmsof s) i v (Implies p1 p2) =
    Boolean (termsem (tmsof s) i v p1 = True ⇒
             termsem (tmsof s) i v p2 = True)``,
  rw[termsem_def,is_implies_sig_def,is_implies_interpretation_def] >>
  qspecl_then[`tmsof s`,`i`,`strlit"==>"`]mp_tac instance_def >> simp[] >>
  disch_then(qspec_then`[]`mp_tac) >>
  simp[] >> disch_then kall_tac >>
  CONV_TAC(LAND_CONV(LAND_CONV(LAND_CONV(RAND_CONV EVAL)))) >>
  fs[interprets_def] >>
  first_x_assum(qspec_then`K boolset`mp_tac) >>
  discharge_hyps >- (
    simp[is_type_valuation_def] >>
    metis_tac[boolean_in_boolset]) >>
  simp[] >> disch_then kall_tac >>
  simp[Boolrel_def] >>
  qmatch_abbrev_tac`Abstract b fbb f ' a1 ' a2 = c` >>
  `Abstract b fbb f ' a1 = f a1` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem_matchable) >>
      simp[] >>
      qexists_tac`s` >> simp[] >>
      imp_res_tac typesem_Bool >> simp[] ) >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[boolean_in_boolset] ) >>
  simp[Abbr`f`] >>
  match_mp_tac apply_abstract_matchable >> simp[] >>
  unabbrev_all_tac >> simp[] >>
  conj_tac >- (
    match_mp_tac (UNDISCH termsem_typesem_matchable) >>
    simp[] >>
    qexists_tac`s` >> simp[] >>
    imp_res_tac typesem_Bool >> simp[] ) >>
  simp[boolean_in_boolset] )

val extends_sub = store_thm("extends_sub",
  ``∀ctxt2 ctxt1. ctxt2 extends ctxt1 ⇒
      tmsof ctxt1 ⊑ tmsof ctxt2 ∧
      tysof ctxt1 ⊑ tysof ctxt2 ∧
      axsof ctxt1 ⊆ axsof ctxt2``,
  simp[extends_def] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >>
  simp[PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  rpt conj_tac >>
  TRY (
    match_mp_tac finite_mapTheory.SUBMAP_FUNION >>
    disj2_tac >> simp[] >>
    imp_res_tac updates_DISJOINT >> fs[] >>
    fs[finite_mapTheory.SUBMAP_DEF,pred_setTheory.IN_DISJOINT] >>
    metis_tac[] ) >>
  metis_tac[pred_setTheory.SUBSET_UNION,pred_setTheory.SUBSET_TRANS])

val extends_is_bool_interpretation = store_thm("extends_is_bool_interpretation",
  ``is_set_theory ^mem ∧
    ctxt2 extends (mk_bool_ctxt ctxt) ∧
    theory_ok (thyof (mk_bool_ctxt ctxt)) ∧
    i models (thyof ctxt2) ⇒
    is_bool_interpretation i``,
  strip_tac >>
  `i models thyof (mk_bool_ctxt ctxt)` by (
    `∃x y z. thyof (mk_bool_ctxt ctxt) = ((x,y),z)` by metis_tac[pairTheory.PAIR] >>
    simp[] >>
    match_mp_tac (UNDISCH models_reduce) >>
    imp_res_tac theory_ok_sig >> rfs[] >>
    `∃x y z. thyof ctxt2 = ((x,y),z)` by metis_tac[pairTheory.PAIR] >>
    fs[] >>
    CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(can(match_term``i models A``)))) >>
    first_assum(match_exists_tac o concl) >> simp[] >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    imp_res_tac extends_sub >> fs[] >>
    fs[theory_ok_def] ) >>
  metis_tac[bool_has_bool_interpretation])

val INST_CORE_NIL = store_thm("INST_CORE_NIL",
  ``∀env tyin tm. welltyped tm ∧ tyin = [] ∧
      (∀x ty. VFREE_IN (Var x ty) tm ⇒ REV_ASSOCD (Var x (TYPE_SUBST tyin ty)) env (Var x ty) = Var x ty) ⇒
      INST_CORE env tyin tm = Result tm``,
  ho_match_mp_tac INST_CORE_ind >>
  simp[INST_CORE_def] >>
  rw[] >> fs[] >>
  Q.PAT_ABBREV_TAC`i1 = INST_CORE X [] tm` >>
  `i1 = Result tm` by (
    qunabbrev_tac`i1` >>
    first_x_assum match_mp_tac >>
    simp[holSyntaxLibTheory.REV_ASSOCD] >>
    rw[] >> metis_tac[] ) >>
  simp[])

val INST_nil = store_thm("INST_nil",
  ``welltyped tm ⇒ (INST [] tm = tm)``,
  rw[INST_def,INST_CORE_def] >>
  qspecl_then[`[]`,`[]`,`tm`]mp_tac INST_CORE_NIL >>
  simp[holSyntaxLibTheory.REV_ASSOCD])
(* -- *)

val lca_ctxt = unpack_ctxt lca_ctxt_thm
val lca_inner_ctxt = lca_extends_init |> concl |> rator |> rand
val lca_ctxt_def = Define`
  lca_ctxt = ^lca_inner_ctxt`

val theory_ok_lca = store_thm("theory_ok_lca",
  ``theory_ok (thyof lca_ctxt)``,
  metis_tac[lca_extends_init |> REWRITE_RULE[GSYM lca_ctxt_def],
            init_theory_ok,extends_theory_ok])

val FLOOKUP_LCA = (
  ``ALOOKUP (const_list lca_ctxt) (strlit"LCA")``
  |> (PURE_ONCE_REWRITE_CONV[lca_ctxt_def] THENC EVAL))

val FLOOKUP_UNIV = (
  ``ALOOKUP (const_list lca_ctxt) (strlit"UNIV")``
  |> (PURE_ONCE_REWRITE_CONV[lca_ctxt_def] THENC EVAL))

val FLOOKUP_cardleq = (
  ``ALOOKUP (const_list lca_ctxt) (strlit"cardleq")``
  |> (PURE_ONCE_REWRITE_CONV[lca_ctxt_def] THENC EVAL))

val FLOOKUP_countable = (
  ``ALOOKUP (const_list lca_ctxt) (strlit"countable")``
  |> (PURE_ONCE_REWRITE_CONV[lca_ctxt_def] THENC EVAL))

val FLOOKUP_INJ = (
  ``ALOOKUP (const_list lca_ctxt) (strlit"INJ")``
  |> (PURE_ONCE_REWRITE_CONV[lca_ctxt_def] THENC EVAL))

val FLOOKUP_IN = (
  ``ALOOKUP (const_list lca_ctxt) (strlit"IN")``
  |> (PURE_ONCE_REWRITE_CONV[lca_ctxt_def] THENC EVAL))

val FLOOKUP_LESS = (
  ``ALOOKUP (const_list lca_ctxt) (strlit"<")``
  |> (PURE_ONCE_REWRITE_CONV[lca_ctxt_def] THENC EVAL))

val lca_is_bool_sig = store_thm("lca_is_bool_sig",
  ``is_bool_sig (sigof lca_ctxt)``,
  EVAL_TAC)

val _ = overload_on("Num", ``Tyapp(strlit"num")[]``)
val quote_def = Define`
  (quote 0 = Const (strlit"0") Num) ∧
  (quote (SUC n) = Comb (Const(strlit"SUC")(Fun Num Num))
                        (quote n))`

val type_ok_Num = store_thm("type_ok_Num",
  ``type_ok (tysof lca_ctxt) Num``,
  rw[type_ok_def] >>
  ONCE_REWRITE_TAC[lca_ctxt_def] >>
  EVAL_TAC)

val LCA_l_UNIV = term_to_deep ``LCA l (UNIV:'U set)``

(* TODO: stolen from reflectionLib.sml *)
val tyvar_inst_exists2 = prove(
  ``∃i. tyvar = REV_ASSOCD b1 i b1 ∧
        tyvar = REV_ASSOCD b2 i b2``,
  qexists_tac`[(tyvar,b1);(tyvar,b2)]` >>
  EVAL_TAC)
val tyvar_inst_exists2_diff = prove(
  ``b1 ≠ b2 ⇒
    ∃i. ty1 = REV_ASSOCD b1 i b1 ∧
        ty2 = REV_ASSOCD b2 i b2``,
  strip_tac >>
  qexists_tac`[(ty1,b1);(ty2,b2)]` >>
  EVAL_TAC >> rw[])
(* -- *)
(* TODO: stolen from holDerivationScript.sml *)
fun replace_term from to =
  let
    fun f tm =
      if tm = from then to else
        case dest_term tm of
          COMB(t1,t2) => mk_comb(f t1, f t2)
        | LAMB(t1,t2) => mk_abs(f t1, f t2)
        | _ => tm
  in
    f
  end
(* -- *)
val EVAL_STRING_SORT = basicReflectionLib.EVAL_STRING_SORT

val (EVAL_type_ok0,EVAL_term_ok0) =
  EVAL_type_ok_term_ok
    EVAL (MATCH_MP theory_ok_sig theory_ok_lca |> SIMP_RULE std_ss[])

val th = prove(``tysof lca_ctxt = tysof(sigof lca_ctxt)``,rw[])
val EVAL_type_ok =
  (RATOR_CONV(RAND_CONV(REWR_CONV th))) THENC EVAL_type_ok0

val EVAL_term_ok =
  EVAL_term_ok0 THENC
  SIMP_CONV (srw_ss()) [
    holSyntaxLibTheory.tyvar_inst_exists,
    tyvar_inst_exists2,
    tyvar_inst_exists2_diff]

fun process n =
  ONCE_REWRITE_TAC[relationTheory.RTC_CASES1] >> disj2_tac >>
  CONV_TAC(QUANT_CONV(LAND_CONV(RATOR_CONV BETA_CONV THENC BETA_CONV))) >>
  CONV_TAC(QUANT_CONV(LAND_CONV(QUANT_CONV(LAND_CONV(REWR_CONV listTheory.CONS_11))))) >>
  CONV_TAC(QUANT_CONV(LAND_CONV((QUANT_CONV(REWR_CONV (GSYM CONJ_ASSOC)))THENC HO_REWR_CONV UNWIND_THM1))) >>
  CONV_TAC((QUANT_CONV(REWR_CONV (GSYM CONJ_ASSOC))) THENC HO_REWR_CONV UNWIND_THM1) >>
  conj_tac >- ACCEPT_TAC (#updates_thm (el n lca_ctxt))

val models_lca_ctxt_has_bool_interpretation = prove(
  ``is_set_theory ^mem ∧ i models thyof lca_ctxt ⇒ is_bool_interpretation i``,
  rw[] >>
  match_mp_tac (GEN_ALL extends_is_bool_interpretation) >>
  qexists_tac`lca_ctxt` >>
  qexists_tac`init_ctxt` >>
  simp[] >>
  conj_tac >- (
    simp[extends_def] >>
    ONCE_REWRITE_TAC[lca_ctxt_def] >>
    map_every process (List.tabulate(18,curry op+1)) >>
    simp[GSYM extends_def] >>
    simp[holConsistencyTheory.hol_extends_bool] ) >>
  metis_tac[extends_theory_ok,bool_extends_init,init_theory_ok])

fun EVAL_INST tm =
  assert (same_const``INST`` o fst o strip_comb) tm |> (
  REWR_CONV(MATCH_MP holDerivationTheory.inst_eval_thm
    (EQT_ELIM(EVAL_welltyped ``welltyped^(rand tm)``))) THENC
  EVAL_subst)

fun Abbrev_intro_tac th = assume_tac(EQ_MP(SPEC(concl th)(GSYM markerTheory.Abbrev_def))th)

val lca_of_sigof = prove(``tmsof (sigof lca_ctxt) = tmsof lca_ctxt``,rw[])

fun use_apply_abstract (g as (asl,w)) =
  let
    val sel = lhs o snd o dest_imp
    val tm = find_term(can(match_term(sel(concl(SPEC_ALL apply_abstract_matchable))))) w
  in
    mp_tac(Q.GEN`u`(PART_MATCH sel apply_abstract_matchable tm))
  end g

fun use_termsem_implies (g as (asl,w)) =
  let
    val tm = find_term(can(match_term``termsem s i v (Implies a b)``)) w
    val (_,args) = strip_comb tm
    val imp = el 5 args
    val p1 = imp |> rator |> rand |> rand
    val p2 = imp |> rand
    val s = el 2 args |> REWR_CONV(SYM lca_of_sigof) |> concl |> rhs |> rand
    val th =
      UNDISCH termsem_implies
      |> SPECL[s, el 3 args, el 4 args, p1, p2]
      |> CONV_RULE(DEPTH_CONV(REWR_CONV lca_of_sigof))
  in
    mp_tac th >>
    discharge_hyps >- (
      assume_tac lca_is_bool_sig >>
      imp_res_tac models_lca_ctxt_has_bool_interpretation >>
      conj_tac >- simp[] >>
      conj_tac >- fs[models_def] >>
      conj_tac >- fs[models_def,is_std_interpretation_def] >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      conj_tac >- (CONV_TAC (LAND_CONV EVAL_typeof) >> REFL_TAC) >>
      conj_tac >- (CONV_TAC (LAND_CONV EVAL_typeof) >> REFL_TAC) >>
      fs[is_bool_interpretation_def,is_bool_sig_def] ) >>
    disch_then (CHANGED_TAC o SUBST1_TAC)
  end g

fun use_termsem_and (g as (asl,w)) =
  let
    val tm = find_term(can(match_term``termsem s i v (And a b)``)) w
    val (_,args) = strip_comb tm
    val imp = el 5 args
    val p1 = imp |> rator |> rand |> rand
    val p2 = imp |> rand
    val s = el 2 args |> REWR_CONV(SYM lca_of_sigof) |> concl |> rhs |> rand
    val th =
      UNDISCH termsem_and
      |> SPECL[s, el 3 args, el 4 args, p1, p2]
      |> CONV_RULE(DEPTH_CONV(REWR_CONV lca_of_sigof))
  in
    mp_tac th >>
    discharge_hyps >- (
      assume_tac lca_is_bool_sig >>
      imp_res_tac models_lca_ctxt_has_bool_interpretation >>
      conj_tac >- simp[] >>
      conj_tac >- fs[models_def] >>
      conj_tac >- fs[models_def,is_std_interpretation_def] >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      conj_tac >- (CONV_TAC (LAND_CONV EVAL_typeof) >> REFL_TAC) >>
      conj_tac >- (CONV_TAC (LAND_CONV EVAL_typeof) >> REFL_TAC) >>
      fs[is_bool_interpretation_def,is_bool_sig_def] ) >>
    disch_then (CHANGED_TAC o SUBST1_TAC)
  end g

fun use_termsem_equation (g as (asl,w)) =
  let
    val tm = find_term(can(match_term``termsem s i v (a === b)``)) w
    val (_,args) = strip_comb tm
    val eq = el 5 args
    val p1 = eq |> rator |> rand
    val p2 = eq |> rand
    val s = el 2 args |> REWR_CONV(SYM lca_of_sigof) |> concl |> rhs |> rand
    val th =
      UNDISCH termsem_equation
      |> SPECL[s, el 3 args, el 4 args, p1, p2, el 2 args]
      |> CONV_RULE(DEPTH_CONV(REWR_CONV lca_of_sigof))
  in
    mp_tac th >>
    discharge_hyps >- (
      conj_tac >- (
        simp[is_structure_def] >>
        fs[models_def] >>
        assume_tac theory_ok_lca >>
        imp_res_tac theory_ok_sig >>
        fs[] ) >>
      conj_tac >- (
        simp[equation_def] >>
        CONV_TAC EVAL_term_ok ) >>
      REFL_TAC ) >>
    disch_then(CHANGED_TAC o SUBST1_TAC)
  end g

fun use_termsem_forall (g as (asl,w)) =
  let
    val tm = find_term(can(match_term``termsem s i v (Forall x y z)``)) w
    val (_,args) = strip_comb tm
    val eq = el 5 args
    val p1 = eq |> rand |> rator |> rand |> rator |> rand
    val p2 = eq |> rand |> rator |> rand |> rand
    val p3 = eq |> rand |> rand
    val s = el 2 args |> REWR_CONV(SYM lca_of_sigof) |> concl |> rhs |> rand
    val th =
      UNDISCH termsem_forall
      |> SPECL[s, el 3 args, el 4 args, p1, p2, p3]
      |> CONV_RULE(DEPTH_CONV(REWR_CONV lca_of_sigof))
  in
    mp_tac th >>
    discharge_hyps >- (
      conj_tac >- simp[] >>
      conj_tac >- fs[models_def] >>
      conj_tac >- fs[models_def] >>
      conj_tac >- (CONV_TAC EVAL_type_ok0) >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      conj_tac >- (CONV_TAC(LAND_CONV EVAL_typeof) >> REFL_TAC) >>
      assume_tac lca_is_bool_sig >>
      imp_res_tac models_lca_ctxt_has_bool_interpretation >>
      fs[is_bool_interpretation_def,is_bool_sig_def]) >>
    disch_then(CHANGED_TAC o SUBST1_TAC)
  end g

fun use_termsem_exists (g as (asl,w)) =
  let
    val tm = find_term(can(match_term``termsem s i v (Exists x y z)``)) w
    val (_,args) = strip_comb tm
    val eq = el 5 args
    val p1 = eq |> rand |> rator |> rand |> rator |> rand
    val p2 = eq |> rand |> rator |> rand |> rand
    val p3 = eq |> rand |> rand
    val s = el 2 args |> REWR_CONV(SYM lca_of_sigof) |> concl |> rhs |> rand
    val th =
      UNDISCH termsem_exists
      |> SPECL[s, el 3 args, el 4 args, p1, p2, p3]
      |> CONV_RULE(DEPTH_CONV(REWR_CONV lca_of_sigof))
  in
    mp_tac th >>
    discharge_hyps >- (
      conj_tac >- simp[] >>
      conj_tac >- fs[models_def] >>
      conj_tac >- fs[models_def] >>
      conj_tac >- (CONV_TAC EVAL_type_ok0) >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      conj_tac >- (CONV_TAC(LAND_CONV EVAL_typeof) >> REFL_TAC) >>
      assume_tac lca_is_bool_sig >>
      imp_res_tac models_lca_ctxt_has_bool_interpretation >>
      fs[is_bool_interpretation_def,is_bool_sig_def]) >>
    disch_then(CHANGED_TAC o SUBST1_TAC)
  end g

val termsem_IN = store_thm("termsem_IN",
  ``is_set_theory ^mem ⇒
    ∀i v ty1 a b ty a0 b0 tyin.
    i models thyof lca_ctxt ∧
    is_valuation (tysof lca_ctxt) (tyaof i) v ∧
    a = INST tyin a0 ∧
    b = INST tyin b0 ∧
    ty1 = Fun ty (Fun (Fun ty Bool) Bool) ∧
    ty = REV_ASSOCD (Tyvar(strlit"A")) tyin (Tyvar(strlit"A")) ∧
    EVERY (type_ok (tysof lca_ctxt)) (MAP FST tyin) ∧
    term_ok (sigof lca_ctxt) a0 ∧
    term_ok (sigof lca_ctxt) b0 ∧
    typeof a0 = Tyvar(strlit"A") ∧
    typeof b0 = (Fun (Tyvar(strlit"A")) Bool) ⇒
    termsem (tmsof lca_ctxt) i v
      (Comb (Comb (Const (strlit "IN") ty1) a) b)
    = Boolean(Holds (termsem (tmsof lca_ctxt) i v b) (termsem (tmsof lca_ctxt) i v a))``,
  rpt strip_tac >>
  qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i v (Comb (Comb (Const g gy) a) b) = R` >>
  qspecl_then[`lca_ctxt`,`i`,`v`,`g`,`gy`,`tyin`,`a`,`b`]mp_tac (UNDISCH termsem_comb2_ax) >>
  qunabbrev_tac`g` >>
  CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(LAND_CONV EVAL)))) >>
  simp[FLOOKUP_IN,Abbr`gy`,REV_ASSOCD] >>
  disch_then(qspecl_then[`a0`,`b0`]mp_tac) >>
  simp[theory_ok_lca] >>
  discharge_hyps >- metis_tac[WELLTYPED,term_ok_welltyped] >>
  disch_then SUBST1_TAC >>
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV(EVAL_subst)))) >>
  qpat_assum`ty = X`Abbrev_intro_tac >>
  qpat_assum`a = X`Abbrev_intro_tac >>
  qpat_assum`b = X`Abbrev_intro_tac >>
  imp_res_tac term_ok_welltyped >>
  simp[INST_def,INST_CORE_def,INST_CORE_NIL_IS_RESULT,NOT_IS_CLASH_IS_RESULT] >>
  simp[GSYM INST_def] >>
  simp[termsem_def,Abbr`R`,holds_def,boolean_def] >> rw[] >>
  qmatch_abbrev_tac`r:'U = False` >>
  `r <: boolset` suffices_by metis_tac[mem_boolset] >>
  qunabbrev_tac`r` >>
  match_mp_tac(UNDISCH apply_in_rng) >>
  qexists_tac`typesem (tyaof i) (tyvof v) ty` >>
  `term_ok (sigof lca_ctxt) a` by (
    qunabbrev_tac`a` >>
    match_mp_tac term_ok_INST >>
    simp[] ) >>
  `term_ok (sigof lca_ctxt) b` by (
    qunabbrev_tac`b` >>
    match_mp_tac term_ok_INST >>
    simp[] ) >>
  qspecl_then[`a0`,`typeof a0`,`tyin`]mp_tac INST_HAS_TYPE >>
  simp_tac bool_ss [] >> discharge_hyps >- metis_tac[WELLTYPED] >>
  qspecl_then[`b0`,`typeof b0`,`tyin`]mp_tac INST_HAS_TYPE >>
  simp_tac bool_ss [] >> discharge_hyps >- metis_tac[WELLTYPED] >>
  simp[] >> ntac 2 strip_tac >>
  imp_res_tac WELLTYPED_LEMMA >>
  conj_tac >- (
    qpat_assum`typeof a = ty`(SUBST1_TAC o SYM) >>
    match_mp_tac (UNDISCH termsem_typesem_matchable) >>
    qexists_tac`sigof lca_ctxt` >> simp[] >>
    fs[models_def,is_std_interpretation_def] ) >>
  match_mp_tac (UNDISCH termsem_typesem_matchable) >>
  qexists_tac`sigof lca_ctxt` >> simp[] >>
  fs[models_def,is_std_interpretation_def] >>
  imp_res_tac typesem_Fun >>
  imp_res_tac typesem_Bool >> simp[])

(*
val (g as (_,w)) = top_goal()
*)

fun use_termsem_IN_simple (g as (asl,w)) =
  let
    val tm = find_term(can(match_term``termsem s i v (Comb (Comb (Const (strlit"IN") ty) a) b)``)) w
    val (_,args) = strip_comb tm
    val app = el 5 args
    val ty = app |> rator |> rand |> rator |> rand |> rand
    val a = app |> rator |> rand |> rand
    val b = app |> rand
    val th =
      UNDISCH termsem_IN
      |> SPECL[el 3 args, el 4 args, ty, a, b]
  in
    mp_tac th >> simp[] >>
    disch_then(qspec_then`[]`mp_tac o SPECL[a,b]) >>
    discharge_hyps_keep >- (
      conj_tac >- (CONV_TAC(RAND_CONV(EVAL_INST)) >> REFL_TAC) >>
      conj_tac >- (CONV_TAC(RAND_CONV(EVAL_INST)) >> REFL_TAC) >>
      conj_tac >- (simp[REV_ASSOCD]) >>
      conj_tac >- (simp[]) >>
      conj_tac >- (CONV_TAC(EVAL_term_ok)) >>
      conj_tac >- (CONV_TAC(EVAL_term_ok)) >>
      conj_tac >- (CONV_TAC(LAND_CONV(EVAL_typeof))>>REFL_TAC) >>
      (CONV_TAC(LAND_CONV(EVAL_typeof))>>REFL_TAC)) >>
    pop_assum(fn th =>
      map_every (SUBST1_TAC o SYM) (List.take((CONJUNCTS th),2))) >>
    disch_then(CHANGED_TAC o SUBST1_TAC)
  end g

val termsem_UNIV = store_thm("termsem_UNIV",
  ``is_set_theory ^mem ⇒
    ∀i v ty.
    i models thyof lca_ctxt ∧
    is_valuation (tysof lca_ctxt) (tyaof i) v ∧
    type_ok (tysof lca_ctxt) ty ⇒
    termsem (tmsof lca_ctxt) i v (Const (strlit "UNIV") (Fun ty Bool))
    = Abstract (typesem (tyaof i) (tyvof v) ty) boolset (K True)``,
  rpt strip_tac >>
  `∃ty0 r. (Const(strlit"UNIV")ty0 === r) ∈ (axsof lca_ctxt)` by
    (EVAL_TAC >> simp[] ) >>
  pop_assum (fn th=> assume_tac th >> mp_tac th) >>
  CONV_TAC(LAND_CONV EVAL) >> strip_tac >>
  qmatch_assum_abbrev_tac`MEM eq aqs` >>
  qpat_assum`ty = X`Abbrev_intro_tac >>
  `i satisfies (sigof lca_ctxt,[],eq)` by fs[models_def] >>
  qspecl_then[`sigof lca_ctxt`,`eq`,`[(ty,Tyvar(strlit"A"))]`]mp_tac termsem_INST >>
  simp[] >>
  discharge_hyps >- (
    unabbrev_all_tac >>
    assume_tac theory_ok_lca >>
    imp_res_tac theory_ok_sig >>
    fs[term_ok_equation] >>
    conj_tac >> CONV_TAC(EVAL_term_ok) ) >>
  disch_then(qspecl_then[`i`,`v`]mp_tac) >>
  simp[Abbr`eq`,equation_def,Abbr`ty0`] >>
  CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV EVAL_INST))) >>
  Q.PAT_ABBREV_TAC`vv:'U valuation = X Y` >>
  `is_valuation (tysof lca_ctxt) (tyaof i) vv` by (
    fs[Abbr`vv`,is_valuation_def,is_type_valuation_def,is_term_valuation_def] >>
    conj_tac >- (
      gen_tac >>
      match_mp_tac(UNDISCH typesem_inhabited) >>
      qexists_tac`tysof lca_ctxt` >>
      simp[is_type_valuation_def] >>
      fs[models_def,is_interpretation_def] >>
      simp[holSyntaxLibTheory.REV_ASSOCD] >>
      BasicProvers.CASE_TAC >> simp[type_ok_def]) >>
    qx_genl_tac[`z`,`zy`] >> strip_tac >>
    first_x_assum(qspecl_then[`z`,`TYPE_SUBST [(ty,Tyvar(strlit"A"))] zy`]mp_tac) >>
    simp[type_ok_TYPE_SUBST,Once typesem_TYPE_SUBST] ) >>
  simp[equation_intro] >>
  fs[satisfies_def] >>
  first_x_assum(qspec_then`vv`mp_tac) >> simp[] >>
  disch_then kall_tac >>
  qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i v (ll === rr) = True ==> R` >>
  qspecl_then[`sigof lca_ctxt`,`i`,`v`,`ll`,`rr`]mp_tac(UNDISCH termsem_equation) >>
  simp[] >> discharge_hyps >- (
    simp[is_structure_def] >>
    fs[models_def] >>
    conj_tac >- (
      assume_tac theory_ok_lca >>
      imp_res_tac theory_ok_sig >> fs[]) >>
    simp[Abbr`ll`,Abbr`rr`,equation_def] >>
    CONV_TAC EVAL_term_ok >>
    simp[] ) >>
  simp[boolean_eq_true] >>
  disch_then kall_tac >>
  simp[Abbr`R`] >> disch_then kall_tac >>
  simp[Abbr`rr`,termsem_def] >>
  qunabbrev_tac`aqs` >>
  imp_res_tac models_lca_ctxt_has_bool_interpretation >>
  fs[models_def,is_std_interpretation_def] >>
  imp_res_tac typesem_Bool >> simp[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[] >>
  assume_tac(EVAL``FLOOKUP (tmsof lca_ctxt) (strlit "T")``) >>
  simp[identity_instance] >>
  EVAL_STRING_SORT >> simp[] >>
  fs[is_bool_interpretation_def,is_true_interpretation_def,interprets_nil] >>
  simp[mem_boolset])

val termsem_INJ = store_thm("termsem_INJ",
  ``is_set_theory ^mem ⇒
    ∀i v ty1 a b c tya tyb a0 b0 c0 tyin.
    i models thyof lca_ctxt ∧
    is_valuation (tysof lca_ctxt) (tyaof i) v ∧
    a = INST tyin a0 ∧
    b = INST tyin b0 ∧
    c = INST tyin c0 ∧
    ty1 = Fun (Fun tya tyb) (Fun (Fun tya Bool) (Fun (Fun tyb Bool) Bool)) ∧
    tya = REV_ASSOCD(Tyvar(strlit"A"))tyin(Tyvar(strlit"A")) ∧
    tyb = REV_ASSOCD(Tyvar(strlit"B"))tyin(Tyvar(strlit"B")) ∧
    EVERY (type_ok (tysof lca_ctxt)) (MAP FST tyin) ∧
    term_ok (sigof lca_ctxt) a0 ∧
    term_ok (sigof lca_ctxt) b0 ∧
    term_ok (sigof lca_ctxt) c0 ∧
    typeof a0 = (Fun (Tyvar(strlit"A")) (Tyvar(strlit"B"))) ∧
    typeof b0 = (Fun (Tyvar(strlit"A")) Bool) ∧
    typeof c0 = (Fun (Tyvar(strlit"B")) Bool)
    ⇒
    termsem (tmsof lca_ctxt) i v
      (Comb (Comb (Comb
        (Const (strlit "INJ") ty1)
        a) b) c) =
    Boolean (INJ ($' (termsem (tmsof lca_ctxt) i v a))
              (ext(typesem (tyaof i) (tyvof v) tya) ∩ Holds (termsem (tmsof lca_ctxt) i v b))
              (ext(typesem (tyaof i) (tyvof v) tyb) ∩ Holds (termsem (tmsof lca_ctxt) i v c)))``,
  rpt strip_tac >>
  qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i v (Comb (Comb (Comb (Const g ty) a) b) c) = R` >>
  qspecl_then[`lca_ctxt`,`i`,`v`,`g`,`ty`,`tyin`,`a`,`b`,`c`]mp_tac (UNDISCH termsem_comb3_ax) >>
  qunabbrev_tac`g` >>
  CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(LAND_CONV EVAL)))) >>
  simp[FLOOKUP_INJ,Abbr`ty`,REV_ASSOCD] >>
  disch_then(qspecl_then[`a0`,`b0`,`c0`]mp_tac) >>
  simp[theory_ok_lca] >>
  discharge_hyps >- metis_tac[WELLTYPED,term_ok_welltyped] >>
  disch_then SUBST1_TAC >>
  qpat_assum`tya = X`Abbrev_intro_tac >>
  qpat_assum`tyb = X`Abbrev_intro_tac >>
  qpat_assum`a = X`Abbrev_intro_tac >>
  qpat_assum`b = X`Abbrev_intro_tac >>
  qpat_assum`c = X`Abbrev_intro_tac >>
  simp[] >>
  Q.PAT_ABBREV_TAC`s = (a0,Var X Y)::Z` >>
  Q.PAT_ABBREV_TAC`tm = And X Y` >>
  `term_ok (sigof lca_ctxt) tm` by (
    qunabbrev_tac`tm` >>
    CONV_TAC(EVAL_term_ok) ) >>
  `term_ok (sigof lca_ctxt) (VSUBST s tm)` by (
    match_mp_tac term_ok_VSUBST >>
    simp[Abbr`s`] >> ntac 2 (pop_assum kall_tac) >> rw[] >>
    metis_tac[WELLTYPED,term_ok_welltyped]) >>
  qspecl_then[`sigof lca_ctxt`,`VSUBST s tm`,`tyin`]mp_tac termsem_INST >> simp[] >>
  disch_then kall_tac >>
  Q.PAT_ABBREV_TAC`vvv:'U valuation = X Y` >>
  `is_valuation (tysof lca_ctxt) (tyaof i) vvv` by (
    qpat_assum`term_ok X tm`kall_tac >>
    qpat_assum`term_ok X (VSUBST A Y)`kall_tac >>
    qunabbrev_tac`tm` >>
    simp[Abbr`vvv`] >>
    fs[is_valuation_def,is_type_valuation_def,is_term_valuation_def] >>
    conj_tac >- (
      gen_tac >>
      match_mp_tac(UNDISCH typesem_inhabited) >>
      qexists_tac`tysof lca_ctxt` >>
      simp[is_type_valuation_def] >>
      fs[models_def,is_interpretation_def] >>
      simp[holSyntaxLibTheory.REV_ASSOCD_ALOOKUP] >>
      BasicProvers.CASE_TAC >> simp[type_ok_def] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[EVERY_MEM,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
      metis_tac[]) >>
     qx_genl_tac[`z`,`ty`] >> strip_tac >>
     first_x_assum(qspecl_then[`z`,`TYPE_SUBST tyin ty`]mp_tac) >>
     simp[type_ok_TYPE_SUBST,Once typesem_TYPE_SUBST] ) >>
  qspecl_then[`tm`,`s`]mp_tac termsem_VSUBST >>
  discharge_hyps >- (
    imp_res_tac term_ok_welltyped >>
    simp[Abbr`s`] >> ntac 9 (pop_assum kall_tac) >> rw[] >>
    metis_tac[WELLTYPED,term_ok_welltyped]) >>
  simp[] >> disch_then kall_tac >>
  Q.PAT_ABBREV_TAC`vv:'U valuation = X Y` >>
  simp[Abbr`tm`] >>
  qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i vv (And tm1 tm2) = R` >>
  qspecl_then[`sigof lca_ctxt`,`i`,`vv`,`tm1`,`tm2`]mp_tac (UNDISCH termsem_and) >>
  `is_valuation (tysof lca_ctxt) (tyaof i) vv` by (
    qpat_assum`term_ok X (And tm1 tm2)`kall_tac >>
    qpat_assum`term_ok X (VSUBST A Y)`kall_tac >>
    map_every qunabbrev_tac[`tm1`,`tm2`] >>
    simp[Abbr`vv`,Abbr`s`,UPDATE_LIST_THM] >>
    match_mp_tac is_valuation_extend >>
    reverse conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem_matchable) >>
      qexists_tac`sigof lca_ctxt`>>simp[] >>
      fs[models_def,is_std_interpretation_def] ) >>
    match_mp_tac is_valuation_extend >>
    reverse conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem_matchable) >>
      qexists_tac`sigof lca_ctxt`>>simp[] >>
      fs[models_def,is_std_interpretation_def] ) >>
    match_mp_tac is_valuation_extend >>
    reverse conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem_matchable) >>
      qexists_tac`sigof lca_ctxt`>>simp[] >>
      fs[models_def,is_std_interpretation_def] ) >>
    simp[] ) >>
  discharge_hyps >- (
    imp_res_tac models_lca_ctxt_has_bool_interpretation >>
    assume_tac lca_is_bool_sig >>
    fs[models_def,is_std_interpretation_def,is_bool_interpretation_def,is_bool_sig_def] >>
    unabbrev_all_tac >>
    conj_tac >- (CONV_TAC EVAL_term_ok) >>
    conj_tac >- (CONV_TAC EVAL_term_ok) >>
    conj_tac >- (CONV_TAC (LAND_CONV EVAL_typeof) >> REFL_TAC) >>
    (CONV_TAC (LAND_CONV EVAL_typeof) >> REFL_TAC)) >>
  simp[] >> disch_then kall_tac >>
  simp[Abbr`R`] >>
  AP_TERM_TAC >>
  simp[pred_setTheory.INJ_DEF] >>
  qmatch_abbrev_tac`A ∧ B ⇔ A' ∧ B'` >>
  `(A ⇔ A') ∧ (B ⇔ B')` suffices_by rw[] >>
  map_every qunabbrev_tac[`A`,`A'`,`B`,`B'`] >>
  conj_tac >- (
    qpat_assum`term_ok X (And tm1 tm2)`kall_tac >>
    qpat_assum`term_ok X (VSUBST A Y)`kall_tac >>
    map_every qunabbrev_tac[`tm1`,`tm2`] >>
    qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i vv (Forall f ty t) = True ⇔ R` >>
    qspecl_then[`sigof lca_ctxt`,`i`,`vv`,`f`,`ty`,`t`]mp_tac (UNDISCH termsem_forall) >>
    discharge_hyps >- (
      imp_res_tac models_lca_ctxt_has_bool_interpretation >>
      assume_tac lca_is_bool_sig >>
      fs[models_def,is_std_interpretation_def,is_bool_interpretation_def,is_bool_sig_def] >>
      unabbrev_all_tac >>
      conj_tac >- (CONV_TAC EVAL_type_ok) >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      (CONV_TAC (LAND_CONV EVAL_typeof) >> REFL_TAC)) >>
    simp[] >> disch_then kall_tac >>
    simp[boolean_eq_true,Abbr`R`] >>
    simp[IN_DEF,ext_def,GSYM AND_IMP_INTRO] >>
    `typesem (tyaof i) (tyvof vv) ty = typesem (tyaof i) (tyvof v) tya` by (
      simp[Abbr`ty`,typesem_def,Abbr`vv`,Abbr`vvv`] ) >>
    simp[] >>
    qho_match_abbrev_tac`(∀x. P x ⇒ Q x) ⇔ (∀x. P x ⇒ R x)` >>
    `∀x. P x ⇒ (Q x ⇔ R x)` suffices_by rw[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >> simp[] >>
    gen_tac >> strip_tac >>
    qunabbrev_tac`t` >>
    qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i vvx (Implies tm1 tm2) = True ⇔ R` >>
    `is_valuation (tysof lca_ctxt) (tyaof i) vvx` by (
      simp[Abbr`vvx`] >>
      match_mp_tac is_valuation_extend >>
      simp[] ) >>
    qspecl_then[`sigof lca_ctxt`,`i`,`vvx`,`tm1`,`tm2`]mp_tac (UNDISCH termsem_implies) >>
    discharge_hyps >- (
      imp_res_tac models_lca_ctxt_has_bool_interpretation >>
      assume_tac lca_is_bool_sig >>
      fs[models_def,is_std_interpretation_def,is_bool_interpretation_def,is_bool_sig_def] >>
      unabbrev_all_tac >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      conj_tac >- (CONV_TAC (LAND_CONV EVAL_typeof) >> REFL_TAC) >>
      (CONV_TAC (LAND_CONV EVAL_typeof) >> REFL_TAC)) >>
    simp[] >> disch_then kall_tac >>
    simp[boolean_eq_true,Abbr`R`] >>
    qmatch_abbrev_tac`A ⇒ B ⇔ A' ⇒ B'` >>
    `(A ⇔ A') ∧ (B ⇔ B')` suffices_by rw[] >>
    map_every qunabbrev_tac[`A`,`A'`,`B`,`B'`] >>
    conj_tac >- (
      simp[Abbr`tm1`,Abbr`tm2`] >>
      qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i vvx (Comb (Comb (Const (strlit"IN") ty0) tm1) tm2) = True ⇔ R` >>
      qspecl_then[`i`,`vvx`,`ty0`,`tm1`,`tm2`,`ty`,`tm1`,`tm2`,`[]`]mp_tac(UNDISCH termsem_IN) >>
      simp[] >>
      discharge_hyps >- (
        unabbrev_all_tac >>
        conj_tac >- ( CONV_TAC(RAND_CONV EVAL_INST) >> REFL_TAC) >>
        conj_tac >- ( CONV_TAC(RAND_CONV EVAL_INST) >> REFL_TAC) >>
        conj_tac >- (simp[REV_ASSOCD]) >>
        conj_tac >- ( CONV_TAC(EVAL_term_ok)) >>
        conj_tac >- ( CONV_TAC(EVAL_term_ok)) >>
        conj_tac >- ( CONV_TAC(LAND_CONV EVAL_typeof) >> REFL_TAC) >>
        ( CONV_TAC(LAND_CONV EVAL_typeof) >> REFL_TAC) ) >>
      simp[] >> disch_then kall_tac >>
      simp[boolean_eq_true,Abbr`R`] >>
      simp[Abbr`tm1`,Abbr`tm2`,termsem_def] >>
      simp[Abbr`vvx`,APPLY_UPDATE_THM,Abbr`f`] >>
      simp[Abbr`vv`,Abbr`s`,UPDATE_LIST_THM,APPLY_UPDATE_THM] >>
      qspecl_then[`sigof lca_ctxt`,`b0`,`tyin`]mp_tac termsem_INST >>
      simp[] ) >>
    simp[Abbr`tm1`,Abbr`tm2`] >>
    qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i vvx (Comb (Comb (Const (strlit"IN") ty0) tm1) tm2) = True ⇔ R` >>
    qspecl_then[`i`,`vvx`,`ty0`,`tm1`,`tm2`,`Tyvar(strlit"B")`]mp_tac(UNDISCH termsem_IN) >>
    simp[] >>
    disch_then(qspecl_then[
      `Comb(Var(strlit"f")(Fun(Tyvar(strlit"C"))ty))(Var f (Tyvar(strlit"C")))`,
      `Var(strlit"t")(Fun ty Bool)`,
      `[(ty,Tyvar(strlit"C"));(Tyvar(strlit"B"),ty)]`]mp_tac) >>
    discharge_hyps_keep >- (
      unabbrev_all_tac >>
      conj_tac >- ( CONV_TAC(RAND_CONV EVAL_INST) >> REFL_TAC) >>
      conj_tac >- ( CONV_TAC(RAND_CONV EVAL_INST) >> REFL_TAC) >>
      conj_tac >- (simp[REV_ASSOCD]) >>
      conj_tac >- (simp[type_ok_def]) >>
      conj_tac >- ( CONV_TAC EVAL_term_ok) >>
      conj_tac >- ( CONV_TAC EVAL_term_ok) >>
      conj_tac >- ( CONV_TAC(LAND_CONV EVAL_typeof) >> REFL_TAC) >>
      ( CONV_TAC(LAND_CONV EVAL_typeof) >> REFL_TAC) ) >>
    pop_assum(fn th =>
      map_every (SUBST1_TAC o SYM) (List.take(CONJUNCTS th,2))) >>
    simp[] >> disch_then kall_tac >>
    simp[boolean_eq_true,Abbr`R`] >>
    simp[Abbr`tm1`,Abbr`tm2`,termsem_def] >>
    simp[Abbr`vvx`,APPLY_UPDATE_THM,Abbr`f`] >>
    simp[Abbr`vv`,Abbr`s`,UPDATE_LIST_THM,APPLY_UPDATE_THM] >>
    qspecl_then[`sigof lca_ctxt`,`c0`,`tyin`]mp_tac termsem_INST >>
    simp[] >> disch_then kall_tac >>
    qspecl_then[`sigof lca_ctxt`,`a0`,`tyin`]mp_tac termsem_INST >>
    simp[] >> disch_then kall_tac >>
    EQ_TAC >> simp[] >> strip_tac >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    match_mp_tac(UNDISCH termsem_typesem_matchable) >>
    simp[] >>
    qexists_tac`sigof lca_ctxt` >>
    simp[] >>
    fs[models_def,is_std_interpretation_def] >>
    imp_res_tac typesem_Fun >> simp[] >>
    simp[typesem_def,Abbr`vvv`] ) >>
  simp[Abbr`tm1`,Abbr`tm2`,IN_DEF,ext_def] >>
  qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i vv (Forall x y z) = True ⇔ R` >>
  qspecl_then[`sigof lca_ctxt`,`i`,`vv`,`x`,`y`,`z`]mp_tac (UNDISCH termsem_forall) >>
  discharge_hyps >- (
    imp_res_tac models_lca_ctxt_has_bool_interpretation >>
    assume_tac lca_is_bool_sig >>
    fs[models_def,is_std_interpretation_def,is_bool_interpretation_def,is_bool_sig_def] >>
    unabbrev_all_tac >>
    conj_tac >- (CONV_TAC EVAL_type_ok) >>
    conj_tac >- (CONV_TAC EVAL_term_ok) >>
    (CONV_TAC (LAND_CONV EVAL_typeof) >> REFL_TAC)) >>
  simp[] >> disch_then kall_tac >>
  simp[boolean_eq_true,Abbr`R`] >>
  simp[Abbr`x`,Abbr`y`,typesem_def] >>
  simp[GSYM AND_IMP_INTRO,Once RIGHT_FORALL_IMP_THM] >>
  AP_TERM_TAC >> simp[FUN_EQ_THM] >> gen_tac >>
  qmatch_abbrev_tac`A ⇒ B ⇔ A' ⇒ B'` >>
  `A = A' ∧ (A ⇒ (B = B'))` suffices_by metis_tac[] >>
  map_every qunabbrev_tac[`A`,`A'`,`B`,`B'`] >>
  conj_tac >- ( simp[Abbr`vv`,Abbr`vvv`] ) >>
  strip_tac >>
  simp[Abbr`z`] >>
  qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i vvx (Forall q y z) = True ⇔ R` >>
  qspecl_then[`sigof lca_ctxt`,`i`,`vvx`,`q`,`y`,`z`]mp_tac (UNDISCH termsem_forall) >>
  discharge_hyps >- (
    conj_tac >- (
      simp[Abbr`vvx`] >>
      match_mp_tac is_valuation_extend >>
      simp[Abbr`y`,typesem_def,APPLY_UPDATE_THM] ) >>
    imp_res_tac models_lca_ctxt_has_bool_interpretation >>
    assume_tac lca_is_bool_sig >>
    fs[models_def,is_std_interpretation_def,is_bool_interpretation_def,is_bool_sig_def] >>
    unabbrev_all_tac >>
    conj_tac >- (CONV_TAC EVAL_type_ok) >>
    conj_tac >- (CONV_TAC EVAL_term_ok) >>
    (CONV_TAC (LAND_CONV EVAL_typeof) >> REFL_TAC)) >>
  simp[] >> disch_then kall_tac >>
  simp[boolean_eq_true,Abbr`R`] >>
  simp[Abbr`q`,Abbr`y`,typesem_def] >>
  CONV_TAC(RAND_CONV(QUANT_CONV(REWR_CONV(PROVE[]``(a ==> b ==> c) <=> (b ==> a ==> c)``)))) >>
  simp[Abbr`vvx`] >>
  AP_TERM_TAC >> simp[FUN_EQ_THM] >> gen_tac >>
  qmatch_abbrev_tac`A ⇒ B ⇔ A' ⇒ B'` >>
  `A = A' ∧ (A ⇒ (B = B'))` suffices_by metis_tac[] >>
  map_every qunabbrev_tac[`A`,`A'`,`B`,`B'`] >>
  conj_tac >- ( simp[Abbr`vv`,Abbr`vvv`] ) >>
  strip_tac >>
  simp[Abbr`z`] >>
  Q.PAT_ABBREV_TAC`vu:'U valuation = X Y` >>
  `is_valuation (tysof lca_ctxt) (tyaof i) vu` by (
    simp[Abbr`vu`] >>
    match_mp_tac is_valuation_extend >>
    simp[typesem_def] >>
    match_mp_tac is_valuation_extend >>
    simp[typesem_def] ) >>
  use_termsem_implies >>
  simp[boolean_eq_true] >>
  simp[Once AND_IMP_INTRO] >>
  qmatch_abbrev_tac`(A ⇒ B) ⇔ (A' ⇒ B')` >>
  `A = A' ∧ (A' ⇒ (B = B'))` suffices_by metis_tac[] >>
  map_every qunabbrev_tac[`A`,`A'`,`B`,`B'`] >>
  conj_tac >- (
    use_termsem_and >>
    simp[boolean_eq_true] >>
    qmatch_abbrev_tac`A ∧ B ⇔ A' ∧ B'` >>
    `(A ⇔ A') ∧ (B ⇔ B')` suffices_by rw[] >>
    map_every qunabbrev_tac[`A`,`A'`,`B`,`B'`] >>
    conj_tac >- (
      use_termsem_IN_simple >>
      simp[boolean_eq_true,termsem_def] >>
      simp[Abbr`vu`,APPLY_UPDATE_THM] >>
      simp[Abbr`vv`,Abbr`s`,UPDATE_LIST_THM,APPLY_UPDATE_THM] >>
      qspecl_then[`sigof lca_ctxt`,`b0`,`tyin`]mp_tac termsem_INST >>
      simp[] ) >>
    use_termsem_IN_simple >>
    simp[boolean_eq_true,termsem_def] >>
    simp[Abbr`vu`,APPLY_UPDATE_THM] >>
    simp[Abbr`vv`,Abbr`s`,UPDATE_LIST_THM,APPLY_UPDATE_THM] >>
    qspecl_then[`sigof lca_ctxt`,`b0`,`tyin`]mp_tac termsem_INST >>
    simp[] ) >>
  strip_tac >>
  use_termsem_implies >>
  simp[boolean_eq_true] >>
  simp[equation_intro] >>
  qmatch_abbrev_tac`(A ⇒ B) ⇔ (A' ⇒ B')` >>
  `A = A' ∧ (B = B')` suffices_by metis_tac[] >>
  map_every qunabbrev_tac[`A`,`A'`,`B`,`B'`] >>
  conj_tac >- (
    use_termsem_equation >>
    simp[boolean_eq_true,termsem_def] >>
    simp[Abbr`vu`,APPLY_UPDATE_THM] >>
    simp[Abbr`vv`,Abbr`s`,UPDATE_LIST_THM,APPLY_UPDATE_THM] >>
    qspecl_then[`sigof lca_ctxt`,`a0`,`tyin`]mp_tac termsem_INST >> simp[]) >>
  use_termsem_equation >>
  simp[boolean_eq_true,termsem_def,Abbr`vu`,APPLY_UPDATE_THM])

fun use_termsem_INJ f tyinq (g as (asl,w)) =
  let
    val tm = find_term(can(match_term``termsem s i v (Comb (Comb (Comb (Const (strlit"INJ") ty) a) b) c)``)) w
    val (_,args) = strip_comb tm
    val app = el 5 args
    val ty = app |> rator |> rand |> rator |> rand |> rator |> rand |> rand
    val a = app |> rator |> rand |> rator |> rand |> rand
    val b = app |> rator |> rand |> rand
    val c = app |> rand
    val th =
      UNDISCH termsem_INJ
      |> SPECL[el 3 args, el 4 args, ty, a, b, c]
  in
    mp_tac th >> simp[] >>
    disch_then(qspec_then tyinq mp_tac o SPECL(map f [a, b, c])) >>
    discharge_hyps_keep >- (
      conj_tac >- (CONV_TAC(RAND_CONV(EVAL_INST)) >> REFL_TAC) >>
      conj_tac >- (CONV_TAC(RAND_CONV(EVAL_INST)) >> REFL_TAC) >>
      conj_tac >- (CONV_TAC(RAND_CONV EVAL_INST) >> REFL_TAC) >>
      conj_tac >- (simp[REV_ASSOCD]) >>
      conj_tac >- (simp[] >> rpt conj_tac >> CONV_TAC(EVAL_type_ok)) >>
      conj_tac >- (CONV_TAC(EVAL_term_ok)) >>
      conj_tac >- (CONV_TAC(EVAL_term_ok)) >>
      conj_tac >- (CONV_TAC(EVAL_term_ok)) >>
      conj_tac >- (CONV_TAC(LAND_CONV(EVAL_typeof))>>REFL_TAC) >>
      conj_tac >- (CONV_TAC(LAND_CONV(EVAL_typeof))>>REFL_TAC) >>
      (CONV_TAC(LAND_CONV(EVAL_typeof))>>REFL_TAC)) >>
    pop_assum(fn th =>
      map_every (SUBST1_TAC o SYM) (List.take((CONJUNCTS th),5))) >>
    disch_then(CHANGED_TAC o SUBST1_TAC)
  end g

val termsem_cardleq = store_thm("termsem_cardleq",
  ``is_set_theory ^mem ⇒
    ∀i v ty1 a b tya tyb a0 b0 tyin.
    i models thyof lca_ctxt ∧
    is_valuation (tysof lca_ctxt) (tyaof i) v ∧
    a = INST tyin a0 ∧
    b = INST tyin b0 ∧
    ty1 = Fun (Fun tya Bool) (Fun (Fun tyb Bool) Bool) ∧
    tya = REV_ASSOCD(Tyvar(strlit"A"))tyin(Tyvar(strlit"A")) ∧
    tyb = REV_ASSOCD(Tyvar(strlit"B"))tyin(Tyvar(strlit"B")) ∧
    EVERY (type_ok (tysof lca_ctxt)) (MAP FST tyin) ∧
    term_ok (sigof lca_ctxt) a0 ∧
    term_ok (sigof lca_ctxt) b0 ∧
    typeof a0 = (Fun (Tyvar(strlit"A")) Bool) ∧
    typeof b0 = (Fun (Tyvar(strlit"B")) Bool)
    ⇒
    termsem (tmsof lca_ctxt) i v
      (Comb (Comb (Const (strlit "cardleq") ty1) a) b) =
      Boolean (ext(typesem (tyaof i) (tyvof v) tya) ∩ Holds (termsem (tmsof lca_ctxt) i v a) ≼
               ext(typesem (tyaof i) (tyvof v) tyb) ∩ Holds (termsem (tmsof lca_ctxt) i v b))``,
  rpt strip_tac >>
  qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i v (Comb (Comb (Const g ty) a) b) = R` >>
  qspecl_then[`lca_ctxt`,`i`,`v`,`g`,`ty`,`tyin`,`a`,`b`]mp_tac (UNDISCH termsem_comb2_ax) >>
  qunabbrev_tac`g` >>
  CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(LAND_CONV EVAL)))) >>
  qpat_assum`tya = X`Abbrev_intro_tac >>
  qpat_assum`tyb = X`Abbrev_intro_tac >>
  qpat_assum`a = X`Abbrev_intro_tac >>
  qpat_assum`b = X`Abbrev_intro_tac >>
  simp[FLOOKUP_cardleq,Abbr`ty`] >>
  disch_then(qspecl_then[`a0`,`b0`]mp_tac) >>
  simp[theory_ok_lca] >>
  discharge_hyps >- metis_tac[WELLTYPED,term_ok_welltyped] >>
  disch_then SUBST1_TAC >>
  Q.PAT_ABBREV_TAC`s = (a0,Var X Y)::Z` >>
  Q.PAT_ABBREV_TAC`tm = Exists X Y Z` >>
  `term_ok (sigof lca_ctxt) tm` by (
    qunabbrev_tac`tm` >>
    CONV_TAC(EVAL_term_ok) ) >>
  `term_ok (sigof lca_ctxt) (VSUBST s tm)` by (
    match_mp_tac term_ok_VSUBST >>
    simp[Abbr`s`] >> ntac 2 (pop_assum kall_tac) >> rw[] >>
    metis_tac[WELLTYPED,term_ok_welltyped]) >>
  qspecl_then[`sigof lca_ctxt`,`VSUBST s tm`,`tyin`]mp_tac termsem_INST >>
  simp[] >> disch_then kall_tac >>
  Q.PAT_ABBREV_TAC`vvv:'U valuation = X Y` >>
  `is_valuation (tysof lca_ctxt) (tyaof i) vvv` by (
    qpat_assum`term_ok X tm`kall_tac >>
    qpat_assum`term_ok X (VSUBST A Y)`kall_tac >>
    qunabbrev_tac`tm` >>
    simp[Abbr`vvv`] >>
    fs[is_valuation_def,is_type_valuation_def,is_term_valuation_def] >>
    conj_tac >- (
      gen_tac >>
      match_mp_tac(UNDISCH typesem_inhabited) >>
      qexists_tac`tysof lca_ctxt` >>
      simp[is_type_valuation_def] >>
      fs[models_def,is_interpretation_def] >>
      simp[holSyntaxLibTheory.REV_ASSOCD_ALOOKUP] >>
      BasicProvers.CASE_TAC >> simp[type_ok_def] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[EVERY_MEM,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
      metis_tac[]) >>
     qx_genl_tac[`z`,`ty`] >> strip_tac >>
     first_x_assum(qspecl_then[`z`,`TYPE_SUBST tyin ty`]mp_tac) >>
     simp[type_ok_TYPE_SUBST,Once typesem_TYPE_SUBST] ) >>
  qspecl_then[`tm`,`s`]mp_tac termsem_VSUBST >>
  discharge_hyps >- (
    imp_res_tac term_ok_welltyped >>
    simp[Abbr`s`] >> ntac 9 (pop_assum kall_tac) >> rw[] >>
    metis_tac[WELLTYPED,term_ok_welltyped]) >>
  simp[] >> disch_then kall_tac >>
  Q.PAT_ABBREV_TAC`vv:'U valuation = X Y` >>
  `is_valuation (tysof lca_ctxt) (tyaof i) vv` by (
    qpat_assum`term_ok X tm`kall_tac >>
    qpat_assum`term_ok X (VSUBST A Y)`kall_tac >>
    qunabbrev_tac`tm` >>
    simp[Abbr`vv`,Abbr`s`,UPDATE_LIST_THM] >>
    match_mp_tac is_valuation_extend >>
    reverse conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem_matchable) >>
      qexists_tac`sigof lca_ctxt`>>simp[] >>
      fs[models_def,is_std_interpretation_def] ) >>
    match_mp_tac is_valuation_extend >>
    reverse conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem_matchable) >>
      qexists_tac`sigof lca_ctxt`>>simp[] >>
      fs[models_def,is_std_interpretation_def] ) >>
    simp[] ) >>
  simp[Abbr`tm`] >>
  qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i vv (Exists f ty bd) = R` >>
  qspecl_then[`sigof lca_ctxt`,`i`,`vv`,`f`,`ty`,`bd`]mp_tac (UNDISCH termsem_exists) >>
  discharge_hyps >- (
    assume_tac lca_is_bool_sig >>
    imp_res_tac models_lca_ctxt_has_bool_interpretation >>
    fs[models_def,is_bool_sig_def,is_bool_interpretation_def] >>
    unabbrev_all_tac >>
    conj_tac >- (CONV_TAC EVAL_type_ok) >>
    conj_tac >- (CONV_TAC EVAL_term_ok) >>
    CONV_TAC(LAND_CONV EVAL_typeof) >> REFL_TAC ) >>
  simp[] >> disch_then kall_tac >>
  simp[Abbr`R`,cardinalTheory.cardleq_def] >>
  AP_TERM_TAC >>
  EQ_TAC >- (
    strip_tac >>
    qmatch_assum_abbrev_tac`termsem (tmsof lca_ctxt) i vvx bd = True` >>
    qexists_tac`$' x` >>
    qpat_assum`X:'U = True`mp_tac >>
    simp[Abbr`bd`] >>
    qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i vvx (Comb(Comb(Comb(Const(strlit"INJ")ty0)aa)bb)cc) = True ⇒ R` >>
    qspecl_then[`i`,`vvx`,`ty0`,`aa`,`bb`,`cc`]mp_tac(UNDISCH termsem_INJ) >>
    simp[] >>
    disch_then(qspecl_then[`aa`,`bb`,`cc`,`[]`]mp_tac) >>
    discharge_hyps_keep >- (
      conj_tac >- (
        simp[Abbr`vvx`] >>
        match_mp_tac is_valuation_extend >>
        simp[] ) >>
      unabbrev_all_tac >>
      conj_tac >- (CONV_TAC(RAND_CONV EVAL_INST) >> REFL_TAC) >>
      conj_tac >- (CONV_TAC(RAND_CONV EVAL_INST) >> REFL_TAC) >>
      conj_tac >- (CONV_TAC(RAND_CONV EVAL_INST) >> REFL_TAC) >>
      conj_tac >- (simp[REV_ASSOCD]) >>
      conj_tac >- (simp[]) >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      conj_tac >- (CONV_TAC(LAND_CONV EVAL_typeof)>>REFL_TAC) >>
      conj_tac >- (CONV_TAC(LAND_CONV EVAL_typeof)>>REFL_TAC) >>
      (CONV_TAC(LAND_CONV EVAL_typeof)>>REFL_TAC)) >>
    pop_assum(fn th =>
      assume_tac(CONJUNCT1 th) >>
      map_every (SUBST1_TAC o SYM) (List.take(tl(CONJUNCTS th),4))) >>
    simp[] >> disch_then kall_tac >>
    simp[boolean_eq_true,Abbr`R`] >>
    simp[REV_ASSOCD,typesem_def] >>
    simp[Abbr`aa`,Abbr`bb`,Abbr`cc`,termsem_def] >>
    simp[Abbr`vvx`,APPLY_UPDATE_THM,Abbr`f`] >>
    simp[Abbr`vv`,Abbr`s`,UPDATE_LIST_THM,APPLY_UPDATE_THM] >>
    qspecl_then[`sigof lca_ctxt`,`a0`,`tyin`]mp_tac termsem_INST >>
    simp[] >> disch_then kall_tac >>
    qspecl_then[`sigof lca_ctxt`,`b0`,`tyin`]mp_tac termsem_INST >>
    simp[] >> disch_then kall_tac >>
    qmatch_assum_abbrev_tac`Abbrev(vvv=(vvy,vvz))` >>
    `tyvof vvv=vvy`by simp[Abbr`vvv`] >>
    pop_assum SUBST1_TAC >>
    simp[Abbr`vvy`] ) >>
  disch_then(qx_choose_then`g`strip_assume_tac) >>
  qexists_tac`Abstract (typesem (tyaof i) (tyvof v) tya) (typesem (tyaof i) (tyvof v) tyb)
                (λm. if Holds (termsem (tmsof lca_ctxt) i v a) m then g m
                     else @x. x <: typesem (tyaof i) (tyvof v) tyb)` >>
  conj_asm1_tac >- (
    simp[Abbr`ty`] >>
    fs[models_def,is_std_interpretation_def] >>
    imp_res_tac typesem_Fun >> simp[] >>
    simp[typesem_def] >>
    simp[Abbr`vv`,Abbr`vvv`] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    fs[INJ_DEF,IN_DEF,ext_def] >>
    gen_tac >> strip_tac >>
    IF_CASES_TAC >- PROVE_TAC[] >>
    SELECT_ELIM_TAC >> simp[] >>
    match_mp_tac(UNDISCH typesem_inhabited) >>
    qexists_tac`tysof lca_ctxt` >>
    fs[is_valuation_def,is_interpretation_def] >>
    fs[Abbr`tyb`] >>
    simp[holSyntaxLibTheory.REV_ASSOCD_ALOOKUP] >>
    BasicProvers.CASE_TAC >> simp[type_ok_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[EVERY_MEM,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[]) >>
  simp[Abbr`bd`] >>
  qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i vvx (Comb(Comb(Comb(Const(strlit"INJ")ty0)aa)bb)cc) = True` >>
  qspecl_then[`i`,`vvx`,`ty0`,`aa`,`bb`,`cc`]mp_tac(UNDISCH termsem_INJ) >>
  simp[] >>
  disch_then(qspecl_then[`aa`,`bb`,`cc`,`[]`]mp_tac) >>
  discharge_hyps_keep >- (
    conj_tac >- (
      simp[Abbr`vvx`] >>
      match_mp_tac is_valuation_extend >>
      simp[] ) >>
    unabbrev_all_tac >>
    conj_tac >- (CONV_TAC(RAND_CONV EVAL_INST) >> REFL_TAC) >>
    conj_tac >- (CONV_TAC(RAND_CONV EVAL_INST) >> REFL_TAC) >>
    conj_tac >- (CONV_TAC(RAND_CONV EVAL_INST) >> REFL_TAC) >>
    conj_tac >- (simp[REV_ASSOCD]) >>
    conj_tac >- (simp[]) >>
    conj_tac >- (CONV_TAC EVAL_term_ok) >>
    conj_tac >- (CONV_TAC EVAL_term_ok) >>
    conj_tac >- (CONV_TAC EVAL_term_ok) >>
    conj_tac >- (CONV_TAC(LAND_CONV EVAL_typeof)>>REFL_TAC) >>
    conj_tac >- (CONV_TAC(LAND_CONV EVAL_typeof)>>REFL_TAC) >>
    (CONV_TAC(LAND_CONV EVAL_typeof)>>REFL_TAC)) >>
  pop_assum(fn th =>
    assume_tac(CONJUNCT1 th) >>
    map_every (SUBST1_TAC o SYM) (List.take(tl(CONJUNCTS th),4))) >>
  simp[REV_ASSOCD] >> disch_then kall_tac >>
  simp[boolean_eq_true] >>
  simp[Abbr`aa`,Abbr`bb`,Abbr`cc`,termsem_def] >>
  simp[Abbr`vvx`,APPLY_UPDATE_THM,Abbr`f`] >>
  simp[Abbr`vv`,UPDATE_LIST_THM,APPLY_UPDATE_THM,Abbr`s`] >>
  rator_x_assum`INJ`mp_tac >>
  qspecl_then[`sigof lca_ctxt`,`a0`,`tyin`]mp_tac termsem_INST >>
  simp[] >> disch_then kall_tac >>
  qspecl_then[`sigof lca_ctxt`,`b0`,`tyin`]mp_tac termsem_INST >>
  simp[] >> disch_then kall_tac >>
  qmatch_assum_abbrev_tac`Abbrev(vvv=(vvy,vvz))` >>
  `tyvof vvv=vvy`by simp[Abbr`vvv`] >>
  pop_assum SUBST1_TAC >>
  simp[Abbr`vvy`,typesem_def] >>
  strip_tac >>
  qmatch_abbrev_tac`INJ h s1 s2` >>
  `∀x. x ∈ s1 ⇒ h x = g x` by (
    simp[Abbr`s1`,Abbr`h`,ext_def] >>
    gen_tac >> strip_tac >>
    match_mp_tac apply_abstract_matchable >>
    simp[] >> fs[IN_DEF] >>
    fs[INJ_DEF,ext_def,Abbr`s2`] >>
    fs[IN_DEF] ) >>
  fs[INJ_DEF])

val Holds_Abstract = store_thm("Holds_Abstract",
  ``is_set_theory ^mem ⇒ (∀z. z <: q ⇒ f z <: boolset) ⇒
    ext q ∩ Holds (Abstract q boolset f) = {a | a ∈ ext q ∧ f a = True}``,
  rw[EXTENSION,holds_def,ext_def] >>
  Cases_on`x <: q`>>rw[] >>
  rw[IN_DEF,holds_def] >>
  `Abstract q boolset f ' x = f x` by (
    match_mp_tac (apply_abstract_matchable) >>
    simp[] ) >>
  simp[])

val termsem_countable = store_thm("termsem_countable",
  ``is_set_theory ^mem ⇒
    ∀i v ty1 a b tya a0 tyin.
    i models thyof lca_ctxt ∧
    is_valuation (tysof lca_ctxt) (tyaof i) v ∧
    wf_to_inner ((to_inner Num):num->'U) ∧
    tyaof i (strlit"num") [] = range((to_inner Num):num->'U) ∧
    a = INST tyin a0 ∧
    ty1 = Fun (Fun tya Bool) Bool ∧
    tya = REV_ASSOCD(Tyvar(strlit"A"))tyin(Tyvar(strlit"A")) ∧
    EVERY (type_ok (tysof lca_ctxt)) (MAP FST tyin) ∧
    term_ok (sigof lca_ctxt) a0 ∧
    typeof a0 = (Fun (Tyvar(strlit"A")) Bool)
    ⇒
    termsem (tmsof lca_ctxt) i v
      (Comb (Const (strlit "countable") ty1) a) =
      Boolean (countable (ext(typesem (tyaof i) (tyvof v) tya) ∩ Holds (termsem (tmsof lca_ctxt) i v a)))``,
  rpt strip_tac >>
  qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i v (Comb (Const g ty) a) = R` >>
  qspecl_then[`lca_ctxt`,`i`,`v`,`g`,`ty`,`tyin`,`a`]mp_tac (UNDISCH termsem_comb1_ax) >>
  qunabbrev_tac`g` >>
  CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(LAND_CONV EVAL)))) >>
  qpat_assum`tya = X`Abbrev_intro_tac >>
  qpat_assum`a = X`Abbrev_intro_tac >>
  simp[FLOOKUP_countable,Abbr`ty`] >>
  disch_then(qspecl_then[`a0`]mp_tac) >>
  simp[theory_ok_lca] >>
  discharge_hyps >- metis_tac[WELLTYPED,term_ok_welltyped] >>
  disch_then SUBST1_TAC >>
  Q.PAT_ABBREV_TAC`s = (a0,Var X Y)::Z` >>
  Q.PAT_ABBREV_TAC`tm = Exists X Y Z` >>
  `term_ok (sigof lca_ctxt) tm` by (
    qunabbrev_tac`tm` >>
    CONV_TAC(EVAL_term_ok) ) >>
  `term_ok (sigof lca_ctxt) (VSUBST s tm)` by (
    match_mp_tac term_ok_VSUBST >>
    simp[Abbr`s`] >> ntac 2 (pop_assum kall_tac) >> rw[] >>
    metis_tac[WELLTYPED,term_ok_welltyped]) >>
  qspecl_then[`sigof lca_ctxt`,`VSUBST s tm`,`tyin`]mp_tac termsem_INST >>
  simp[] >> disch_then kall_tac >>
  Q.PAT_ABBREV_TAC`vvv:'U valuation = X Y` >>
  `is_valuation (tysof lca_ctxt) (tyaof i) vvv` by (
    qpat_assum`term_ok X tm`kall_tac >>
    qpat_assum`term_ok X (VSUBST A Y)`kall_tac >>
    qunabbrev_tac`tm` >>
    simp[Abbr`vvv`] >>
    fs[is_valuation_def,is_type_valuation_def,is_term_valuation_def] >>
    conj_tac >- (
      gen_tac >>
      match_mp_tac(UNDISCH typesem_inhabited) >>
      qexists_tac`tysof lca_ctxt` >>
      simp[is_type_valuation_def] >>
      fs[models_def,is_interpretation_def] >>
      simp[holSyntaxLibTheory.REV_ASSOCD_ALOOKUP] >>
      BasicProvers.CASE_TAC >> simp[type_ok_def] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[EVERY_MEM,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
      metis_tac[]) >>
     qx_genl_tac[`z`,`ty`] >> strip_tac >>
     first_x_assum(qspecl_then[`z`,`TYPE_SUBST tyin ty`]mp_tac) >>
     simp[type_ok_TYPE_SUBST,Once typesem_TYPE_SUBST] ) >>
  qspecl_then[`tm`,`s`]mp_tac termsem_VSUBST >>
  discharge_hyps >- (
    imp_res_tac term_ok_welltyped >>
    simp[Abbr`s`] >> ntac 9 (pop_assum kall_tac) >> rw[] >>
    metis_tac[WELLTYPED,term_ok_welltyped]) >>
  simp[] >> disch_then kall_tac >>
  Q.PAT_ABBREV_TAC`vv:'U valuation = X Y` >>
  `is_valuation (tysof lca_ctxt) (tyaof i) vv` by (
    qpat_assum`term_ok X tm`kall_tac >>
    qpat_assum`term_ok X (VSUBST A Y)`kall_tac >>
    qunabbrev_tac`tm` >>
    simp[Abbr`vv`,Abbr`s`,UPDATE_LIST_THM] >>
    match_mp_tac is_valuation_extend >>
    reverse conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem_matchable) >>
      qexists_tac`sigof lca_ctxt`>>simp[] >>
      fs[models_def,is_std_interpretation_def] ) >>
    simp[] ) >>
  simp[Abbr`tm`] >>
  use_termsem_exists >>
  simp[boolean_eq_true,Abbr`R`] >>
  simp[countable_def] >>
  AP_TERM_TAC >>
  EQ_TAC >- (
    strip_tac >>
    qmatch_assum_abbrev_tac`termsem (tmsof lca_ctxt) i vvx bd = True` >>
    qexists_tac`finv(to_inner Num) o $' x` >>
    qpat_assum`X:'U = True`mp_tac >>
    simp[Abbr`bd`] >>
    `is_valuation (tysof lca_ctxt) (tyaof i) vvx` by (
      simp[Abbr`vvx`] >>
      match_mp_tac is_valuation_extend >> simp[] ) >>
    use_termsem_INJ
      (replace_term``Num````Tyvar(strlit"B")``)
      `[(Num,Tyvar(strlit"B"))]` >>
    simp[boolean_eq_true] >>
    qspecl_then[`i`,`vvx`,`Num`]mp_tac(UNDISCH termsem_UNIV) >>
    discharge_hyps >- ( simp[] >> CONV_TAC(EVAL_type_ok) ) >>
    disch_then(CHANGED_TAC o SUBST1_TAC) >>
    simp[Holds_Abstract,mem_boolset] >>
    simp[termsem_def,typesem_def] >>
    simp[Abbr`vvx`,APPLY_UPDATE_THM] >>
    simp[Abbr`vv`,APPLY_UPDATE_THM,Abbr`s`,UPDATE_LIST_THM] >>
    qspecl_then[`sigof lca_ctxt`,`a0`,`tyin`]mp_tac termsem_INST >>
    simp[] >> disch_then kall_tac >>
    qmatch_assum_abbrev_tac`Abbrev(vvv=(vvy,vvz))` >>
    `tyvof vvv=vvy`by simp[Abbr`vvv`] >>
    pop_assum SUBST1_TAC >>
    simp[Abbr`vvy`] >>
    strip_tac >>
    match_mp_tac INJ_COMPOSE >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp[INJ_DEF,ext_def] >>
    metis_tac[wf_to_inner_finv_right]) >>
  disch_then(qx_choose_then`g`strip_assume_tac) >>
  qexists_tac`Abstract (typesem (tyaof i) (tyvof v) tya) (tyaof i (strlit"num")[])
                (λm. (* if Holds (termsem (tmsof lca_ctxt) i v a) m then *) to_inner Num (g m)
                     (* else  *) )` >>
  conj_asm1_tac >- (
    simp[] >>
    fs[models_def,is_std_interpretation_def] >>
    imp_res_tac typesem_Fun >> simp[] >>
    simp[typesem_def] >>
    simp[Abbr`vv`,Abbr`vvv`] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[] >>  metis_tac[wf_to_inner_range_thm] ) >>
  Q.PAT_ABBREV_TAC`vvx:'U valuation = X Y` >>
  `is_valuation (tysof lca_ctxt) (tyaof i) vvx` by (
    simp[Abbr`vvx`] >>
    match_mp_tac is_valuation_extend >> simp[] >>
    rfs[]) >>
  use_termsem_INJ
    (replace_term``Num````Tyvar(strlit"B")``)
    `[(Num,Tyvar(strlit"B"))]` >>
  simp[boolean_eq_true] >>
  qspecl_then[`i`,`vvx`,`Num`]mp_tac(UNDISCH termsem_UNIV) >>
  discharge_hyps >- ( simp[] >> CONV_TAC(EVAL_type_ok) ) >>
  disch_then(CHANGED_TAC o SUBST1_TAC) >>
  simp[Holds_Abstract,mem_boolset] >>
  simp[termsem_def,typesem_def] >>
  simp[Abbr`vvx`,APPLY_UPDATE_THM] >>
  simp[Abbr`vv`,APPLY_UPDATE_THM,Abbr`s`,UPDATE_LIST_THM] >>
  qmatch_assum_abbrev_tac`Abbrev(vvv=(vvy,vvz))` >>
  `tyvof vvv=vvy`by simp[Abbr`vvv`] >>
  pop_assum SUBST1_TAC >>
  simp[Abbr`vvy`] >>
  rator_x_assum`INJ`mp_tac >>
  qspecl_then[`sigof lca_ctxt`,`a0`,`tyin`]mp_tac termsem_INST >>
  simp[] >> disch_then kall_tac >>
  simp[INJ_DEF,ext_def] >>
  simp[IN_DEF] >> strip_tac >>
  conj_tac >- (
    rw[] >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    first_assum(match_exists_tac o concl) >> rw[] >>
    match_mp_tac (UNDISCH abstract_in_funspace_matchable) >>
    simp[] >> metis_tac[wf_to_inner_range_thm] ) >>
  rw[] >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  simp[] >>
  pop_assum mp_tac >>
  use_apply_abstract >> simp[] >>
  discharge_hyps >- metis_tac[wf_to_inner_range_thm] >>
  disch_then SUBST1_TAC >>
  use_apply_abstract >> simp[] >>
  discharge_hyps >- metis_tac[wf_to_inner_range_thm] >>
  disch_then SUBST1_TAC >>
  metis_tac[wf_to_inner_finv_left])

val termsem_LESS = store_thm("termsem_LESS",
  ``is_set_theory ^mem ⇒
    ∀i v a b ty1.
    i models thyof lca_ctxt ∧
    is_valuation (tysof lca_ctxt) (tyaof i) v ∧
    wf_to_inner ((to_inner Num):num->'U) ∧
    tyaof i (strlit"num") [] = range((to_inner Num):num->'U) ∧
    ty1 = Fun Num (Fun Num Bool) ∧
    term_ok (sigof lca_ctxt) a ∧
    term_ok (sigof lca_ctxt) b ∧
    typeof a = Num ∧
    typeof b = Num
    ⇒
    termsem (tmsof lca_ctxt) i v
      (Comb (Comb (Const (strlit "<") ty1) a) b) =
      Boolean (prim_rec$<
                (finv (to_inner Num) (termsem (tmsof lca_ctxt) i v a))
                (finv (to_inner Num) (termsem (tmsof lca_ctxt) i v b)))``,
  rpt strip_tac >>
  qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i v (Comb (Comb (Const g ty) a) b) = R` >>
  qspecl_then[`lca_ctxt`,`i`,`v`,`g`,`ty`,`[]`,`a`,`b`]mp_tac (UNDISCH termsem_comb2_ax) >>
  qunabbrev_tac`g` >>
  CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(LAND_CONV EVAL)))) >>
  simp[FLOOKUP_LESS,Abbr`ty`] >>
  disch_then(qspecl_then[`a`,`b`]mp_tac) >>
  simp[theory_ok_lca] >>
  discharge_hyps_keep >- metis_tac[WELLTYPED,term_ok_welltyped,INST_nil] >>
  pop_assum(fn th => map_every (SUBST1_TAC o SYM) (List.drop(CONJUNCTS th,2))) >>
  disch_then SUBST1_TAC >>
  Q.PAT_ABBREV_TAC`s = (a,Var X Y)::Z` >>
  Q.PAT_ABBREV_TAC`tm = Exists X Y Z` >>
  `term_ok (sigof lca_ctxt) tm` by (
    qunabbrev_tac`tm` >>
    CONV_TAC(EVAL_term_ok) ) >>
  `term_ok (sigof lca_ctxt) (VSUBST s tm)` by (
    match_mp_tac term_ok_VSUBST >>
    simp[Abbr`s`] >> ntac 2 (pop_assum kall_tac) >> rw[] >>
    metis_tac[WELLTYPED,term_ok_welltyped]) >>
  `INST [] (VSUBST s tm) = VSUBST s tm` by metis_tac[term_ok_welltyped,INST_nil] >>
  pop_assum SUBST1_TAC >>
  qspecl_then[`tm`,`s`]mp_tac termsem_VSUBST >>
  discharge_hyps >- (
    imp_res_tac term_ok_welltyped >>
    simp[Abbr`s`] >> ntac 8 (pop_assum kall_tac) >> rw[] >>
    metis_tac[WELLTYPED,term_ok_welltyped]) >>
  simp[] >> disch_then kall_tac >>
  Q.PAT_ABBREV_TAC`vv:'U valuation = X Y` >>
  `is_valuation (tysof lca_ctxt) (tyaof i) vv` by (
    qpat_assum`term_ok X tm`kall_tac >>
    qpat_assum`term_ok X (VSUBST A Y)`kall_tac >>
    qunabbrev_tac`tm` >>
    simp[Abbr`vv`,Abbr`s`,UPDATE_LIST_THM] >>
    match_mp_tac is_valuation_extend >>
    reverse conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem_matchable) >>
      qexists_tac`sigof lca_ctxt`>>simp[] >>
      fs[models_def,is_std_interpretation_def] ) >>
    match_mp_tac is_valuation_extend >>
    reverse conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem_matchable) >>
      qexists_tac`sigof lca_ctxt`>>simp[] >>
      fs[models_def,is_std_interpretation_def] ) >>
    simp[] ) >>
  simp[Abbr`tm`] >>
  use_termsem_exists >>
  simp[Abbr`R`,prim_recTheory.LESS_DEF] >>
  AP_TERM_TAC >>
  qho_match_abbrev_tac`(∃x. P x ∧ Q x) ⇔ (∃y. B y)` >>
  qho_match_abbrev_tac`(∃x. A x) ⇔ (∃y. B y)` >>
  map_every qunabbrev_tac[`P`,`Q`] >>
  `∀x. A (Abstract (tyaof i (strlit"num") []) boolset (λm. Boolean (x (finv (to_inner Num) m)))) ⇔ B x`
  suffices_by (
    disch_then(mp_tac o GSYM) >> simp[] >>
    disch_then kall_tac >>
    simp[EQ_IMP_THM,PULL_EXISTS] >>
    reverse conj_tac >- metis_tac[] >>
    gen_tac >>
    simp[Abbr`A`] >> strip_tac >>
    fs[models_def,is_std_interpretation_def] >>
    imp_res_tac typesem_Fun >> fs[] >>
    imp_res_tac (UNDISCH in_funspace_abstract) >>
    qexists_tac`finv bool_to_inner o f o to_inner Num` >>
    Q.PAT_ABBREV_TAC`x' = Abstract X Y Z` >>
    `x' = x` suffices_by rw[] >>
    qunabbrev_tac`x'` >> simp[] >>
    simp[Once typesem_def] >>
    imp_res_tac typesem_Bool >> simp[] >>
    match_mp_tac (UNDISCH abstract_eq) >>
    simp[boolean_in_boolset] >> fs[] >>
    gen_tac >> strip_tac >>
    conj_tac >- (
      first_x_assum match_mp_tac >>
      simp[typesem_def] ) >>
    imp_res_tac wf_to_inner_finv_right >>
    simp[] >>
    simp[GSYM bool_to_inner_def] >>
    match_mp_tac(MP_CANON wf_to_inner_finv_right) >>
    simp[range_bool_to_inner,wf_to_inner_bool_to_inner] >>
    first_x_assum match_mp_tac >>
    simp[typesem_def] ) >>
  simp[Abbr`A`,Abbr`B`] >>
  qx_gen_tac`P` >>
  qmatch_abbrev_tac`A ∧ B ⇔ C` >>
  `A` by (
    simp[Abbr`A`,Abbr`B`,Abbr`C`] >>
    fs[models_def,is_std_interpretation_def] >>
    imp_res_tac typesem_Fun >>
    imp_res_tac typesem_Bool >>
    simp[] >>
    match_mp_tac (UNDISCH abstract_in_funspace_matchable) >>
    simp[boolean_in_boolset] >>
    simp[typesem_def] ) >>
  simp[] >> qunabbrev_tac`A` >>
  simp[Abbr`B`,Abbr`C`] >>
  Q.PAT_ABBREV_TAC`vvx:'U valuation = X Y` >>
  `is_valuation (tysof lca_ctxt) (tyaof i) vvx` by (
    simp[Abbr`vvx`] >> match_mp_tac is_valuation_extend >> simp[] ) >>
  use_termsem_and >>
  simp[boolean_eq_true] >>
  qmatch_abbrev_tac`A ∧ B ⇔ A' ∧ B'` >>
  rator_x_assum`term_ok`kall_tac >>
  rator_x_assum`term_ok`kall_tac >>
  `A = A' ∧ B = B'` suffices_by metis_tac[] >>
  map_every qunabbrev_tac[`A`,`A'`,`B`,`B'`] >>
  conj_tac >- (
    use_termsem_forall >>
    simp[boolean_eq_true] >>
    cheat ) >>
  use_termsem_and >>
  simp[boolean_eq_true] >>
  qmatch_abbrev_tac`A ∧ B ⇔ A' ∧ B'` >>
  `A = A' ∧ B = B'` suffices_by metis_tac[] >>
  map_every qunabbrev_tac[`A`,`A'`,`B`,`B'`] >>
  conj_tac >- (
    simp[termsem_def] >>
    simp[Abbr`vvx`,APPLY_UPDATE_THM] >>
    use_apply_abstract >>
    simp[boolean_in_boolset] >>
    simp[Abbr`vv`,Abbr`s`,UPDATE_LIST_THM,APPLY_UPDATE_THM] >>
    discharge_hyps >- (
      match_mp_tac (UNDISCH termsem_typesem_matchable) >>
      qexists_tac`sigof lca_ctxt`>>simp[] >>
      fs[models_def,is_std_interpretation_def] >>
      simp[typesem_def] ) >>
    disch_then SUBST1_TAC >>
    simp[boolean_eq_true] ) >>
  cheat)

val intermediate_thm = store_thm("intermediate_thm",
  ``LCA (SUC l) (UNIV:'U set) ⇒
    ∃(mem:'U reln).
      is_set_theory mem ∧ (∃inf. is_infinite mem inf) ∧
      (i models (thyof lca_ctxt) ∧
       wf_to_inner ((to_inner Num):num->'U) ∧
       wf_to_inner ((to_inner Ind):ind->'U) ∧
       tyaof i (strlit"ind") [] = range((to_inner Ind):ind->'U) ∧
       tyaof i (strlit"num") [] = range((to_inner Num):num->'U) ∧
       tmaof i (strlit"0") [] = to_inner Num (0:num) ⇒
         ∃v.
           is_valuation (tysof lca_ctxt) (tyaof i) v ∧
           (tmvof v (strlit"l",Num) = to_inner Num l) ∧
           (termsem (tmsof lca_ctxt) i v ^LCA_l_UNIV = True))``,
  CONV_TAC(LAND_CONV(REWR_CONV LCA_alt)) >> strip_tac >>
  first_assum(qspec_then`l`mp_tac) >>
  discharge_hyps >- simp[] >>
  first_assum(SUBST1_TAC) >> strip_tac >>
  imp_res_tac strongly_inaccessible_imp >>
  qexists_tac`mem` >>
  conj_tac >- simp[] >>
  conj_tac >- PROVE_TAC[] >>
  strip_tac >>
  first_assum(qspec_then`f l`mp_tac) >>
  discharge_hyps >- simp[] >>
  disch_then(qx_choose_then`fl`strip_assume_tac) >>
  `is_type_valuation (K fl)` by (
    simp[is_type_valuation_def] >>
    `(UNIV:ind set) ≼ f l` by (
      `∀k. k < SUC l ⇒ f k ≺ f (SUC k)` by metis_tac[] >>
      pop_assum mp_tac >>
      qid_spec_tac`l` >>
      last_x_assum mp_tac >>
      rpt(pop_assum kall_tac) >>
      strip_tac >>
      Induct >> simp[] >>
      strip_tac >>
      qpat_assum`X ⇒ Y`mp_tac >>
      discharge_hyps >- (
        rw[] >>
        `k < SUC(SUC l)` by simp[] >>
        res_tac ) >>
      rw[] >>
      first_x_assum(qspec_then`l`mp_tac) >> simp[] >>
      metis_tac[cardinalTheory.cardleq_lt_trans,cardinalTheory.cardlt_lenoteq] ) >>
    spose_not_then strip_assume_tac >> fs[] >>
    rfs[cardinalTheory.cardleq_empty] ) >>
  qspecl_then[`tysof lca_ctxt`,`tyaof i`,`K fl`]mp_tac(UNDISCH constrained_term_valuation_exists) >>
  simp[] >>
  discharge_hyps >- fs[models_def,is_interpretation_def] >>
  disch_then(qspec_then`[((strlit"l",Num),to_inner Num l)]`mp_tac) >>
  discharge_hyps >- (
    simp[type_ok_Num] >>
    simp[typesem_def] >>
    metis_tac[wf_to_inner_range_thm]) >>
  simp[] >> strip_tac >>
  qexists_tac`(K fl,σ)` >>
  conj_asm1_tac >- simp[is_valuation_def] >>
  conj_tac >- simp[] >>
  qmatch_abbrev_tac`termsem (tmsof ctxt) i v (Comb (Comb (Const g ty) a) b) = True` >>
  qspecl_then[`ctxt`,`i`,`v`,`g`,`ty`,`[]`,`a`,`b`,`ty`,`a`,`b`]mp_tac(UNDISCH termsem_comb2_ax) >>
  simp[Abbr`ctxt`,theory_ok_lca,Abbr`g`,FLOOKUP_LCA] >>
  CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(LAND_CONV EVAL)))) >>
  simp[Abbr`ty`] >>
  discharge_hyps >- (
    unabbrev_all_tac >>
    conj_tac >- (CONV_TAC EVAL_term_ok) >>
    conj_tac >- (CONV_TAC EVAL_term_ok >> simp[holSyntaxLibTheory.tyvar_inst_exists]) >>
    conj_tac >- simp[Once has_type_cases] >>
    conj_tac >- simp[Once has_type_cases] >>
    conj_tac >> CONV_TAC(RAND_CONV EVAL_INST) >> REFL_TAC) >>
  disch_then SUBST1_TAC >>
  map_every qunabbrev_tac[`a`,`b`] >>
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV(EVAL_subst) THENC EVAL_INST))) >>
  use_termsem_exists >>
  simp[boolean_eq_true] >>
  qexists_tac`
    Abstract
      (range ((to_inner Num):num->'U))
      (Funspace fl boolset)
      (λm. Abstract fl boolset
             (Boolean o (f (finv (to_inner Num) m))))` >>
  conj_asm1_tac >- (
    simp[] >>
    fs[models_def,is_std_interpretation_def] >>
    imp_res_tac typesem_Fun >> simp[] >>
    match_mp_tac (UNDISCH abstract_in_funspace_matchable) >>
    simp[] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      match_mp_tac (UNDISCH abstract_in_funspace) >>
      simp[bool_to_inner_def,boolean_in_boolset] ) >>
    imp_res_tac typesem_Bool >> simp[] >>
    simp[typesem_def] >> simp[Abbr`v`] ) >>
  Q.PAT_ABBREV_TAC`vv:'U valuation = X Y` >>
  `is_valuation (tysof lca_ctxt) (tyaof i) vv` by (
    simp[Abbr`vv`] >>
    match_mp_tac is_valuation_extend >>
    simp[] ) >>
  use_termsem_and >>
  simp[boolean_eq_true] >>
  conj_tac >- (
    simp[] >>
    qmatch_abbrev_tac`termsem (tmsof s) i vv (Comb (Comb (Const (strlit"cardleq") gy) a) b) = True` >>
    qspecl_then[`i`,`vv`,`gy`,`a`,`b`]mp_tac (UNDISCH termsem_cardleq) >>
    simp[Abbr`gy`] >>
    disch_then(qspecl_then[
      `Const(strlit"UNIV")(Fun(Tyvar(strlit"A"))Bool)`,
      `Comb(Var (strlit"f") (Fun Num (Fun (Tyvar(strlit"B")) Bool)))(Const(strlit"0")Num)`,
      `[(Ind,Tyvar(strlit"A"));(Tyvar(strlit"U"),Tyvar(strlit"B"))]`]mp_tac) >>
    discharge_hyps_keep >- (
      unabbrev_all_tac >>
      conj_tac >- (CONV_TAC(RAND_CONV EVAL_INST) >> REFL_TAC) >>
      conj_tac >- (CONV_TAC(RAND_CONV EVAL_INST) >> REFL_TAC) >>
      conj_tac >- (simp[REV_ASSOCD]) >>
      conj_tac >- (simp[] >> conj_tac >> CONV_TAC EVAL_type_ok) >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      conj_tac >- (CONV_TAC (LAND_CONV EVAL_typeof) >> REFL_TAC) >>
      (CONV_TAC (LAND_CONV EVAL_typeof) >> REFL_TAC) ) >>
    pop_assum(fn th =>
      map_every (SUBST1_TAC o SYM) (List.take(CONJUNCTS th,4))) >>
    disch_then(CHANGED_TAC o SUBST1_TAC) >>
    simp[boolean_eq_true] >>
    simp[Abbr`a`] >>
    qspecl_then[`i`,`vv`,`Ind`]mp_tac(UNDISCH termsem_UNIV) >>
    discharge_hyps >- (
      simp[REV_ASSOCD,Abbr`s`] >>
      CONV_TAC EVAL_type_ok ) >>
    simp[Abbr`s`] >> disch_then kall_tac >>
    simp[Holds_Abstract,mem_boolset] >>
    simp[Once typesem_def] >>
    simp[Once typesem_def] >>
    `tyvof vv (strlit "U") = fl` by
      (simp[Abbr`vv`,Abbr`v`]) >> simp[] >>
    simp[Abbr`b`,Once termsem_def] >>
    simp[Once termsem_def,Abbr`vv`,APPLY_UPDATE_THM] >>
    Q.PAT_ABBREV_TAC`vv:'U valuation = X Y` >>
    use_apply_abstract >> simp[] >>
    discharge_hyps >- (
      conj_tac >- (
        match_mp_tac(UNDISCH termsem_typesem_matchable) >>
        simp[] >> qexists_tac`sigof lca_ctxt` >> simp[] >>
        fs[models_def,is_std_interpretation_def] >>
        conj_tac >- (CONV_TAC EVAL_term_ok) >>
        simp[typesem_def] ) >>
      match_mp_tac(UNDISCH abstract_in_funspace) >>
      simp[boolean_in_boolset,bool_to_inner_def] ) >>
    disch_then(CHANGED_TAC o SUBST1_TAC) >>
    simp[termsem_def] >>
    simp[EVAL``FLOOKUP (tmsof lca_ctxt) (strlit "0")``,identity_instance] >>
    EVAL_STRING_SORT >> simp[] >>
    simp[Holds_Abstract,bool_to_inner_def,boolean_in_boolset] >>
    simp[boolean_eq_true] >>
    imp_res_tac wf_to_inner_finv_left >>
    simp[] >>
    qmatch_abbrev_tac`a:'U set ≼ b` >>
    `(UNIV:ind set) ≈ a` by (
      simp[Abbr`a`,range_def] >>
      SELECT_ELIM_TAC >>
      conj_tac >- metis_tac[wf_to_inner_def] >>
      simp[cardinalTheory.cardeq_def,ext_def] >>
      metis_tac[] ) >>
    `(UNIV:ind set) ≼ b` suffices_by (
      metis_tac[cardinalTheory.cardleq_TRANS,cardinalTheory.cardleq_lteq,cardinalTheory.cardeq_SYM] ) >>
    `b = f 0` suffices_by rw[] >>
    simp[Abbr`b`,ext_def,EXTENSION,IN_DEF] >>
    gen_tac >> EQ_TAC >> simp[] >>
    `f 0 ⊆ f l` suffices_by (
      simp[SUBSET_DEF,IN_DEF] ) >>
    `∀k. k < SUC l ⇒ f k ⊆ f (SUC k)` by metis_tac[] >>
    pop_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    qid_spec_tac`l` >>
    Induct >> simp[] >> strip_tac >>
    qpat_assum`x ==> y`mp_tac >>
    discharge_hyps >- (
      rw[] >> first_x_assum match_mp_tac >>
      simp[] ) >> rw[] >>
    first_x_assum(qspec_then`l`mp_tac) >>
    simp[] >> metis_tac[SUBSET_TRANS] ) >>
  use_termsem_and >>
  simp[boolean_eq_true] >>
  conj_tac >- (
    simp[equation_intro] >>
    use_termsem_equation >>
    simp[boolean_eq_true] >>
    qspecl_then[`i`,`vv`,`Tyvar(strlit"U")`]mp_tac (UNDISCH termsem_UNIV) >>
    discharge_hyps >- simp[type_ok_def] >>
    disch_then(CHANGED_TAC o SUBST1_TAC) >>
    simp[termsem_def,typesem_def] >>
    simp[Abbr`vv`,APPLY_UPDATE_THM,Abbr`v`] >>
    use_apply_abstract >> simp[] >>
    discharge_hyps >- (
      conj_tac >- metis_tac[wf_to_inner_range_thm] >>
      match_mp_tac (UNDISCH abstract_in_funspace_matchable) >>
      simp[bool_to_inner_def,boolean_in_boolset] ) >>
    disch_then(CHANGED_TAC o SUBST1_TAC) >>
    match_mp_tac(UNDISCH abstract_eq) >>
    simp[bool_to_inner_def,boolean_in_boolset] >>
    simp[boolean_eq_true,mem_boolset] >>
    imp_res_tac wf_to_inner_finv_left >>
    simp[] ) >>
  use_termsem_forall >>
  simp[boolean_eq_true] >>
  gen_tac >> strip_tac >>
  Q.PAT_ABBREV_TAC`vu:'U valuation = X Y` >>
  `is_valuation (tysof lca_ctxt) (tyaof i) vu` by (
    qunabbrev_tac`vu` >>
    match_mp_tac is_valuation_extend >> simp[] ) >>
  use_termsem_implies >>
  simp[boolean_eq_true] >>
  strip_tac >>
  first_x_assum(qspec_then`(finv (to_inner Num) x):num`mp_tac) >>
  discharge_hyps >- (
    `finv (to_inner Num) x < l` suffices_by simp[] >>
    qspecl_then[`i`,`vu`,`Var(strlit"k")Num`,`Var(strlit"l")Num`]mp_tac (UNDISCH termsem_LESS) >>
    simp[] >>
    discharge_hyps >- (
      CONJ_TAC >> CONV_TAC EVAL_term_ok ) >>
    simp[boolean_eq_true] >>
    simp[termsem_def] >>
    simp[Abbr`vu`,APPLY_UPDATE_THM] >>
    simp[Abbr`vv`,APPLY_UPDATE_THM] >>
    simp[Abbr`v`] >>
    PROVE_TAC[wf_to_inner_finv_left] ) >>
  strip_tac >>
  cheat)

master theorem...

``∀n. (^thy,[]) |- [∀l. LCA l UNIV ⇒ ^^phi ^(quote n) l] ⇒
    ∀l. LCA (SUC l) UNIV ⇒ ^phi n l``

where thy extends (thyof LCA_ctxt)

to prove master theorem:
1. assume Provable(LCA l ==> phi l)
2. assume LCA (SUC l)
3. get termsem (LCA l) = True from 2 and intermediate
4. get termsem (LCA l ==> phi l) = True from 1 and soundness
5. combine 3 and 4 to get termsem (phi l) = True
6. termsem_cert (phi l) to get termsem (phi l) = True <=> phi l
7. combine 5 and 6

*)

val _ = export_theory()
