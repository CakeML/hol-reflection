open HolKernel boolLib bossLib lcsymtacs miscLib
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

val FLOOKUP_LCA = save_thm("FLOOKUP_LCA",
  ``ALOOKUP (const_list lca_ctxt) (strlit"LCA")``
  |> (PURE_ONCE_REWRITE_CONV[lca_ctxt_def] THENC EVAL))

val FLOOKUP_UNIV = save_thm("FLOOKUP_UNIV",
  ``ALOOKUP (const_list lca_ctxt) (strlit"UNIV")``
  |> (PURE_ONCE_REWRITE_CONV[lca_ctxt_def] THENC EVAL))

val FLOOKUP_cardleq = save_thm("FLOOKUP_cardleq",
  ``ALOOKUP (const_list lca_ctxt) (strlit"cardleq")``
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

val (EVAL_type_ok0,EVAL_term_ok) =
  EVAL_type_ok_term_ok
    EVAL (MATCH_MP theory_ok_sig theory_ok_lca |> SIMP_RULE std_ss[])

val th = prove(``tysof lca_ctxt = tysof(sigof lca_ctxt)``,rw[])
val EVAL_type_ok =
  (RATOR_CONV(RAND_CONV(REWR_CONV th))) THENC EVAL_type_ok0

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

fun EVAL_INST tm =
  assert (same_const``INST`` o fst o strip_comb) tm |> (
  REWR_CONV(MATCH_MP holDerivationTheory.inst_eval_thm
    (EQT_ELIM(EVAL_welltyped ``welltyped^(rand tm)``))) THENC
  EVAL_subst)

val termsem_cardleq = store_thm("termsem_cardleq",
  ``is_set_theory ^mem ∧
    i models thyof lca_ctxt ∧
    is_valuation (tysof lca_ctxt) (tyaof i) v ∧
    a = INST tyin a0 ∧
    b = INST tyin b0 ∧
    tyin = [(tya,Tyvar(strlit"A"));(tyb,Tyvar(strlit"B"))] ∧
    type_ok (tysof lca_ctxt) tya ∧
    type_ok (tysof lca_ctxt) tyb ∧
    term_ok (sigof lca_ctxt) a0 ∧
    term_ok (sigof lca_ctxt) b0 ∧
    typeof a0 = (Fun (Tyvar(strlit"A")) Bool) ∧
    typeof b0 = (Fun (Tyvar(strlit"B")) Bool) ∧
    DISJOINT {strlit"f"} {y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u [a0;b0]} ∧
    bv_names a0 = [] ∧ bv_names b0 = []
    ⇒
    termsem (tmsof lca_ctxt) i v
      (Comb (Comb (Const (strlit "cardleq") (Fun (Fun tya Bool) (Fun (Fun tyb Bool) Bool))) a) b) =
      Boolean (Holds (termsem (tmsof lca_ctxt) i v a) ≼ Holds (termsem (tmsof lca_ctxt) i v b))``,
  strip_tac >>
  qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i v (Comb (Comb (Const g ty) a) b) = R` >>
  qspecl_then[`lca_ctxt`,`i`,`v`,`g`,`ty`,`tyin`,`a`,`b`]mp_tac (UNDISCH termsem_comb2_ax) >>
  qunabbrev_tac`g` >>
  CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(LAND_CONV EVAL)))) >>
  simp[FLOOKUP_cardleq,Abbr`ty`,REV_ASSOCD] >>
  disch_then(qspecl_then[`a0`,`b0`]mp_tac) >>
  simp[theory_ok_lca] >>
  discharge_hyps >- metis_tac[WELLTYPED,term_ok_welltyped] >>
  disch_then SUBST1_TAC >>
  Q.PAT_ABBREV_TAC`tm = Exists X Y Z` >>
  Q.PAT_ABBREV_TAC`s = [(a0,Var X Y);Z]` >>
  qspecl_then[`tm`,`s`]mp_tac VSUBST_simple_subst >>
  discharge_hyps >- (
    fs[Abbr`s`,Abbr`tm`] >>
    metis_tac[] ) >>
  disch_then SUBST1_TAC >>
  simp[Abbr`s`,Abbr`tm`,REV_ASSOCD] >>
  Q.PAT_ABBREV_TAC`tm = Exists X Y Z` >>
  qspecl_then[`tyin`,`tm`]mp_tac INST_simple_inst >>
  discharge_hyps >- (
    fs[Abbr`tm`] >>
    metis_tac[term_ok_welltyped] ) >>
  simp[] >> disch_then kall_tac >>
  simp[Abbr`tm`] >>
  qspecl_then[`tyin`,`a0`]mp_tac INST_simple_inst >>
  discharge_hyps >- ( simp[] >> metis_tac[term_ok_welltyped] ) >>
  qpat_assum`a = X`(assume_tac o SYM) >>
  disch_then(mp_tac o SYM) >> simp[] >> disch_then kall_tac >>
  qspecl_then[`tyin`,`b0`]mp_tac INST_simple_inst >>
  discharge_hyps >- ( simp[] >> metis_tac[term_ok_welltyped] ) >>
  qpat_assum`b = X`(assume_tac o SYM) >>
  disch_then(mp_tac o SYM) >> simp[] >> disch_then kall_tac >>
  simp[REV_ASSOCD] >>
  qmatch_abbrev_tac`termsem (tmsof lca_ctxt) i v (Exists f ty bd) = R` >>
  qspecl_then[`sigof lca_ctxt`,`i`,`v`,`f`,`ty`,`bd`]mp_tac (UNDISCH termsem_exists) >>
  discharge_hyps >- (
    assume_tac lca_is_bool_sig >>
    imp_res_tac models_lca_ctxt_has_bool_interpretation >>
    fs[models_def,is_bool_interpretation_def,is_bool_sig_def,Abbr`bd`,Abbr`ty`] >>
    conj_tac >- (CONV_TAC EVAL_type_ok >> simp[]) >>
    CONV_TAC EVAL_term_ok >>
    simp[tyvar_inst_exists2_diff] >>
    `term_ok (sigof lca_ctxt) (INST tyin a0) ∧
     term_ok (sigof lca_ctxt) (INST tyin b0)` by (
       conj_tac >> match_mp_tac term_ok_INST >> simp[] ) >>
    imp_res_tac term_ok_welltyped >>
    BasicProvers.VAR_EQ_TAC >>
    BasicProvers.VAR_EQ_TAC >>
    `a0 has_type typeof a0 ∧
     b0 has_type typeof b0` by metis_tac[WELLTYPED] >>
    imp_res_tac INST_HAS_TYPE >>
    rpt(first_x_assum(qspec_then`tyin`mp_tac)) >>
    simp_tac std_ss [] >> ntac 2 strip_tac >>
    imp_res_tac WELLTYPED_LEMMA >>
    first_x_assum(CHANGED_TAC o SUBST1_TAC) >>
    first_x_assum(CHANGED_TAC o SUBST1_TAC) >>
    simp[REV_ASSOCD] ) >>
  simp[Abbr`R`] >>
  disch_then kall_tac >>

val intermediate_thm = store_thm("intermediate_thm",
  ``LCA (SUC l) (UNIV:'U set) ⇒
    ∃(mem:'U reln).
      is_set_theory mem ∧ (∃inf. is_infinite mem inf) ∧
      (i models (thyof lca_ctxt) ∧
       wf_to_inner ((to_inner Num):num->'U) ∧
       to_inner Num l <: tyaof i (strlit "num") [] ⇒
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
    simp[typesem_def] ) >>
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
  qmatch_abbrev_tac`termsem (tmsof s) i v (Exists ff fy pp) = True` >>
  assume_tac lca_is_bool_sig >>
  `is_bool_interpretation i` by (
    match_mp_tac models_lca_ctxt_has_bool_interpretation >>
    simp[] ) >>
  qspecl_then[`sigof s`,`i`,`v`,`ff`,`fy`,`pp`]mp_tac(UNDISCH termsem_exists) >>
  discharge_hyps >- (
    simp[] >> fs[models_def] >>
    unabbrev_all_tac >> simp[] >>
    conj_tac >- (
      `tysof lca_ctxt = tysof (sigof lca_ctxt)` by simp[] >>
      pop_assum SUBST1_TAC >> (CONV_TAC EVAL_type_ok)) >>
    conj_tac >- (
      CONV_TAC EVAL_term_ok >>
      simp[holSyntaxLibTheory.tyvar_inst_exists,tyvar_inst_exists2,tyvar_inst_exists2_diff] ) >>
    fs[is_bool_sig_def,is_bool_interpretation_def] ) >>
  simp[] >> disch_then kall_tac >>
  simp[boolean_eq_true] >>
  qexists_tac`
    Abstract
      (tyaof i (strlit"num")[])
      (* (range ((to_inner Num):num->'U)) *)
      (Funspace fl boolset)
      (λm. Abstract fl boolset
             (bool_to_inner o (f (finv (to_inner Num) m))))` >>
  conj_asm1_tac >- (
    simp[Abbr`fy`,Abbr`pp`] >>
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
  simp[Abbr`pp`] >>
  qmatch_abbrev_tac`termsem (tmsof s) i vv (And p1 p2) = True` >>
  `is_valuation (tysof s) (tyaof i) vv` by (
    simp[Abbr`vv`] >>
    match_mp_tac is_valuation_extend >>
    simp[] ) >>
  qspecl_then[`sigof s`,`i`,`vv`,`p1`,`p2`]mp_tac(UNDISCH termsem_and) >>
  discharge_hyps >- (
    simp[] >> fs[models_def] >>
    rfs[is_bool_sig_def,is_bool_interpretation_def,is_std_interpretation_def] >>
    unabbrev_all_tac >> simp[] >>
    conj_tac >> CONV_TAC EVAL_term_ok >>
    simp[holSyntaxLibTheory.tyvar_inst_exists,tyvar_inst_exists2,tyvar_inst_exists2_diff] ) >>
  simp[boolean_eq_true] >> disch_then kall_tac >>
  conj_tac >- (
    simp[Abbr`p1`,Abbr`p2`] >>
    qmatch_abbrev_tac`termsem (tmsof s) i vv (Comb (Comb (Const g gy) a) b) = True` >>

    (* at this point delegate to termsem_cardleq *)
    qabbrev_tac`tyin = [(Ind,Tyvar(strlit"A"));(Tyvar(strlit"U"),Tyvar(strlit"B"))]` >>
    qspecl_then[`s`,`i`,`vv`,`g`,`gy`,`tyin`,`a`,`b`]mp_tac(UNDISCH termsem_comb2_ax) >>
    simp[Abbr`s`,theory_ok_lca,Abbr`g`,FLOOKUP_cardleq] >>
    CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(LAND_CONV EVAL)))) >>
    simp[Abbr`gy`] >>
    disch_then(qspecl_then
      [`Const(strlit"UNIV")(Fun(Tyvar(strlit"A"))Bool)`,
       `Comb (Var ff (Fun Num (Fun (Tyvar (strlit"B")) Bool))) (Const(strlit"0")Num)`]
      mp_tac) >>
    discharge_hyps >- (
      conj_tac >- simp[Abbr`tyin`,holSyntaxLibTheory.REV_ASSOCD] >>
      conj_tac >- (
        simp[Abbr`tyin`] >>
        `tysof lca_ctxt = tysof (sigof lca_ctxt)` by simp[] >>
        pop_assum SUBST1_TAC >>
        conj_tac >> CONV_TAC EVAL_type_ok) >>
      conj_tac >- (
        CONV_TAC EVAL_term_ok >>
        simp[holSyntaxLibTheory.tyvar_inst_exists] ) >>
      conj_tac >- (
        CONV_TAC EVAL_term_ok >>
        simp[holSyntaxLibTheory.tyvar_inst_exists] ) >>
      conj_tac >- simp[Once has_type_cases] >>
      conj_tac >- (
        simp[Once has_type_cases] >>
        simp[Once has_type_cases] >>
        simp[Once has_type_cases] ) >>
      simp[Abbr`a`,Abbr`b`,Abbr`tyin`,Abbr`fy`] >>
      conj_tac >> CONV_TAC(RAND_CONV EVAL_INST) >> REFL_TAC) >>
    simp[Abbr`a`,Abbr`b`,Abbr`tyin`,Abbr`ff`,Abbr`fy`] >>
    CONV_TAC(LAND_CONV EVAL_subst) >>
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EVAL_INST)) >>
    disch_then SUBST1_TAC >>
    cheat ) >>
  simp[Abbr`p1`,Abbr`p2`] >>
  qmatch_abbrev_tac`termsem (tmsof s) i vv (And p1 p2) = True` >>
  qspecl_then[`sigof s`,`i`,`vv`,`p1`,`p2`]mp_tac(UNDISCH termsem_and) >>
  discharge_hyps >- (
    simp[] >> fs[models_def] >>
    rfs[is_bool_sig_def,is_bool_interpretation_def,is_std_interpretation_def] >>
    unabbrev_all_tac >> simp[] >>
    conj_tac >> CONV_TAC EVAL_term_ok >>
    simp[holSyntaxLibTheory.tyvar_inst_exists,tyvar_inst_exists2,tyvar_inst_exists2_diff] ) >>
  simp[boolean_eq_true] >> disch_then kall_tac >>
  conj_tac >- (
    simp[Abbr`p1`,Abbr`p2`] >>
    Q.PAT_ABBREV_TAC`ll = Comb(Var X Y) Z` >>
    qspecl_then[`ll`](mp_tac o GSYM)equation_def >>
    simp[Abbr`ll`,Abbr`fy`] >> disch_then kall_tac >>
    qmatch_abbrev_tac`termsem tmenv i vv (ll === rr) = True` >>
    qspecl_then[`sigof s`,`i`,`vv`,`ll`,`rr`,`tmenv`]mp_tac(UNDISCH termsem_equation) >>
    simp[Abbr`tmenv`] >> discharge_hyps >- (
      simp[is_structure_def] >>
      fs[models_def] >>
      assume_tac theory_ok_lca >>
      imp_res_tac theory_ok_sig >> rfs[] >>
      unabbrev_all_tac >>
      simp[equation_def] >>
      CONV_TAC EVAL_term_ok >>
      simp[holSyntaxLibTheory.tyvar_inst_exists]) >>
    simp[boolean_eq_true] >> disch_then kall_tac >>
    simp[Abbr`ll`,Abbr`vv`,termsem_def,combinTheory.APPLY_UPDATE_THM] >>
    match_mp_tac apply_abstract_matchable >>
    simp[Abbr`v`] >>
    conj_tac >- (
      match_mp_tac (UNDISCH abstract_in_funspace) >>
      simp[bool_to_inner_def,boolean_in_boolset] ) >>
    imp_res_tac wf_to_inner_finv_left >> simp[] >>
    simp[bool_to_inner_def,Abbr`rr`] >>
    qmatch_abbrev_tac`rr = termsem (tmsof s) i vv uu` >>
    qabbrev_tac`u = Const(strlit"UNIV")(Fun(Tyvar(strlit"A"))Bool)` >>
    qabbrev_tac`tyin=[(Tyvar(strlit"U"),Tyvar(strlit"A"))]` >>
    `uu = INST tyin u` by (
      unabbrev_all_tac >>
      CONV_TAC(RAND_CONV EVAL_INST) >>
      REFL_TAC ) >>
    `u === Abs (Var (strlit"x") (Tyvar(strlit"A"))) True ∈ axsof s` by (
      unabbrev_all_tac >> EVAL_TAC ) >>
    qmatch_assum_abbrev_tac`MEM eq axs` >>
    `i satisfies (sigof s,[],eq)` by fs[models_def] >>
    pop_assum mp_tac >> simp[satisfies_def] >>
    disch_then(qspec_then`vv`mp_tac) >> fs[bool_to_inner_def] >>
    termsem_INST
    cheat (* termsem_comb2_ax *)) >>
  simp[Abbr`p1`,Abbr`p2`] >>
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
