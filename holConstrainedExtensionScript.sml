open HolKernel boolLib bossLib lcsymtacs miscLib
open miscTheory finite_mapTheory alistTheory listTheory pairTheory pred_setTheory
open holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory holExtensionTheory
val _ = ParseExtras.temp_tight_equality()
val _ = new_theory"holConstrainedExtension"

val mem = ``mem:'U->'U->bool``

val types_in_def = Define`
  types_in (Var x ty) = {ty} ∧
  types_in (Const c ty) = {ty} ∧
  types_in (Comb t1 t2) = types_in t1 ∪ types_in t2 ∧
  types_in (Abs x ty t) = ty INSERT types_in t`
val _ = export_rewrites["types_in_def"]

val type_ok_types_in = store_thm("type_ok_types_in",
  ``∀sig. is_std_sig sig ⇒ ∀tm ty. term_ok sig tm ∧ ty ∈ types_in tm ⇒ type_ok (tysof sig) ty``,
  gen_tac >> strip_tac >> Induct >> simp[] >> rw[] >>
  TRY (imp_res_tac term_ok_def >> NO_TAC) >> fs[term_ok_def])

val constrainable_update_def = Define`
  constrainable_update upd ⇔
    let axiom_tyvars = set (FLAT (MAP tvars (axioms_of_upd upd))) in
    let const_tyvars = set (FLAT (MAP (tyvars o SND) (consts_of_upd upd))) in
    axiom_tyvars = const_tyvars ∧
    let all_types =
      BIGUNION (set (MAP types_in (axioms_of_upd upd))) ∪
      set (MAP SND (consts_of_upd upd)) in
    ∀name arity args.
      MEM (name,arity) (types_of_upd upd) ∧
      Tyapp name args ∈ all_types
      ⇒
      (∀args'. Tyapp name args' ∈ all_types ⇒ args' = args) ∧
      ∃vars. args = MAP Tyvar vars ∧
             set vars = axiom_tyvars ∧
             arity = LENGTH args`

val TypeDefn_constrainable = store_thm("TypeDefn_constrainable",
  ``∀name pred abs rep ctxt.
    TypeDefn name pred abs rep updates ctxt ∧
    is_std_sig (sigof ctxt) ⇒
    constrainable_update (TypeDefn name pred abs rep)``,
  rw[updates_cases] >>
  `MEM "fun" (MAP FST (type_list ctxt)) ∧ MEM "bool" (MAP FST (type_list ctxt))` by (
    fs[is_std_sig_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  `∃repty. typeof pred = Fun repty Bool ∧ (∀x. MEM x (tyvars repty) ⇒ MEM x (tvars pred))` by (
    imp_res_tac proves_term_ok >> fs[term_ok_def] >>
    imp_res_tac WELLTYPED_LEMMA >> fs[] >> rfs[] >>
    rw[] >> imp_res_tac tyvars_typeof_subset_tvars >>
    fs[tyvars_def,tvars_def] >>
    `MEM x (tyvars (typeof pred))` by simp[tyvars_def] >>
    fs[WELLTYPED] >>
    imp_res_tac tyvars_typeof_subset_tvars >>
    fs[tyvars_def,SUBSET_DEF]) >>
  `∀args'. Tyapp name args' ∉ types_in pred ∧ Tyapp name args' ≠ repty ∧ Tyapp name args' ≠ Bool` by (
    imp_res_tac proves_term_ok >> fs[term_ok_def] >>
    rw[] >>
    spose_not_then strip_assume_tac >>
    imp_res_tac type_ok_types_in >>
    imp_res_tac term_ok_type_ok >>
    fs[type_ok_def] >>
    rw[] >> rfs[type_ok_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  simp[constrainable_update_def] >>
  conj_tac >- (
    simp[conexts_of_upd_def,tvars_def,equation_def,tyvars_def] >>
    simp[EXTENSION,MEM_FOLDR_LIST_UNION,MEM_MAP,PULL_EXISTS,tyvars_def] >>
    rw[EQ_IMP_THM] >> rw[] >>
    imp_res_tac proves_term_ok >> fs[Once has_type_cases] >>
    imp_res_tac WELLTYPED_LEMMA >> fs[tyvars_def] ) >>
  simp[conexts_of_upd_def,tvars_def,equation_def,tyvars_def] >>
  rw[] >> fs[] >> rw[] >> fs[] >> TRY(metis_tac[]) >>
  qexists_tac`STRING_SORT (tvars pred)` >> simp[] >>
  simp[EXTENSION,MEM_FOLDR_LIST_UNION,MEM_MAP,PULL_EXISTS,tyvars_def] >>
  rw[EQ_IMP_THM] >> fs[])

val _ = Parse.type_abbrev("constraints",``:'U list -> ('U list # 'U list) option``)

val constrain_assignment_def = Define`
  constrain_assignment cs p ns f =
    λname args. case cs args of NONE => f name args
    | SOME x => THE(ALOOKUP (ZIP(ns,p x)) name)`

val constrain_interpretation_def = Define`
  constrain_interpretation upd cs ((δ,γ):'U interpretation) =
    (constrain_assignment cs FST (MAP FST (types_of_upd upd)) δ,
     constrain_assignment cs SND (MAP FST (consts_of_upd upd)) γ)`

val well_formed_constraints_def = xDefine"well_formed_constraints"`
  well_formed_constraints0 ^mem upd cs δ ⇔
    ∀vs tyvs tmvs. cs vs = SOME (tyvs,tmvs) ⇒
        LENGTH tyvs = LENGTH (types_of_upd upd) ∧
        EVERY inhabited tyvs ∧
        let vars = STRING_SORT (tvars (HD (axioms_of_upd upd))) in
        LENGTH vars = LENGTH vs ∧
        let τ = K boolset =++ (ZIP(vars,vs))in
        (* TODO: should constrain δ here, or expect it to already be constrained? *)
        LIST_REL (λv ty. v <: typesem δ τ ty)
          tmvs (MAP SND (consts_of_upd upd))`
val _ = Parse.overload_on("well_formed_constraints",``well_formed_constraints0 ^mem``)

val old_constrain_assignment_def = Define`
  old_constrain_assignment cs f =
    λname args. case cs name args of SOME x => x | NONE => f name args`

val old_constrain_interpretation_def = Define`
  old_constrain_interpretation (tycs,tmcs) ((δ,γ):'U interpretation) =
    (old_constrain_assignment tycs δ,
     old_constrain_assignment tmcs γ)`

val old_add_constraints_thm = store_thm("old_add_constraints_thm",
  ``is_set_theory ^mem ⇒
    ∀i upd ctxt cs.
      upd updates ctxt ∧ ctxt extends init_ctxt ∧
      i models (thyof (upd::ctxt)) ∧
      (∀name args. IS_SOME (FST cs name args) ⇒
        MEM (name,LENGTH args) (types_of_upd upd) ∧
        inhabited (THE (FST cs name args)) ∧
        ∀x. MEM x (MAP FST (consts_of_upd upd)) ⇒
            IS_SOME (SND cs x args)
            (* the type of the constant should have exactly the same type
            variables as the new type hence the re-use of args here *)) ∧
      (∀name args. IS_SOME (SND cs name args) ⇒
        ∃ty. MEM (name,ty) (consts_of_upd upd) ∧
             (LENGTH (tyvars ty) = LENGTH args) ∧
             ∀τ. is_type_valuation τ ∧
                 (MAP τ (STRING_SORT (tyvars ty)) = args) ⇒
             (THE (SND cs name args)) <: typesem (old_constrain_assignment (FST cs) (FST i)) τ ty) ∧
      (∀p. MEM p (axioms_of_upd upd) ⇒
        old_constrain_interpretation cs i satisfies (sigof (upd::ctxt),[],p))
      ⇒
      (old_constrain_interpretation cs i) models (thyof (upd::ctxt))``,
  rw[] >> fs[models_def] >>
  REWRITE_TAC[CONJ_ASSOC] >>
  `theory_ok (thyof ctxt)` by metis_tac[extends_theory_ok,init_theory_ok] >>
  `∃δ γ. i =(δ,γ)` by metis_tac[pair_CASES] >>
  `∃tycs tmcs. cs =(tycs,tmcs)` by metis_tac[pair_CASES] >>
  `ALL_DISTINCT (MAP FST (type_list (upd::ctxt))) ∧
   ALL_DISTINCT (MAP FST (const_list (upd::ctxt)))` by (
    conj_tac >>
    imp_res_tac updates_ALL_DISTINCT >>
    first_x_assum match_mp_tac >>
    imp_res_tac extends_ALL_DISTINCT >>
    first_x_assum match_mp_tac >>
    EVAL_TAC ) >>
  conj_asm1_tac >- (
    fs[is_interpretation_def,is_std_interpretation_def,old_constrain_interpretation_def] >>
    simp[GSYM CONJ_ASSOC] >>
    conj_tac >- (
      fs[is_type_assignment_def,FEVERY_ALL_FLOOKUP] >> rw[] >>
      res_tac >> rw[old_constrain_assignment_def] >>
      BasicProvers.CASE_TAC >> rw[] >>
      fs[IS_SOME_EXISTS,PULL_EXISTS] >>
      res_tac >> metis_tac[] ) >>
    CONV_TAC(lift_conjunct_conv(can (match_term ``is_std_type_assignment X``))) >>
    conj_asm1_tac >- (
      fs[is_std_type_assignment_def,old_constrain_assignment_def] >>
      imp_res_tac theory_ok_sig >>
      fs[is_std_sig_def,IS_SOME_EXISTS,PULL_EXISTS] >>
      imp_res_tac ALOOKUP_MEM >>
      rw[] >> fs[ALL_DISTINCT_APPEND] >>
      BasicProvers.CASE_TAC >>
      res_tac >> fs[] >> rw[] >>
      rpt (BasicProvers.CASE_TAC >> res_tac >> fs[]) >>
      fs[MEM_MAP,EXISTS_PROD] >> metis_tac[]) >>
    conj_tac >- (
      fs[interprets_def,old_constrain_assignment_def] >> rw[] >>
      BasicProvers.CASE_TAC >>
      fs[IS_SOME_EXISTS,PULL_EXISTS] >>
      imp_res_tac theory_ok_sig >>
      fs[is_std_sig_def] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[Once updates_cases] >> rw[] >> fs[] >>
      res_tac >> fs[] >> rw[] >>
      fs[MEM_MAP,EXISTS_PROD,LET_THM] >>
      metis_tac[] ) >>
    fs[is_term_assignment_def,FEVERY_ALL_FLOOKUP] >> rw[] >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    rw[old_constrain_assignment_def] >>
    reverse BasicProvers.CASE_TAC >- (
      fs[IS_SOME_EXISTS,PULL_EXISTS] >>
      first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
      qpat_assum`FLOOKUP X Y = Z`mp_tac >>
      simp[FLOOKUP_FUNION] >>
      BasicProvers.CASE_TAC >- (
        imp_res_tac ALOOKUP_FAILS >> fs[] ) >>
      rw[] >>
      `v = ty` by (
        fs[Once updates_cases] >> rw[] >> fs[] >>
        qmatch_assum_abbrev_tac`ALOOKUP al k = SOME v` >>
        `ALL_DISTINCT (MAP FST al)` by (
          simp[Abbr`al`,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] ) >>
        imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
        fs[Abbr`al`] ) >>
      rw[] >> res_tac >> fs[old_constrain_assignment_def]) >>
    Cases_on`type_ok (tysof ctxt) v` >- (
      qmatch_abbrev_tac`a <: b` >>
      qmatch_assum_abbrev_tac`a <: c` >>
      qsuff_tac `b = c` >- rw[] >>
      unabbrev_all_tac >>
      match_mp_tac typesem_consts >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      simp[type_ok_def] >> rw[FUN_EQ_THM] >>
      BasicProvers.CASE_TAC >>
      fs[IS_SOME_EXISTS,PULL_EXISTS] >> res_tac >>
      fs[Once updates_cases] >> rw[] >> fs[] >> rw[] >>
      imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    qpat_assum`FLOOKUP X Y = Z`mp_tac >>
    simp[FLOOKUP_FUNION] >>
    BasicProvers.CASE_TAC >- (
      strip_tac >>
      fs[theory_ok_def] >>
      qsuff_tac`F`>-rw[]>>
      qpat_assum`¬x`mp_tac >>simp[]>>
      first_x_assum match_mp_tac >>
      simp[IN_FRANGE_FLOOKUP] >>
      metis_tac[] ) >>
    rw[] >>
    qmatch_abbrev_tac`a <: b` >>
    qmatch_assum_abbrev_tac`a <: c` >>
    qsuff_tac `b = c` >- rw[] >>
    unabbrev_all_tac >>
    fs[Once updates_cases] >> rw[] >> fs[] >- (
      rpt AP_THM_TAC >> AP_TERM_TAC >> rw[FUN_EQ_THM] ) >>
    qmatch_abbrev_tac`typesem d1 τ v = typesem δ τ v` >>
    `is_std_type_assignment d1 ∧
     is_std_type_assignment δ` by (
       reverse conj_asm2_tac >- fs[is_std_interpretation_def] >>
       simp[Abbr`d1`,GSYM old_constrain_assignment_def] ) >>
    rator_x_assum`ALOOKUP` mp_tac >> simp[] >>
    Q.PAT_ABBREV_TAC`t1 = domain (typeof pred)` >>
    Q.PAT_ABBREV_TAC`t2 = Tyapp name X` >>
    qsuff_tac`k ∈ {abs;rep} ∧ (set (tyvars v) = set (tyvars (Fun t1 t2))) ⇒
              (typesem d1 τ t1 = typesem δ τ t1) ∧
              (typesem d1 τ t2 = typesem δ τ t2)` >- (
      match_mp_tac SWAP_IMP >> strip_tac >>
      discharge_hyps >- (
        pop_assum mp_tac >> rw[] >>
        simp[tyvars_def] >>
        metis_tac[pred_setTheory.UNION_COMM] ) >>
      pop_assum mp_tac >>
      rw[] >>
      qmatch_abbrev_tac`typesem d1 τ (Fun dom rng) = typesem δ τ (Fun dom rng)` >>
      qspecl_then[`δ`,`τ`,`dom`,`rng`]mp_tac typesem_Fun >>
      qspecl_then[`d1`,`τ`,`dom`,`rng`]mp_tac typesem_Fun >>
      simp[] >> rw[]) >>
    strip_tac >>
    conj_tac >- (
      unabbrev_all_tac >>
      match_mp_tac typesem_consts >>
      qexists_tac`tysof (ctxt)` >>
      imp_res_tac proves_term_ok >>
      qpat_assum`k ∈ X`kall_tac >>
      fs[term_ok_def] >>
      conj_tac >- (
        imp_res_tac term_ok_type_ok >>
        fs[theory_ok_def] ) >>
      simp[type_ok_def] >> rw[FUN_EQ_THM] >>
      BasicProvers.CASE_TAC >>
      fs[IS_SOME_EXISTS,PULL_EXISTS] >> res_tac >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >> metis_tac[] ) >>
    unabbrev_all_tac >>
    simp[typesem_def,MAP_MAP_o,combinTheory.o_DEF,ETA_AX] >>
    BasicProvers.CASE_TAC >>
    qsuff_tac`set (tyvars v) = set (tvars pred)` >- (
      qpat_assum`set (tyvars v) = X`kall_tac >>
      rw[] >>
      `STRING_SORT (tvars pred) = STRING_SORT (tyvars v)` by (
        `ALL_DISTINCT (tvars pred)` by simp[] >>
        `ALL_DISTINCT (tyvars v)` by simp[] >>
        `PERM (tvars pred) (tyvars v)` by (
          match_mp_tac sortingTheory.PERM_ALL_DISTINCT >>
          fs[pred_setTheory.EXTENSION] ) >>
        metis_tac[holSyntaxLibTheory.STRING_SORT_EQ] ) >>
      fs[IS_SOME_EXISTS,PULL_EXISTS,LET_THM] >>
      metis_tac[optionTheory.NOT_SOME_NONE] ) >>
    simp[tyvars_def,pred_setTheory.EXTENSION,
         holSyntaxLibTheory.MEM_FOLDR_LIST_UNION,
         MEM_MAP,PULL_EXISTS] >>
    qpat_assum`k ∈ X`kall_tac >>
    imp_res_tac proves_term_ok >> fs[term_ok_def] >>
    fs[WELLTYPED] >>
    imp_res_tac tyvars_typeof_subset_tvars >>
    fs[pred_setTheory.SUBSET_DEF,tyvars_def] >>
    metis_tac[] ) >>
  gen_tac >>
  qmatch_abbrev_tac`P ⇒ q` >>
  strip_tac >> qunabbrev_tac`q` >>
  first_x_assum(qspec_then`p`mp_tac) >>
  fs[Abbr`P`] >>
  disch_then kall_tac >>
  first_x_assum(qspec_then`p`mp_tac) >> simp[] >>
  strip_tac >>
  `term_ok (sigof ctxt) p` by fs[theory_ok_def] >>
  imp_res_tac theory_ok_sig >>
  match_mp_tac satisfies_extend >>
  map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
  simp[] >>
  REWRITE_TAC[CONJ_ASSOC] >>
  conj_asm1_tac >- (
    conj_tac >>
    match_mp_tac SUBMAP_FUNION >>
    disj2_tac >>
    fs[ALL_DISTINCT_APPEND,pred_setTheory.IN_DISJOINT] >>
    metis_tac[] ) >>
  match_mp_tac satisfies_consts >>
  qexists_tac`i` >> simp[] >> fs[] >>
  simp[term_ok_def,type_ok_def] >>
  REWRITE_TAC[CONJ_ASSOC] >>
  conj_tac >- (
    rw[old_constrain_interpretation_def,old_constrain_assignment_def,FUN_EQ_THM] >>
    BasicProvers.CASE_TAC >>
    fs[IS_SOME_EXISTS,PULL_EXISTS] >> res_tac >>
    fs[ALL_DISTINCT_APPEND,MEM_MAP,EXISTS_PROD] >>
    imp_res_tac ALOOKUP_MEM >>
    metis_tac[] ) >>
  fs[satisfies_def] >> rw[] >>
  qmatch_assum_abbrev_tac`tmsof ctxt ⊑ tmsig` >>
  qmatch_assum_abbrev_tac`tysof ctxt ⊑ tysig` >>
  first_assum(
    mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO](UNDISCH extend_valuation_exists))) >>
  first_assum(fn th => disch_then (mp_tac o C MATCH_MP th)) >>
  discharge_hyps >- fs[is_interpretation_def] >> strip_tac >>
  first_x_assum(qspec_then`v'`mp_tac) >> simp[] >>
  disch_then (SUBST1_TAC o SYM) >>
  match_mp_tac EQ_TRANS >>
  qexists_tac`termsem (tmsof ctxt) (δ,γ) v' p` >>
  conj_tac >- (
    match_mp_tac termsem_frees >>
    simp[] >> rw[] >>
    first_x_assum match_mp_tac >>
    imp_res_tac term_ok_VFREE_IN >>
    fs[term_ok_def] ) >>
  metis_tac[termsem_extend])

val _ = export_theory()
