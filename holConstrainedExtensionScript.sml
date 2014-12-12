open HolKernel boolLib bossLib lcsymtacs miscLib
open miscTheory finite_mapTheory alistTheory listTheory pairTheory pred_setTheory
open holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory holExtensionTheory
val _ = ParseExtras.temp_tight_equality()
val _ = new_theory"holConstrainedExtension"

val mem = ``mem:'U->'U->bool``

(* TODO: move *)

val UPDATE_LIST_NOT_MEM = store_thm("UPDATE_LIST_NOT_MEM",
  ``∀ls f x. ¬MEM x(MAP FST ls) ⇒ (f =++ ls) x = f x``,
  Induct >> simp[UPDATE_LIST_THM,combinTheory.APPLY_UPDATE_THM])

val MAP_ZIP_UPDATE_LIST_ALL_DISTINCT_same = store_thm("MAP_ZIP_UPDATE_LIST_ALL_DISTINCT_same",
  ``∀ks vs f. LENGTH ks = LENGTH vs ∧ ALL_DISTINCT ks ⇒ (MAP (f =++ ZIP (ks,vs)) ks = vs)``,
  Induct >> simp[LENGTH_NIL_SYM] >>
  gen_tac >> Cases >> simp[UPDATE_LIST_THM] >>
  simp[UPDATE_LIST_NOT_MEM,MAP_ZIP,combinTheory.APPLY_UPDATE_THM])

val is_type_valuation_UPDATE_LIST = store_thm("is_type_valuation_UPDATE_LIST",
  ``∀t ls. is_type_valuation t ∧ EVERY (inhabited o SND) ls ⇒
           is_type_valuation (t =++ ls)``,
  rw[is_type_valuation_def,APPLY_UPDATE_LIST_ALOOKUP] >>
  BasicProvers.CASE_TAC >> rw[] >> imp_res_tac ALOOKUP_MEM >>
  fs[EVERY_MEM,FORALL_PROD] >> metis_tac[])

val ALL_DISTINCT_MAP_implode = store_thm("ALL_DISTINCT_MAP_implode",
  ``ALL_DISTINCT ls ⇒ ALL_DISTINCT (MAP implode ls)``,
  strip_tac >>
  match_mp_tac ALL_DISTINCT_MAP_INJ >>
  rw[mlstringTheory.implode_def])
val _ = export_rewrites["ALL_DISTINCT_MAP_implode"]

val tyvars_Tyapp_MAP_Tyvar = store_thm("tyvars_Tyapp_MAP_Tyvar",
  ``∀x ls. ALL_DISTINCT ls ⇒ (tyvars (Tyapp x (MAP Tyvar ls)) = LIST_UNION [] ls)``,
  simp[tyvars_def] >>
  Induct >> fs[tyvars_def,LIST_UNION_def] >>
  rw[LIST_INSERT_def])

val set_MAP_implode_STRING_SORT_MAP_explode = store_thm("set_MAP_implode_STRING_SORT_MAP_explode",
  ``set (MAP implode (STRING_SORT (MAP explode ls))) = set ls``,
  rw[EXTENSION,MEM_MAP,PULL_EXISTS,mlstringTheory.implode_explode])

val STRING_SORT_SET_TO_LIST_set_tvars = store_thm("STRING_SORT_SET_TO_LIST_set_tvars",
  ``∀tm. STRING_SORT (MAP explode (SET_TO_LIST (set (tvars tm)))) =
         STRING_SORT (MAP explode (tvars tm))``,
  gen_tac >> assume_tac(SPEC_ALL tvars_ALL_DISTINCT) >>
  simp[STRING_SORT_EQ] >>
  match_mp_tac sortingTheory.PERM_MAP >>
  pop_assum mp_tac >>
  REWRITE_TAC[sortingTheory.ALL_DISTINCT_PERM_LIST_TO_SET_TO_LIST] >>
  simp[sortingTheory.PERM_SYM])

(* -- *)

val types_in_def = Define`
  types_in (Var x ty) = {ty} ∧
  types_in (Const c ty) = {ty} ∧
  types_in (Comb t1 t2) = types_in t1 ∪ types_in t2 ∧
  types_in (Abs v t) = types_in v ∪ types_in t`
val _ = export_rewrites["types_in_def"]

val type_ok_types_in = store_thm("type_ok_types_in",
  ``∀sig. is_std_sig sig ⇒ ∀tm ty. term_ok sig tm ∧ ty ∈ types_in tm ⇒ type_ok (tysof sig) ty``,
  gen_tac >> strip_tac >> Induct >> simp[] >> rw[] >>
  TRY (imp_res_tac term_ok_def >> NO_TAC) >> fs[term_ok_def])

val (subtype1_rules,subtype1_ind,subtype1_cases) = Hol_reln`
  MEM a args ⇒ subtype1 a (Tyapp name args)`
val _ = Parse.add_infix("subtype",401,Parse.NONASSOC)
val _ = Parse.overload_on("subtype",``RTC subtype1``)
val subtype_Tyvar = save_thm("subtype_Tyvar",
  ``ty subtype (Tyvar x)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subtype1_cases])
val _ = export_rewrites["subtype_Tyvar"]
val subtype_Tyapp = save_thm("subtype_Tyapp",
  ``ty subtype (Tyapp name args)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subtype1_cases])

val subtype_type_ok = store_thm("subtype_type_ok",
  ``∀tysig ty1 ty2. type_ok tysig ty2 ∧ ty1 subtype ty2 ⇒ type_ok tysig ty1``,
  gen_tac >>
  (relationTheory.RTC_lifts_invariants
    |> Q.GEN`R` |> Q.ISPEC`inv subtype1`
    |> SIMP_RULE std_ss [relationTheory.inv_MOVES_OUT,relationTheory.inv_DEF]
    |> Q.GEN`P` |> Q.ISPEC`type_ok tysig`
    |> match_mp_tac) >>
  ONCE_REWRITE_TAC[CONJ_COMM] >>
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  CONV_TAC SWAP_FORALL_CONV >> gen_tac >>
  ho_match_mp_tac subtype1_ind >>
  simp[type_ok_def,EVERY_MEM])

val typesem_consts = store_thm("typesem_consts",
  ``∀δ τ ty δ'.
    (∀name args. (Tyapp name args) subtype ty ⇒
      δ' name = δ name ∨
      ∃vars. args = MAP Tyvar vars ∧
             δ' name (MAP τ vars) = δ name (MAP τ vars))
    ⇒ typesem δ' τ ty = typesem δ τ ty``,
  ho_match_mp_tac typesem_ind >>
  conj_tac >- simp[typesem_def] >>
  rw[] >> simp[typesem_def] >>
  fs[subtype_Tyapp] >>
  first_assum(qspecl_then[`name`,`args`]mp_tac) >>
  discharge_hyps >- rw[] >> strip_tac >- (
    rw[] >> AP_TERM_TAC >> simp[MAP_EQ_f] >> metis_tac[] ) >>
  simp[MAP_MAP_o,combinTheory.o_DEF,typesem_def,ETA_AX])

val VFREE_IN_types_in = store_thm("VFREE_IN_types_in",
  ``∀t2 t1. VFREE_IN t1 t2 ⇒ typeof t1 ∈ types_in t2``,
  ho_match_mp_tac term_induction >> rw[] >> rw[])

val (subterm1_rules,subterm1_ind,subterm1_cases) = Hol_reln`
  subterm1 t1 (Comb t1 t2) ∧
  subterm1 t2 (Comb t1 t2) ∧
  subterm1 tm (Abs v tm) ∧
  subterm1 v (Abs v tm)`

val _ = Parse.add_infix("subterm",401,Parse.NONASSOC)
val _ = Parse.overload_on("subterm",``RTC subterm1``)
val subterm_Var = save_thm("subterm_Var",
  ``tm subterm (Var x ty)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases])
val subterm_Const = save_thm("subterm_Const",
  ``tm subterm (Const x ty)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases])
val _ = export_rewrites["subterm_Var","subterm_Const"]
val subterm_Comb = save_thm("subterm_Comb",
  ``tm subterm (Comb t1 t2)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases])
val subterm_Abs = save_thm("subterm_Abs",
  ``tm subterm (Abs v t)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases])

val VFREE_IN_subterm = store_thm("VFREE_IN_subterm",
  ``∀t1 t2. VFREE_IN t1 t2 ⇒ t1 subterm t2``,
  Induct_on`t2` >> simp[subterm_Comb,subterm_Abs] >>
  metis_tac[])

val subterm_welltyped = save_thm("subterm_welltyped",
  let val th =
    prove(``∀tm ty. tm has_type ty ⇒ ∀t. t subterm tm ⇒ welltyped t``,
      ho_match_mp_tac has_type_strongind >>
      simp[subterm_Comb,subterm_Abs] >> rw[] >>
      rw[] >> imp_res_tac WELLTYPED_LEMMA >> simp[])
  in METIS_PROVE[th,welltyped_def]
    ``∀t tm. welltyped tm ∧ t subterm tm ⇒ welltyped t``
  end)

val termsem_consts = store_thm("termsem_consts",
  ``∀tmsig i v tm i'.
      welltyped tm ∧
      (∀name ty. VFREE_IN (Const name ty) tm ⇒
                 instance tmsig i' name ty (tyvof v) =
                 instance tmsig i name ty (tyvof v)) ∧
      (∀t. t subterm tm ⇒
         typesem (tyaof i') (tyvof v) (typeof t) =
         typesem (tyaof i ) (tyvof v) (typeof t))
      ⇒
      termsem tmsig i' v tm = termsem tmsig i v tm``,
  Induct_on`tm` >> simp[termsem_def] >> rw[]
  >- (
    fs[subterm_Comb] >>
    metis_tac[]) >>
  simp[termsem_def] >>
  fsrw_tac[boolSimps.DNF_ss][subterm_Abs] >>
  rpt AP_TERM_TAC >> simp[FUN_EQ_THM])

val updates_upd_ALL_DISTINCT = store_thm("updates_upd_ALL_DISTINCT",
  ``∀upd ctxt. upd updates ctxt ⇒
      ALL_DISTINCT (MAP FST (consts_of_upd upd)) ∧
      ALL_DISTINCT (MAP FST (types_of_upd upd))``,
  ho_match_mp_tac updates_ind >> rw[] >>
  rw[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX])

val updates_upd_DISJOINT = store_thm("updates_upd_DISJOINT",
  ``∀upd ctxt. upd updates ctxt ⇒
      DISJOINT (set (MAP FST (types_of_upd upd))) (set (MAP FST (type_list ctxt))) ∧
      DISJOINT (set (MAP FST (consts_of_upd upd))) (set (MAP FST (const_list ctxt)))``,
  ho_match_mp_tac updates_ind >> rw[IN_DISJOINT,MEM_MAP,FORALL_PROD,EXISTS_PROD,PULL_EXISTS,LET_THM] >>
  metis_tac[])

val TYPE_SUBST_tyvars_subtype_lemma = prove(
  ``∀i e ty0. MEM e (tyvars ty0) ⇒
      TYPE_SUBST i (Tyvar e) subtype TYPE_SUBST i ty0``,
    ntac 2 gen_tac >>
    ho_match_mp_tac type_ind >>
    rw[tyvars_def,MEM_FOLDR_LIST_UNION] >>
    fs[REV_ASSOCD_ALOOKUP] >>
    simp[subtype_Tyapp] >>
    fs[EVERY_MEM] >>
    res_tac >>
    BasicProvers.CASE_TAC >> fs[MEM_MAP,PULL_EXISTS] >>
    metis_tac[])

val Var_subterm_types_in = prove(
  ``∀t x ty. Var x ty subterm t ⇒ ty ∈ types_in t``,
  ho_match_mp_tac term_induction >> rw[subterm_Comb,subterm_Abs] >>
  metis_tac[])

val Const_subterm_types_in = prove(
  ``∀t x ty. Const x ty subterm t ⇒ ty ∈ types_in t``,
  ho_match_mp_tac term_induction >> rw[subterm_Comb,subterm_Abs] >>
  metis_tac[])

val subterm_typeof_types_in = store_thm("subterm_typeof_types_in",
  ``∀t1 t2 name args. (Tyapp name args) subtype (typeof t1) ∧ t1 subterm t2 ∧ welltyped t2 ∧ name ≠ (strlit"fun") ⇒
      ∃ty2. Tyapp name args subtype ty2 ∧ ty2 ∈ types_in t2``,
  ho_match_mp_tac term_induction >>
  conj_tac >- ( rw[] >> metis_tac[Var_subterm_types_in] ) >>
  conj_tac >- ( rw[] >> metis_tac[Const_subterm_types_in] ) >>
  conj_tac >- (
    rw[] >>
    imp_res_tac subterm_welltyped >> fs[] >> fs[] >>
    last_x_assum match_mp_tac >> simp[] >>
    conj_tac >- (
      simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      simp[subtype_Tyapp] >>
      metis_tac[relationTheory.RTC_REFL] ) >>
    simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp[subterm_Comb] ) >>
  rw[] >>
  fs[subtype_Tyapp] >- (
    last_x_assum(match_mp_tac) >> simp[] >>
    conj_tac >- (
      simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
      first_assum(match_exists_tac o concl) >> simp[] ) >>
    simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp[subterm_Abs] ) >>
  first_x_assum(match_mp_tac) >> simp[] >>
  conj_tac >- (
    simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
    first_assum(match_exists_tac o concl) >> simp[] ) >>
  simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
  ONCE_REWRITE_TAC[CONJ_COMM] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[subterm_Abs] )

(* maybe the above too *)

(* TODO: move? *)
val mlstring_sort_def = Define`
  mlstring_sort ls = MAP implode (STRING_SORT (MAP explode ls))`

val PERM_MAP_BIJ = store_thm("PERM_MAP_BIJ",
  ``∀f l1 l2.
    BIJ f UNIV UNIV ⇒
    (PERM l1 l2 ⇔ PERM (MAP f l1) (MAP f l2))``,
  rw[BIJ_IFF_INV] >>
  EQ_TAC >- rw[sortingTheory.PERM_MAP] >>
  `∀l. MEM l [l1;l2] ⇒ l = MAP g (MAP f l)` by (
    rw[MAP_MAP_o,combinTheory.o_DEF] ) >>
  fs[] >>
  metis_tac[sortingTheory.PERM_MAP])

val implode_BIJ = store_thm("implode_BIJ",
  ``BIJ implode UNIV UNIV``,
  rw[BIJ_IFF_INV] >>
  qexists_tac`explode` >>
  rw[mlstringTheory.implode_explode,
     mlstringTheory.explode_implode])

val explode_BIJ = store_thm("explode_BIJ",
  ``BIJ explode UNIV UNIV``,
  rw[BIJ_IFF_INV] >>
  qexists_tac`implode` >>
  rw[mlstringTheory.implode_explode,
     mlstringTheory.explode_implode])

val INJ_MAP_EQ_IFF = store_thm("INJ_MAP_EQ_IFF",
  ``∀f l1 l2.
    INJ f (set l1 ∪ set l2) UNIV ⇒
    (MAP f l1 = MAP f l2 ⇔ l1 = l2)``,
  rw[] >> EQ_TAC >- metis_tac[INJ_MAP_EQ] >> rw[])

val mlstring_sort_eq = store_thm("mlstring_sort_eq",
  ``∀l1 l2. ALL_DISTINCT l1 ∧ ALL_DISTINCT l2 ⇒
    ((mlstring_sort l1 = mlstring_sort l2) ⇔ PERM l1 l2)``,
  rw[mlstring_sort_def] >>
  qspecl_then[`l1`,`l2`]mp_tac(MATCH_MP PERM_MAP_BIJ explode_BIJ) >>
  disch_then SUBST1_TAC >>
  imp_res_tac ALL_DISTINCT_MAP_explode >>
  imp_res_tac STRING_SORT_EQ >>
  first_x_assum(CHANGED_TAC o (SUBST1_TAC o SYM)) >>
  match_mp_tac INJ_MAP_EQ_IFF >>
  mp_tac implode_BIJ >>
  simp[BIJ_DEF,INJ_DEF,MEM_MAP,PULL_EXISTS])
(* -- *)

val mlstring_sort_SET_TO_LIST_set_tvars = store_thm("mlstring_sort_SET_TO_LIST_set_tvars",
  ``mlstring_sort (SET_TO_LIST (set (tvars tm))) = mlstring_sort (tvars tm)``,
  rw[mlstring_sort_def,STRING_SORT_SET_TO_LIST_set_tvars])

val constrainable_update_def = Define`
  constrainable_update upd ⇔
    ∃vars.
      FINITE vars ∧
      EVERY ($= vars) (MAP (set o tvars) (axioms_of_upd upd)) ∧
      EVERY ($= vars) (MAP (set o tyvars o SND) (consts_of_upd upd)) ∧
      EVERY (λp. ∀name ty ty'.
                    VFREE_IN (Const name ty) p ∧
                    MEM (name,ty') (consts_of_upd upd)
                    ⇒ ty' = ty)
            (axioms_of_upd upd) ∧
      let all_types =
        BIGUNION (set (MAP types_in (axioms_of_upd upd))) ∪
        set (MAP SND (consts_of_upd upd)) in
      ∀name arity.
        MEM (name,arity) (types_of_upd upd) ⇒
        arity = CARD vars ∧
        ∀args ty.
          Tyapp name args subtype ty ∧ ty ∈ all_types ⇒
          args = MAP Tyvar (mlstring_sort (SET_TO_LIST vars))`

val TypeDefn_constrainable = store_thm("TypeDefn_constrainable",
  ``∀name pred abs rep ctxt.
    TypeDefn name pred abs rep updates ctxt ∧
    is_std_sig (sigof ctxt) ⇒
    constrainable_update (TypeDefn name pred abs rep)``,
  rw[updates_cases] >>
  `MEM (strlit"fun") (MAP FST (type_list ctxt)) ∧ MEM (strlit"bool") (MAP FST (type_list ctxt))` by (
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
  simp[constrainable_update_def,ALL_DISTINCT_CARD_LIST_TO_SET] >>
  simp[tyvars_def,Q.SPECL[`set s`,`set t`]EXTENSION,MEM_FOLDR_LIST_UNION,MEM_MAP,PULL_EXISTS,EVERY_MAP] >>
  conj_tac >- (
    simp[conexts_of_upd_def,tvars_def,equation_def,tyvars_def] >>
    simp[EXTENSION,MEM_FOLDR_LIST_UNION,MEM_MAP,PULL_EXISTS,tyvars_def,mlstringTheory.implode_explode] >>
    rw[EQ_IMP_THM] >> rw[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (
    simp[EVERY_MEM,GSYM mlstring_sort_def] >>
    simp[conexts_of_upd_def,GSYM mlstring_sort_def] >>
    gen_tac >> strip_tac >> BasicProvers.VAR_EQ_TAC >> rpt gen_tac >>
    CONV_TAC(LAND_CONV (LAND_CONV EVAL)) >>
    simp[GSYM STRING_SORT_def,GSYM mlstringTheory.implode_def,GSYM mlstring_sort_def] >>
    rw[] >>
    fs[is_std_sig_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,mlstringTheory.implode_def,EXISTS_PROD] >>
    TRY(metis_tac[]) >>
    imp_res_tac proves_term_ok >> fs[] >>
    fs[term_ok_def] >>
    imp_res_tac term_ok_VFREE_IN >>
    fs[term_ok_def] >>
    imp_res_tac ALOOKUP_MEM >>
    metis_tac[]) >>
  CHANGED_TAC(ONCE_REWRITE_TAC[GSYM LIST_TO_SET_APPEND]) >>
  ONCE_REWRITE_TAC[GSYM tyvars_def] >>
  simp[tyvars_Tyapp_MAP_Tyvar] >>
  simp[set_MAP_implode_STRING_SORT_MAP_explode] >>
  fs[GSYM SUBSET_DEF,SUBSET_UNION_ABSORPTION] >>
  simp[GSYM ALL_DISTINCT_CARD_LIST_TO_SET,ALL_DISTINCT_LIST_UNION] >>
  simp[set_MAP_implode_STRING_SORT_MAP_explode] >>
  simp[mlstring_sort_SET_TO_LIST_set_tvars,GSYM mlstring_sort_def] >>
  simp[EVERY_MEM] >>
  simp[conexts_of_upd_def,tvars_def,equation_def,tyvars_def] >>
  rw[] >> fs[] >> rw[] >> fs[Once subtype_Tyapp] >> TRY(metis_tac[]) >>
  rw[] >> fs[Once subtype_Tyapp] >>
  fs[Q.ISPEC`Tyvar`(Q.SPEC`l`MEM_MAP)] >> rw[] >> fs[] >>
  fs[Once subtype_Tyapp] >> TRY(metis_tac[]) >>
  fs[Q.ISPEC`Tyvar`(Q.SPEC`l`MEM_MAP)] >> rw[] >> fs[] >>
  simp[GSYM mlstring_sort_def] >>
  qmatch_assum_abbrev_tac`aty subtype bty` >>
  `type_ok (tysof ctxt) bty` by (
    (imp_res_tac proves_term_ok >> fs[term_ok_def] >>
     imp_res_tac term_ok_type_ok >> rfs[] >> NO_TAC) ORELSE
    (qspec_then`sigof ctxt`mp_tac type_ok_types_in >> simp[] >>
     disch_then(match_mp_tac) >>
     imp_res_tac proves_term_ok >> fs[term_ok_def] >>
     metis_tac[])) >>
  `type_ok (tysof ctxt) aty` by metis_tac[subtype_type_ok] >>
  fs[Abbr`aty`,type_ok_def] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,EXISTS_PROD] >>
  metis_tac[])

val _ = Parse.type_abbrev("constraints",``:'U list -> ('U list # 'U list) option``)

val constrain_assignment_def = Define`
  constrain_assignment cs p ns f =
    λname args. case cs args of NONE => f name args
    | SOME x => case ALOOKUP (ZIP(ns,p x)) name of NONE => f name args
                   | SOME v => v`

val _ = Parse.overload_on("constrain_tyass",
  ``λcs upd. constrain_assignment cs FST (MAP FST (types_of_upd upd))``)
val _ = Parse.overload_on("constrain_tmass",
  ``λcs upd. constrain_assignment cs SND (MAP FST (consts_of_upd upd))``)

val constrain_interpretation_def = Define`
  constrain_interpretation upd cs ((δ,γ):'U interpretation) =
    (constrain_tyass cs upd δ,
     constrain_tmass cs upd γ)`

val set_tyvars_of_upd_def = new_specification("set_tyvars_of_upd_def",["set_tyvars_of_upd"],
  constrainable_update_def |> SPEC_ALL
  |> EQ_IMP_RULE |> fst
  |> CONV_RULE(HO_REWR_CONV (GSYM RIGHT_EXISTS_IMP_THM))
  |> GEN_ALL
  |> CONV_RULE(HO_REWR_CONV SKOLEM_THM))

val tyvars_of_upd_def = Define`
  tyvars_of_upd upd = mlstring_sort (SET_TO_LIST (set_tyvars_of_upd upd))`

val ALL_DISTINCT_mlstring_sort = store_thm("ALL_DISTINCT_mlstring_sort",
  ``∀ls. ALL_DISTINCT (mlstring_sort ls)``,
  rw[mlstring_sort_def])
val _ = export_rewrites["ALL_DISTINCT_mlstring_sort"]

val ALL_DISTINCT_tyvars_of_upd = store_thm("ALL_DISTINCT_tyvars_of_upd",
  ``∀upd. ALL_DISTINCT (tyvars_of_upd upd)``,
  rw[tyvars_of_upd_def])
val _ = export_rewrites["ALL_DISTINCT_tyvars_of_upd"]

val tyvars_of_TypeDefn = store_thm("tyvars_of_TypeDefn",
  ``TypeDefn name pred abs rep updates ctxt ∧ is_std_sig (sigof ctxt) ⇒
    (tyvars_of_upd (TypeDefn name pred abs rep) = mlstring_sort (tvars pred))``,
  strip_tac >> imp_res_tac TypeDefn_constrainable >>
  imp_res_tac set_tyvars_of_upd_def >>
  pop_assum kall_tac >>
  simp[tyvars_of_upd_def] >>
  qmatch_abbrev_tac`mlstring_sort l1 = mlstring_sort l2` >>
  `ALL_DISTINCT l1 ∧ ALL_DISTINCT l2` by (
     unabbrev_all_tac >> simp[] ) >>
  simp[mlstring_sort_eq] >>
  match_mp_tac sortingTheory.PERM_ALL_DISTINCT >>
  simp[] >>
  simp[GSYM EXTENSION] >>
  unabbrev_all_tac >>
  fs[LET_THM] >>
  fs[updates_cases] >>
  imp_res_tac proves_term_ok >> fs[] >>
  fs[Once has_type_cases] >>
  imp_res_tac WELLTYPED_LEMMA >>
  simp[tyvars_def] >>
  simp[SET_EQ_SUBSET] >>
  reverse conj_tac >- (
    simp[SUBSET_DEF,MEM_FOLDR_LIST_UNION,MEM_MAP,PULL_EXISTS,tyvars_def,
         mlstringTheory.implode_explode]) >>
  imp_res_tac tyvars_typeof_subset_tvars >> fs[tyvars_def] >>
  simp[SUBSET_DEF,MEM_FOLDR_LIST_UNION,MEM_MAP,PULL_EXISTS,tyvars_def,
       mlstringTheory.implode_explode] >>
  fs[SUBSET_DEF] >> metis_tac[])

val tvars_VSUBST_same_type = store_thm("tvars_VSUBST_same_type",
  ``∀tm ilist.
      welltyped tm ∧
      EVERY (λ(x,y). ∃n n' ty. (x = Const n ty ∨ x = Var n' ty) ∧ (y = Var n ty)) ilist ⇒
      tvars (VSUBST ilist tm) = tvars tm``,
  ho_match_mp_tac term_induction >>
  conj_tac >- (
    rw[tvars_def,VSUBST_def] >>
    rw[REV_ASSOCD_ALOOKUP] >>
    BasicProvers.CASE_TAC >> rw[tvars_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[EVERY_MEM,MEM_MAP,EXISTS_PROD] >>
    res_tac >> fs[] >> simp[tvars_def] ) >>
  conj_tac >- rw[VSUBST_def,tvars_def] >>
  conj_tac >- rw[VSUBST_def,tvars_def] >>
  rw[] >> fs[] >>
  rw[tvars_def] >>
  rw[VSUBST_def] >>
  rw[tvars_def,Abbr`z`] >- (
    fs[tvars_def] >>
    AP_TERM_TAC >>
    first_x_assum match_mp_tac >>
    simp[Abbr`ilist''`,Abbr`ilist'`,EVERY_FILTER] >>
    fs[EVERY_MEM] ) >>
  simp[Abbr`t'`] >>
  AP_TERM_TAC >>
  first_x_assum match_mp_tac >>
  simp[Abbr`ilist'`,EVERY_FILTER] >>
  fs[EVERY_MEM])

val VFREE_IN_Const_VSUBST = store_thm("VFREE_IN_Const_VSUBST",
  ``∀tm name ty ilist.
      welltyped tm ⇒
      VFREE_IN (Const name ty) (VSUBST ilist tm) ⇒
      VFREE_IN (Const name ty) tm ∨
      ∃x xy. VFREE_IN (Var x xy) tm ∧ VFREE_IN (Const name ty) (VSUBST ilist (Var x xy))``,
  ho_match_mp_tac term_induction >>
  simp[] >>
  conj_tac >- simp[VSUBST_def] >>
  conj_tac >- (
    rw[VSUBST_def] >>
    metis_tac[] ) >>
  rw[VSUBST_def] >>
  fs[LET_THM] >>
  pop_assum mp_tac >>
  rw[EXISTS_MEM,MEM_FILTER,UNCURRY] >>
  fs[VSUBST_def] >>
  res_tac >> rw[] >>
  fs[REV_ASSOCD,REV_ASSOCD_FILTER] >>
  pop_assum mp_tac >> rw[] >> fs[] >>
  metis_tac[])

val ConstSpec_constrainable = store_thm("ConstSpec_constrainable",
  ``ConstSpec eqs prop updates ctxt ∧
    EVERY (λ(x,t). set (tyvars (typeof t)) = set (tvars prop)) eqs ⇒
    constrainable_update (ConstSpec eqs prop)``,
  strip_tac >>
  simp[constrainable_update_def,conexts_of_upd_def] >>
  `welltyped prop` by (
    fs[updates_cases] >>
    imp_res_tac proves_term_ok >>
    fs[welltyped_def] >> metis_tac[]) >>
  conj_tac >- (
    rw[LET_THM,EVERY_MAP,UNCURRY,EVERY_MEM,
       FORALL_PROD,EXISTS_PROD,MEM_MAP] >>
    fs[EVERY_MEM,FORALL_PROD] >>
    res_tac >>
    pop_assum(SUBST1_TAC) >>
    AP_TERM_TAC >>
    match_mp_tac tvars_VSUBST_same_type >>
    simp[EVERY_MAP,UNCURRY]) >>
  simp[MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
  rw[] >>
  imp_res_tac VFREE_IN_Const_VSUBST >- (
    fs[updates_cases] >>
    imp_res_tac proves_term_ok >> fs[] >>
    imp_res_tac term_ok_VFREE_IN >>
    fs[term_ok_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  fs[VSUBST_def,REV_ASSOCD_ALOOKUP] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >- (
    imp_res_tac ALOOKUP_FAILS >>
    fs[MEM_MAP] ) >>
  strip_tac >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,EXISTS_PROD] >> fs[] >> rw[] >>
  fs[updates_cases] >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >> fs[])

val tyvars_of_ConstSpec = store_thm("tyvars_of_ConstSpec",
  ``welltyped prop ∧ constrainable_update (ConstSpec eqs prop) ⇒
    tyvars_of_upd (ConstSpec eqs prop) = mlstring_sort (tvars prop)``,
  rw[] >> imp_res_tac set_tyvars_of_upd_def >>
  pop_assum kall_tac >>
  rw[tyvars_of_upd_def] >>
  qmatch_abbrev_tac`mlstring_sort l1 = mlstring_sort l2` >>
  `ALL_DISTINCT l1 ∧ ALL_DISTINCT l2` by (
     unabbrev_all_tac >> simp[] ) >>
  simp[mlstring_sort_eq] >>
  match_mp_tac sortingTheory.PERM_ALL_DISTINCT >>
  simp[] >>
  simp[GSYM EXTENSION] >>
  unabbrev_all_tac >>
  simp[SET_TO_LIST_INV] >>
  fs[conexts_of_upd_def,LET_THM] >>
  AP_TERM_TAC >>
  match_mp_tac tvars_VSUBST_same_type >>
  simp[EVERY_MAP,UNCURRY])

val well_formed_constraints_def = xDefine"well_formed_constraints"`
  well_formed_constraints0 ^mem upd cs δ ⇔
    ∀vs tyvs tmvs.
        cs vs = SOME (tyvs,tmvs) ⇒
        EVERY inhabited vs ∧
        LENGTH tyvs = LENGTH (types_of_upd upd) ∧
        EVERY inhabited tyvs ∧
        LENGTH (tyvars_of_upd upd) = LENGTH vs ∧
        ∀τ. is_type_valuation τ ∧ MAP τ (tyvars_of_upd upd) = vs ⇒
          LIST_REL (λv ty. v <: typesem (constrain_tyass cs upd δ) τ ty)
            tmvs (MAP SND (consts_of_upd upd))`
val _ = Parse.overload_on("well_formed_constraints",``well_formed_constraints0 ^mem``)

val well_formed_constraints_implies_lengths = store_thm("well_formed_constraints_implies_lengths",
  ``is_set_theory ^mem ⇒
    well_formed_constraints upd cs δ ⇒
    (∀vs tyvs tmvs.
      (cs vs = SOME (tyvs,tmvs)) ⇒
      (LENGTH tyvs = LENGTH (types_of_upd upd)) ∧
      (LENGTH tmvs = LENGTH (consts_of_upd upd)))``,
  rw[well_formed_constraints_def] >> res_tac >>
  fs[LET_THM] >>
  qmatch_assum_abbrev_tac`LENGTH vars = LENGTH args` >>
  first_x_assum(qspec_then`args`mp_tac) >> simp[] >>
  first_x_assum(qspec_then`K boolset =++ ZIP(vars,args)`mp_tac) >>
  discharge_hyps >- (
    match_mp_tac MAP_ZIP_UPDATE_LIST_ALL_DISTINCT_same >>
    simp[Abbr`vars`] ) >>
  discharge_hyps >- (
    match_mp_tac is_type_valuation_UPDATE_LIST >>
    simp[EVERY_MEM,is_type_valuation_def] >>
    conj_tac >- metis_tac[setSpecTheory.boolean_in_boolset] >>
    simp[MEM_ZIP,PULL_EXISTS] >>
    fs[EVERY_MEM,MEM_EL,PULL_EXISTS]) >>
  simp[LIST_REL_EL_EQN])

val constrain_interpretation_equal_on = store_thm("constrain_interpretation_equal_on",
  ``is_set_theory ^mem ⇒
    ∀upd cs i ctxt.
      constrainable_update upd ∧
      (∀vs tyvs tmvs.
        (cs vs = SOME (tyvs,tmvs)) ⇒
        (LENGTH tyvs = LENGTH (types_of_upd upd)) ∧
        (LENGTH tmvs = LENGTH (consts_of_upd upd))) ∧
      upd updates ctxt ∧ ctxt extends init_ctxt
      ⇒
      equal_on (sigof ctxt) i (constrain_interpretation upd cs i)``,
  rw[] >> Cases_on`i` >>
  fs[equal_on_def,constrain_interpretation_def] >>
  fs[well_formed_constraints_def,constrain_assignment_def] >>
  simp[FUN_EQ_THM] >>
  `upd::ctxt extends init_ctxt` by (
    simp[extends_def,Once relationTheory.RTC_CASES1] >>
    simp[GSYM extends_def] ) >>
  pop_assum(mp_tac o MATCH_MP extends_ALL_DISTINCT) >>
  simp[init_ALL_DISTINCT,ALL_DISTINCT_APPEND] >> strip_tac >>
  rw[term_ok_def,type_ok_def] >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  imp_res_tac ALOOKUP_MEM >>
  Cases_on`x`>>fs[]>>res_tac>>
  fs[LET_THM,LIST_REL_EL_EQN] >>
  fs[ZIP_MAP,MEM_MAP,PULL_EXISTS,FORALL_PROD] >>
  imp_res_tac MEM_ZIP_MEM_MAP >> rfs[] >>
  PairCases_on`p`>>fs[] >>rw[]>>
  Cases_on`y`>>fs[]>>metis_tac[])

val valid_constraints_def = xDefine"valid_constraints"`
  valid_constraints0 ^mem ctxt upd cs i ⇔
    EVERY
      (λp. constrain_interpretation upd cs i satisfies
             (sigof (upd::ctxt), [], p))
      (axioms_of_upd upd)`
val _ = Parse.overload_on("valid_constraints",``valid_constraints0 ^mem``)

val constrain_tyass_is_type_assignment = store_thm("constrain_tyass_is_type_assignment",
  ``∀upd cs δ. is_type_assignment tysig δ ∧
               (∀vs tyvs tmvs.
                 (cs vs = SOME (tyvs,tmvs)) ⇒
                   EVERY inhabited tyvs ∧
                   (LENGTH tyvs = LENGTH (types_of_upd upd))) ⇒
               is_type_assignment tysig (constrain_tyass cs upd δ)``,
  fs[is_type_assignment_def,FEVERY_ALL_FLOOKUP] >> rw[] >>
  res_tac >> rw[constrain_assignment_def] >>
  BasicProvers.CASE_TAC >> rw[] >>
  BasicProvers.CASE_TAC >- metis_tac[] >>
  qmatch_assum_rename_tac`cs ls = SOME p`[]>>
  PairCases_on`p`>>res_tac>>
  imp_res_tac ALOOKUP_MEM>>
  rfs[ZIP_MAP,MEM_MAP] >>
  rfs[EVERY_MEM,MEM_ZIP] >>
  metis_tac[MEM_EL])

val constrain_tmass_is_term_assignment = store_thm("constrain_tmass_is_term_assignment",
  ``is_set_theory ^mem ⇒
    is_term_assignment (tmsof (upd::ctxt)) δ γ ∧
    is_std_type_assignment δ ∧
    is_std_type_assignment (constrain_tyass cs upd δ) ∧
    constrainable_update upd ∧
    well_formed_constraints upd cs δ ∧
    upd updates ctxt ∧ ctxt extends init_ctxt
    ⇒
    is_term_assignment (tmsof (upd::ctxt)) (constrain_tyass cs upd δ) (constrain_tmass cs upd γ)``,
  strip_tac >> simp[] >> strip_tac >>
  `theory_ok (thyof ctxt)` by metis_tac[extends_theory_ok,init_theory_ok] >>
  `theory_ok (thyof (upd::ctxt))` by metis_tac[updates_theory_ok] >>
  `ALL_DISTINCT (MAP FST (type_list (upd::ctxt))) ∧
   ALL_DISTINCT (MAP FST (const_list (upd::ctxt)))` by (
    conj_tac >>
    imp_res_tac updates_ALL_DISTINCT >>
    first_x_assum match_mp_tac >>
    imp_res_tac extends_ALL_DISTINCT >>
    first_x_assum match_mp_tac >>
    EVAL_TAC ) >>
  fs[is_term_assignment_def,FEVERY_ALL_FLOOKUP] >> rw[] >>
  first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
  first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
  rw[constrain_assignment_def] >>
  fs[GSYM mlstring_sort_def] >>
  reverse BasicProvers.CASE_TAC >- (
    fs[well_formed_constraints_def] >>
    qmatch_assum_rename_tac`cs ls = SOME p`["ls"]>>
    PairCases_on`p`>>
    first_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
    fs[LET_THM] >>
    qpat_assum`FLOOKUP X Y = Z`mp_tac >>
    simp[FLOOKUP_FUNION] >>
    BasicProvers.CASE_TAC >- (
      BasicProvers.CASE_TAC >- (
        rw[] >>
        qmatch_abbrev_tac`m <: typesem d1 τ v` >>
        qsuff_tac`typesem d1 τ v = typesem δ τ v` >- rw[] >>
        match_mp_tac typesem_sig >>
        qexists_tac`tysof ctxt` >>
        conj_tac >- (
          fs[theory_ok_def] >>
          first_x_assum match_mp_tac >>
          simp[IN_FRANGE_FLOOKUP] >>
          metis_tac[] ) >>
        simp[type_ok_def,Abbr`d1`,FUN_EQ_THM] >> rw[] >>
        BasicProvers.CASE_TAC >>
        BasicProvers.CASE_TAC >>
        qmatch_assum_rename_tac`cs ls = SOME p`["ls"]>>
        PairCases_on`p`>>
        res_tac >> fs[ZIP_MAP] >>
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP] >>
        imp_res_tac MEM_ZIP_MEM_MAP >>
        rfs[] >>
        PairCases_on`p`>>fs[ALL_DISTINCT_APPEND,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
        Cases_on`y`>>fs[]>>
        metis_tac[] ) >>
      strip_tac >>
      imp_res_tac ALOOKUP_MEM >>
      qpat_assum`∀X. Y`mp_tac >>
      qpat_abbrev_tac`vars = mlstring_sort X` >>
      disch_then(qspec_then`K boolset =++ ZIP(tyvars_of_upd upd, MAP τ vars)`mp_tac) >>
      discharge_hyps >- (
        conj_tac >- (
          match_mp_tac is_type_valuation_UPDATE_LIST >>
          simp[EVERY_MEM,is_type_valuation_def] >>
          conj_tac >- metis_tac[setSpecTheory.boolean_in_boolset] >>
          simp[MEM_ZIP,PULL_EXISTS,Abbr`vars`] >>
          fs[EVERY_MEM,MEM_EL,PULL_EXISTS]) >>
        match_mp_tac MAP_ZIP_UPDATE_LIST_ALL_DISTINCT_same >>
        simp[Abbr`vars`] ) >>
      strip_tac >> imp_res_tac LIST_REL_LENGTH >>
      imp_res_tac MEM_ZIP_MEM_MAP >>
      rfs[] >>
      fs[MEM_MAP,EXISTS_PROD,ALL_DISTINCT_APPEND,PULL_EXISTS] >>
      metis_tac[]) >>
    rw[] >>
    `tyvars_of_upd upd = mlstring_sort (tyvars v)` by (
      simp[tyvars_of_upd_def] >>
      imp_res_tac set_tyvars_of_upd_def >>
      simp[mlstring_sort_eq,ALL_DISTINCT_SET_TO_LIST] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[EVERY_MAP,EVERY_MEM] >> res_tac >> fs[] >>
      metis_tac[sortingTheory.ALL_DISTINCT_PERM_LIST_TO_SET_TO_LIST,
                sortingTheory.PERM_SYM,tyvars_ALL_DISTINCT]) >>
    first_x_assum(qspec_then`τ`mp_tac) >>
    simp[] >>
    strip_tac >> imp_res_tac LIST_REL_LENGTH >>
    BasicProvers.CASE_TAC >- (
      imp_res_tac ALOOKUP_FAILS >>
      imp_res_tac ALOOKUP_MEM >>
      rfs[MEM_MAP,ZIP_MAP,EXISTS_PROD] >>
      rfs[MEM_ZIP,MEM_EL] >>
      metis_tac[] ) >>
    imp_res_tac ALOOKUP_MEM >>
    rfs[LIST_REL_EL_EQN,MEM_ZIP] >>
    first_x_assum(qspec_then`n`mp_tac) >> simp[] >>
    fs[ALL_DISTINCT_APPEND] >>
    `v = EL n (MAP SND (consts_of_upd upd))` by (
      imp_res_tac ALOOKUP_ALL_DISTINCT_EL >> fs[EL_MAP] ) >>
    simp[] >>
    qmatch_abbrev_tac`m <: x1 ⇒ m <: x2` >>
    qsuff_tac`x1 = x2`>-rw[]>>
    unabbrev_all_tac >>
    match_mp_tac typesem_sig >>
    qexists_tac`tysof(upd::ctxt)` >>
    simp[FUN_EQ_THM,constrain_assignment_def] >>
    fs[theory_ok_def] >>
    first_x_assum match_mp_tac >>
    simp[IN_FRANGE_FLOOKUP,FLOOKUP_FUNION] >>
    qexists_tac`EL n (MAP FST (consts_of_upd upd))` >>
    simp[]) >>
  Cases_on`type_ok (tysof ctxt) v` >- (
    qmatch_abbrev_tac`a <: b` >>
    qmatch_assum_abbrev_tac`a <: c` >>
    qsuff_tac `b = c` >- rw[] >>
    unabbrev_all_tac >>
    match_mp_tac typesem_sig >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp[type_ok_def] >> rw[FUN_EQ_THM] >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    fs[well_formed_constraints_def,ALL_DISTINCT_APPEND] >>
    qmatch_assum_rename_tac`cs ls = SOME p`["ls"]>>
    PairCases_on`p`>>res_tac>>
    imp_res_tac ALOOKUP_MEM >> rfs[MEM_MAP,EXISTS_PROD,ZIP_MAP]>>
    imp_res_tac MEM_ZIP_MEM_MAP >> rfs[] >>
    metis_tac[]) >>
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
    rpt AP_THM_TAC >> AP_TERM_TAC >> rw[FUN_EQ_THM] >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    fs[well_formed_constraints_def] >>
    qmatch_assum_rename_tac`cs ls = SOME p`["ls"]>>
    PairCases_on`p`>>res_tac>>
    fs[LENGTH_NIL]) >>
  qmatch_abbrev_tac`typesem d1 τ v = typesem δ τ v` >>
  `is_std_type_assignment d1 ∧
   is_std_type_assignment δ` by (
     reverse conj_asm2_tac >- fs[is_std_interpretation_def] >>
     simp[Abbr`d1`,GSYM constrain_assignment_def] ) >>
  rator_x_assum`ALOOKUP` mp_tac >> simp[] >>
  Q.PAT_ABBREV_TAC`t1 = domain (typeof pred)` >>
  Q.PAT_ABBREV_TAC`t2 = Tyapp name X` >>
  fs[GSYM mlstring_sort_def] >>
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
    match_mp_tac typesem_sig >>
    qexists_tac`tysof (ctxt)` >>
    imp_res_tac proves_term_ok >>
    qpat_assum`k ∈ X`kall_tac >>
    fs[term_ok_def] >>
    conj_tac >- (
      imp_res_tac term_ok_type_ok >>
      fs[theory_ok_def] ) >>
    simp[type_ok_def] >> rw[FUN_EQ_THM] >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    fs[well_formed_constraints_def] >>
    qmatch_assum_rename_tac`cs ls = SOME p`["ls"]>>
    PairCases_on`p`>>res_tac>>
    imp_res_tac ALOOKUP_MEM >> rfs[MEM_MAP,EXISTS_PROD,ZIP_MAP]>>
    imp_res_tac MEM_ZIP_MEM_MAP >> rfs[] >>
    metis_tac[]) >>
  unabbrev_all_tac >>
  simp[typesem_def,MAP_MAP_o,combinTheory.o_DEF,ETA_AX] >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  qsuff_tac`set (tyvars v) = set (tvars pred)` >- (
    qpat_assum`set (tyvars v) = X`kall_tac >>
    rw[] >>
    `mlstring_sort (tvars pred) = mlstring_sort (tyvars v)` by (
      `ALL_DISTINCT (tvars pred)` by simp[] >>
      `ALL_DISTINCT (tyvars v)` by simp[] >>
      simp[mlstring_sort_eq] >>
      match_mp_tac sortingTheory.PERM_ALL_DISTINCT >>
      fs[pred_setTheory.EXTENSION]) >>
    fs[IS_SOME_EXISTS,PULL_EXISTS,LET_THM,MAP_MAP_o,combinTheory.o_DEF]) >>
  simp[tyvars_def,pred_setTheory.EXTENSION,
       holSyntaxLibTheory.MEM_FOLDR_LIST_UNION,
       MEM_MAP,PULL_EXISTS] >>
  imp_res_tac proves_term_ok >> fs[term_ok_def] >>
  fs[WELLTYPED] >>
  imp_res_tac tyvars_typeof_subset_tvars >>
  fs[pred_setTheory.SUBSET_DEF,tyvars_def] >>
  simp[mlstring_sort_def,MEM_MAP,PULL_EXISTS] >>
  metis_tac[mlstringTheory.implode_explode] )

val add_constraints_thm = store_thm("add_constraints_thm",
  ``is_set_theory ^mem ⇒
    ∀i upd ctxt cs.
      constrainable_update upd ∧
      upd updates ctxt ∧ ctxt extends init_ctxt ∧
      i models (thyof (upd::ctxt)) ∧
      well_formed_constraints upd cs (tyaof i) ∧
      valid_constraints ctxt upd cs i
      ⇒
      constrain_interpretation upd cs i models thyof (upd::ctxt)``,
  rw[] >> fs[models_def] >>
  REWRITE_TAC[CONJ_ASSOC] >>
  `theory_ok (thyof ctxt)` by metis_tac[extends_theory_ok,init_theory_ok] >>
  `theory_ok (thyof (upd::ctxt))` by metis_tac[updates_theory_ok] >>
  `∃δ γ. i =(δ,γ)` by metis_tac[pair_CASES] >>
  `ALL_DISTINCT (MAP FST (type_list (upd::ctxt))) ∧
   ALL_DISTINCT (MAP FST (const_list (upd::ctxt)))` by (
    conj_tac >>
    imp_res_tac updates_ALL_DISTINCT >>
    first_x_assum match_mp_tac >>
    imp_res_tac extends_ALL_DISTINCT >>
    first_x_assum match_mp_tac >>
    EVAL_TAC ) >>
  conj_asm1_tac >- (
    conj_asm2_tac >- (
      simp[is_interpretation_def] >>
      conj_tac >- (
        simp[constrain_interpretation_def] >>
        match_mp_tac constrain_tyass_is_type_assignment >>
        fs[is_interpretation_def] >>
        imp_res_tac well_formed_constraints_implies_lengths >>
        fs[well_formed_constraints_def] >>
        metis_tac[] ) >>
      simp[constrain_interpretation_def] >>
      match_mp_tac (GEN_ALL(UNDISCH(SIMP_RULE (srw_ss())[]constrain_tmass_is_term_assignment))) >>
      simp[] >> fs[is_interpretation_def] >>
      fs[is_std_interpretation_def] >>
      rfs[constrain_interpretation_def] ) >>
    fs[is_interpretation_def,is_std_interpretation_def,constrain_interpretation_def] >>
    conj_asm1_tac >- (
      fs[is_std_type_assignment_def,constrain_assignment_def] >>
      imp_res_tac theory_ok_sig >>
      fs[is_std_sig_def,IS_SOME_EXISTS,PULL_EXISTS] >>
      imp_res_tac ALOOKUP_MEM >>
      rw[] >> fs[ALL_DISTINCT_APPEND] >>
      BasicProvers.CASE_TAC >>
      res_tac >> fs[] >> rw[] >>
      rpt (BasicProvers.CASE_TAC >> res_tac >> fs[]) >>
      fs[well_formed_constraints_def] >>
      qmatch_assum_rename_tac`cs ls = SOME p`["ls"]>>
      PairCases_on`p`>>res_tac>>
      imp_res_tac ALOOKUP_MEM >> rfs[MEM_MAP,EXISTS_PROD,ZIP_MAP]>>
      imp_res_tac MEM_ZIP_MEM_MAP >> rfs[] >>
      metis_tac[]) >>
    fs[interprets_def,constrain_assignment_def] >> rw[] >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    imp_res_tac ALOOKUP_MEM >>
    imp_res_tac well_formed_constraints_implies_lengths >>
    fs[well_formed_constraints_def] >>
    qmatch_assum_rename_tac`cs ls = SOME p`["ls"]>>
    PairCases_on`p`>>res_tac>>
    fs[LET_THM] >>
    qmatch_assum_abbrev_tac`LENGTH ls = 1` >>
    first_x_assum(qspec_then`((HD ls) =+ (τ(strlit"A"))) (K boolset)`mp_tac) >>
    discharge_hyps >- (
      Cases_on`ls`>>fs[LENGTH_NIL] >>
      simp[is_type_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
      rw[] >> metis_tac[setSpecTheory.boolean_in_boolset]) >> strip_tac >>
    imp_res_tac LIST_REL_LENGTH >> fs[] >>
    imp_res_tac MEM_ZIP_MEM_MAP >> rfs[] >>
    imp_res_tac theory_ok_sig >>
    fs[is_std_sig_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[ALL_DISTINCT_APPEND,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
    metis_tac[]) >>
  gen_tac >>
  qmatch_abbrev_tac`P ⇒ q` >>
  strip_tac >> qunabbrev_tac`q` >>
  first_x_assum(qspec_then`p`mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on`MEM p (axiom_list ctxt)` >- (
    fs[Abbr`P`] >>
    `term_ok (sigof ctxt) p` by (
      fs[theory_ok_def]) >>
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
    match_mp_tac satisfies_sig >>
    qexists_tac`i` >> simp[] >> fs[] >>
    conj_tac >- (
      match_mp_tac (UNDISCH constrain_interpretation_equal_on) >>
      simp[] >>
      imp_res_tac well_formed_constraints_implies_lengths >>
      metis_tac[]) >>
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
      simp[] >>
      conj_tac >- (
        fs[theory_ok_def] >>
        metis_tac[term_ok_welltyped] ) >>
      rw[] >>
      first_x_assum match_mp_tac >>
      imp_res_tac term_ok_VFREE_IN >>
      fs[term_ok_def] ) >>
    metis_tac[termsem_extend]) >>
  fs[valid_constraints_def] >>
  fs[markerTheory.Abbrev_def,EVERY_MEM])

val lemma = prove(
  ``∀i e ty0. ty0 = TYPE_SUBST i ty0 ∧ REV_ASSOCD (Tyvar e) i (Tyvar e) ≠ Tyvar e ∧ MEM e (tyvars ty0) ⇒ F``,
  ntac 2 gen_tac >>
  ho_match_mp_tac type_ind >>
  rw[tyvars_def,MEM_FOLDR_LIST_UNION] >- metis_tac[] >>
  fs[EVERY_MEM] >>
  fsrw_tac[boolSimps.ETA_ss][] >>
  spose_not_then strip_assume_tac >>
  res_tac >>
  fs[LIST_EQ_REWRITE,EL_MAP] >>
  fs[MEM_EL] >>
  metis_tac[])

val constrain_interpretation_satisfies = store_thm("constrain_interpretation_satisfies",
  ``is_set_theory ^mem ⇒
    ∀j upd ctxt cs.
    constrainable_update upd ∧ upd updates ctxt ∧ theory_ok (thyof ctxt) ∧
    (axexts_of_upd upd = []) ∧
    j models (thyof (upd::ctxt)) ∧
    (∀vs. IS_SOME (cs vs) ⇒
            LENGTH (FST(THE(cs vs))) = LENGTH (types_of_upd upd) ∧
            LENGTH (SND(THE(cs vs))) = LENGTH (consts_of_upd upd)) ∧
    EVERY (λx.
      (∀vs. IS_SOME (cs vs) ⇒
         ∀tyval tmval.
             is_valuation (tysof (upd::ctxt)) (tyaof (constrain_interpretation upd cs j)) (tyval,tmval) ⇒
             MAP tyval (tyvars_of_upd upd) = vs ⇒
             termsem (tmsof (upd::ctxt)) (constrain_interpretation upd cs j) (tyval,tmval) x = True))
      (axioms_of_upd upd)
    ⇒
    valid_constraints ctxt upd cs j``,
  strip_tac >>
  rpt gen_tac >>
  qabbrev_tac`axs = axioms_of_upd upd` >>
  REWRITE_TAC[valid_constraints_def] >>
  ASM_SIMP_TAC pure_ss [] >>
  qabbrev_tac`sig = sigof(upd::ctxt)` >>
  qabbrev_tac`tysig = tysof (upd::ctxt)` >>
  qabbrev_tac`tmsig = tmsof (upd::ctxt)` >>
  simp[EVERY_MEM,models_def] >> strip_tac >>
  rw[] >>
  rfs[Abbr`axs`] >>
  first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
  first_x_assum(qspec_then`p`mp_tac) >> simp[] >> strip_tac >>
  simp[satisfies_def] >> rw[] >>
  `tysof sig = tysig` by simp[Abbr`tysig`,Abbr`sig`] >> fs[] >> pop_assum kall_tac >>
  pop_assum mp_tac >> PairCases_on`v`>>simp[is_valuation_def] >> strip_tac >>
  `tyvars_of_upd upd = mlstring_sort (tvars p)` by (
    simp[tyvars_of_upd_def] >>
    qmatch_abbrev_tac`mlstring_sort l1 = mlstring_sort l2` >>
    `ALL_DISTINCT l1 ∧ ALL_DISTINCT l2` by (
      imp_res_tac set_tyvars_of_upd_def >>
      simp[Abbr`l1`,Abbr`l2`] ) >>
    simp[mlstring_sort_eq] >>
    match_mp_tac sortingTheory.PERM_ALL_DISTINCT >>
    simp[GSYM EXTENSION] >>
    simp[Abbr`l1`,Abbr`l2`] >>
    imp_res_tac set_tyvars_of_upd_def >>
    simp[SET_TO_LIST_INV] >>
    fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] ) >>
  Cases_on`cs (MAP v0 (tyvars_of_upd upd))` >- (
    fs[satisfies_def] >>
    `∃v2. is_valuation (tysof sig) (tyaof j) (v0,v2)` by (
      match_mp_tac (UNDISCH term_valuation_exists) >>
      fs[is_interpretation_def] ) >>
    qabbrev_tac`v3 = λ(x,ty). if VFREE_IN (Var x ty) p then v1 (x,ty) else v2 (x,ty)` >>
    `is_valuation (tysof sig) (tyaof j) (v0,v3)` by (
      fs[is_valuation_def] >>
      fs[is_term_valuation_def] >> rw[] >>
      rw[Abbr`v3`] >>
      last_x_assum(qspecl_then[`v`,`ty`]mp_tac) >>
      discharge_hyps >- ( fs[Abbr`tysig`,Abbr`sig`] ) >>
      qmatch_abbrev_tac`m <: t1 ⇒ m <: t2` >>
      qsuff_tac`t1=t2`>-rw[] >>
      map_every qunabbrev_tac[`t1`,`t2`] >>
      qmatch_assum_abbrev_tac`cs vs = NONE` >>
      match_mp_tac typesem_consts >> rw[] >>
      reverse(Cases_on`∃arity. MEM (name,arity) (types_of_upd upd)`)>>fs[]>-(
        disj1_tac >>
        PairCases_on`j` >>
        rw[constrain_interpretation_def,constrain_assignment_def] >>
        simp[FUN_EQ_THM] >>
        qx_gen_tac`args2` >>
        BasicProvers.CASE_TAC >>
        BasicProvers.CASE_TAC >>
        last_x_assum(qspec_then`args2`mp_tac) >>
        rw[] >>
        imp_res_tac ALOOKUP_MEM >>
        rfs[ZIP_MAP,MEM_MAP,EXISTS_PROD] >>
        rfs[MEM_ZIP,MEM_EL] >>
        metis_tac[] ) >>
      disj2_tac >>
      imp_res_tac set_tyvars_of_upd_def >>
      pop_assum mp_tac >> simp[] >>
      disch_then(qspecl_then[`name`,`arity`]mp_tac) >> simp[] >>
      strip_tac >>
      pop_assum(qspecl_then[`args`,`ty`]mp_tac) >> simp[] >>
      discharge_hyps >- (
        disj1_tac >>
        imp_res_tac VFREE_IN_types_in >> fs[] >>
        simp[MEM_MAP,PULL_EXISTS] >>
        metis_tac[] ) >>
      rw[] >>
      rw[GSYM tyvars_of_upd_def] >>
      qexists_tac`mlstring_sort (tvars p)` >>
      PairCases_on`j` >>
      rw[constrain_interpretation_def] >>
      rw[constrain_assignment_def] >>
      BasicProvers.CASE_TAC >>
      BasicProvers.CASE_TAC >>
      rfs[Abbr`vs`] ) >>
    first_x_assum(qspec_then`v0,v3`mp_tac) >> simp[] >>
    disch_then(SUBST1_TAC o SYM) >>
    match_mp_tac EQ_TRANS >>
    qexists_tac`termsem (tmsof sig) (constrain_interpretation upd cs j) (v0,v3) p` >>
    `welltyped p ∧ term_ok sig p` by (
      imp_res_tac updates_theory_ok >>
      fs[theory_ok_def] >>
      simp[welltyped_def] >>
      metis_tac[] ) >>
    conj_tac >- (
      match_mp_tac termsem_frees >> simp[] >>
      simp[Abbr`v3`] ) >>
    match_mp_tac termsem_consts >> simp[] >>
    PairCases_on`j` >> simp[constrain_interpretation_def] >>
    `∀t. t subterm p ⇒
        ∀ty. ty subtype (typeof t) ⇒
            typesem (constrain_tyass cs upd j0) v0 ty = typesem j0 v0 ty` by (
      gen_tac >> strip_tac >>
      imp_res_tac set_tyvars_of_upd_def >>
      pop_assum mp_tac >> simp[] >> strip_tac >>
      ho_match_mp_tac type_ind >>
      conj_tac >- simp[typesem_def] >>
      qx_gen_tac`args2`>>strip_tac >>
      qx_gen_tac`name` >> strip_tac >>
      simp[typesem_def] >>
      simp_tac (std_ss++boolSimps.ETA_ss)[] >>
      `MAP (typesem (constrain_tyass cs upd j0) v0) args2 =
       MAP (typesem j0 v0) args2` by (
        simp[MAP_EQ_f] >>
        fs[EVERY_MEM] >>
        qx_gen_tac`ty2`>>strip_tac >>
        first_x_assum(qspec_then`ty2`mp_tac) >>
        simp[] >>
        discharge_hyps >- (
          simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
          qexists_tac`Tyapp name args2` >>
          simp[subtype_Tyapp] >>
          disj2_tac >>
          qexists_tac`ty2` >>
          simp[] ) >>
        rw[] ) >>
      reverse(Cases_on`∃arity. MEM (name,arity) (types_of_upd upd)`)>>fs[]>-(
        simp[typesem_def] >>
        simp[constrain_assignment_def] >>
        BasicProvers.CASE_TAC >>
        fs[GSYM constrain_assignment_def] >>
        BasicProvers.CASE_TAC >>
        imp_res_tac ALOOKUP_MEM >>
        qmatch_assum_abbrev_tac`cs vs = SOME x` >>
        last_x_assum(qspec_then`vs`mp_tac) >>
        simp[] >> strip_tac >>
        fs[ZIP_MAP,MEM_MAP,EXISTS_PROD] >>
        fs[MEM_ZIP,MEM_EL] >>
        metis_tac[] ) >>
      simp[typesem_def] >>
      simp[Once constrain_assignment_def] >>
      BasicProvers.CASE_TAC >>
      BasicProvers.CASE_TAC >>
      first_x_assum(qspecl_then[`name`,`arity`]mp_tac) >> simp[] >>
      strip_tac >>
      qsuff_tac`MAP v0 (tyvars_of_upd upd) = MAP (typesem j0 v0) args2` >- (
        metis_tac[optionTheory.NOT_SOME_NONE] ) >>
      qspecl_then[`t`,`p`,`name`,`args2`]mp_tac subterm_typeof_types_in >>
      simp[] >>
      discharge_hyps >- (
        spose_not_then strip_assume_tac >>
        imp_res_tac updates_upd_DISJOINT >>
        imp_res_tac theory_ok_sig >>
        fs[is_std_sig_def] >>
        imp_res_tac ALOOKUP_MEM >>
        fs[IN_DISJOINT,MEM_MAP,EXISTS_PROD] >>
        metis_tac[] ) >>
      strip_tac >>
      first_x_assum(qspecl_then[`args2`,`ty2`]mp_tac) >> simp[] >>
      discharge_hyps >- (
        simp[MEM_MAP,PULL_EXISTS] >>
        metis_tac[] ) >>
      rw[MAP_MAP_o,combinTheory.o_DEF,typesem_def,ETA_AX] >>
      AP_TERM_TAC >>
      simp[GSYM mlstring_sort_SET_TO_LIST_set_tvars] >>
      AP_TERM_TAC >> AP_TERM_TAC >>
      fs[EVERY_MEM,MEM_MAP,EXISTS_PROD,PULL_EXISTS] ) >>
    reverse conj_tac >- (
      metis_tac[relationTheory.RTC_REFL] ) >>
    imp_res_tac set_tyvars_of_upd_def >>
    rpt gen_tac >> strip_tac >>
    fs[EVERY_MEM] >>
    first_x_assum(qspec_then`p`mp_tac) >>
    simp[] >> disch_then(qspecl_then[`name`,`ty`]mp_tac) >> simp[] >>
    strip_tac >>
    imp_res_tac term_ok_VFREE_IN >>
    pop_assum mp_tac >>
    simp[Abbr`sig`,term_ok_def] >> strip_tac >>
    qspecl_then[`tmsig`,`j0,j1`,`name`,`ty`]mp_tac instance_def >>
    simp[] >> disch_then kall_tac >>
    qspecl_then[`tmsig`,`constrain_interpretation upd cs (j0,j1)`,`name`,`ty`]mp_tac instance_def >>
    simp[constrain_interpretation_def] >> disch_then kall_tac >>
    simp[GSYM mlstring_sort_def] >>
    rator_x_assum`FLOOKUP`mp_tac >>
    simp[Abbr`tmsig`,FLOOKUP_FUNION] >>
    BasicProvers.CASE_TAC >- (
      rw[Once constrain_assignment_def] >>
      ntac 2 (
        BasicProvers.CASE_TAC >- (
          AP_TERM_TAC >>
          simp[MAP_EQ_f] >>
          simp[mlstring_sort_def,MEM_MAP,PULL_EXISTS,mlstringTheory.implode_explode] >>
          rw[] >>
          first_x_assum(match_mp_tac o MP_CANON) >>
          imp_res_tac VFREE_IN_subterm >>
          first_assum(match_exists_tac o concl) >> simp[] >>
          ONCE_REWRITE_TAC[GSYM TYPE_SUBST_def] >>
          metis_tac[TYPE_SUBST_tyvars_subtype_lemma] )) >>
      imp_res_tac ALOOKUP_MEM >>
      imp_res_tac ALOOKUP_FAILS >>
      qmatch_assum_abbrev_tac`cs vs = SOME x` >>
      last_x_assum(qspec_then`vs`mp_tac) >>
      simp[] >> strip_tac >>
      fs[ZIP_MAP,MEM_MAP,EXISTS_PROD] >>
      fs[MEM_ZIP,MEM_EL] >>
      metis_tac[] ) >>
    rw[] >>
    `MAP (typesem (constrain_tyass cs upd j0) v0 o TYPE_SUBST i o Tyvar) (mlstring_sort (tyvars ty0)) =
     MAP (typesem j0 v0 o TYPE_SUBST i o Tyvar) (mlstring_sort (tyvars ty0))` by (
      simp[MAP_EQ_f] >>
      fs[EVERY_MEM] >>
      simp[mlstring_sort_def,MEM_MAP,PULL_EXISTS,mlstringTheory.implode_explode] >>
      rw[] >>
      first_x_assum(match_mp_tac o MP_CANON) >>
      imp_res_tac VFREE_IN_subterm >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      ONCE_REWRITE_TAC[GSYM TYPE_SUBST_def] >>
      metis_tac[TYPE_SUBST_tyvars_subtype_lemma] ) >>
    rw[Once constrain_assignment_def] >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    qsuff_tac`MAP v0 (tyvars_of_upd upd) = MAP (typesem j0 v0 o TYPE_SUBST i o Tyvar) (mlstring_sort (tyvars ty0))` >- (
      metis_tac[optionTheory.NOT_SOME_NONE] ) >>
    `mlstring_sort (tyvars ty0) = tyvars_of_upd upd` by (
      fs[MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
      fs[tyvars_of_upd_def] >>
      qpat_assum`X = mlstring_sort (tvars p)`(mp_tac o SYM) >>
      simp[] >> strip_tac >>
      imp_res_tac ALOOKUP_MEM >>
      res_tac >>
      first_x_assum(CHANGED_TAC o SUBST1_TAC) >>
      qmatch_abbrev_tac`mlstring_sort l1 = mlstring_sort l2` >>
      `ALL_DISTINCT l1 ∧ ALL_DISTINCT l2` by (
        imp_res_tac set_tyvars_of_upd_def >>
        simp[Abbr`l1`,Abbr`l2`] ) >>
      simp[mlstring_sort_eq] >>
      match_mp_tac sortingTheory.PERM_ALL_DISTINCT >>
      simp[GSYM EXTENSION] >>
      unabbrev_all_tac >>
      metis_tac[SET_TO_LIST_INV,FINITE_LIST_TO_SET] ) >>
    pop_assum (SUBST1_TAC o SYM) >>
    simp[MAP_EQ_f,mlstring_sort_def,MEM_MAP,PULL_EXISTS,mlstringTheory.implode_explode] >>
    rw[] >>
    imp_res_tac ALOOKUP_MEM >>
    `ty0 = TYPE_SUBST i ty0` by metis_tac[] >>
    qsuff_tac`REV_ASSOCD (Tyvar e) i (Tyvar e) = Tyvar e`>-rw[typesem_def] >>
    spose_not_then strip_assume_tac >>
    metis_tac[lemma] ) >>
  first_x_assum(qspec_then`MAP v0 (tyvars_of_upd upd)`mp_tac) >> simp[] >>
  simp[is_valuation_def,FORALL_PROD,Abbr`sig`])

val _ = export_theory()
