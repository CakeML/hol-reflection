open HolKernel boolLib bossLib lcsymtacs
open pred_setTheory cardinalTheory
open ordinalTheory wellorderTheory
open setSpecTheory miscLib
val _ = new_theory"lca"

(* TODO: move *)
val MULT_LE_EXP = store_thm("MULT_LE_EXP",
  ``∀a:num b. a ≠ 1 ⇒ a * b ≤ a ** b``,
  Induct_on`b` >> simp[arithmeticTheory.MULT,arithmeticTheory.EXP] >>
  Cases >> simp[] >> strip_tac >>
  first_x_assum(qspec_then`SUC n`mp_tac) >>
  simp[arithmeticTheory.MULT] >>
  Cases_on`b=0` >- (
    simp[arithmeticTheory.EXP] ) >>
  `SUC b ≤ b + b * n` suffices_by simp[] >>
  simp[arithmeticTheory.ADD1] >>
  Cases_on`b * n` >> simp[] >>
  fs[arithmeticTheory.MULT_EQ_0] >> fs[])

val domain_rrestrict_subset = store_thm("domain_rrestrict_subset",
  ``domain (rrestrict r s) ⊆ domain r ∩ s``,
  rw[set_relationTheory.domain_def,
     set_relationTheory.rrestrict_def,
     SUBSET_DEF] >> metis_tac[])

val range_rrestrict_subset = store_thm("range_rrestrict_subset",
  ``range (rrestrict r s) ⊆ range r ∩ s``,
  rw[set_relationTheory.range_def,
     set_relationTheory.rrestrict_def,
     SUBSET_DEF] >> metis_tac[])

(* -- *)

val strong_limit_cardinal_def = Define`
  strong_limit_cardinal X ⇔
    ∀x. x ⊆ X ∧ x ≺ X ⇒ POW x ≺ X`

val strong_infinite = store_thm("strong_infinite",
  ``strong_limit_cardinal X ∧ X ≠ ∅ ⇒ INFINITE X``,
  rpt strip_tac >>
  fs[strong_limit_cardinal_def] >>
  first_x_assum(qspec_then`REST X`mp_tac) >>
  `CARD X ≠ 0` by simp[] >>
  simp[REST_SUBSET] >>
  simp[cardlt_lenoteq] >>
  simp[CARDLEQ_CARD,FINITE_POW,CARD_POW] >>
  simp[CARD_REST,CARDEQ_CARD_EQN] >>
  qspecl_then[`CARD X`,`1`,`2`]mp_tac arithmeticTheory.EXP_SUB >>
  simp[] >> strip_tac >>
  simp[arithmeticTheory.X_LE_DIV] >>
  simp[MULT_LE_EXP])

val limitation_of_size_def = Define`
  limitation_of_size X ⇔
    ∃f. BIJ f X { x | x ⊆ X ∧ x ≺ X}`

(*
val limitation_of_size_alt = store_thm("limitation_of_size_alt",
  ``limitation_of_size X ⇔
    {x | x ⊆ X ∧ x ≺ X} ≼ X``,
  rw[GSYM cardeq_def,limitation_of_size_def] >>
  EQ_TAC >- metis_tac[CARDEQ_SUBSET_CARDLEQ,cardeq_SYM] >>
  strip_tac >>
  match_mp_tac cardleq_ANTISYM >> simp[] >>
  Cases_on`∃x. X ⊆ {x}` >- (
    fs[] >>
    simp[Once cardleq_def] >>
    qexists_tac`K {}` >>
    simp[INJ_DEF] >>
    Cases_on`X = {}` >> simp[] >>
    `X = {x}` by (
      fs[SUBSET_DEF,EXTENSION] >>
      metis_tac[] ) >>
    simp[cardleq_def] ) >>
  simp[Once cardleq_def] >>
  qexists_tac`λx. {x}` >>
  simp[INJ_DEF] >> rw[] >>
  simp[Once cardleq_lteq] >>
  conj_tac >- (
    match_mp_tac SUBSET_CARDLEQ >>
    simp[] ) >>

  rw[limitation_of_size_def,EQ_IMP_THM] >- (
    simp[Once cardleq_def] >>
    metis_tac[BIJ_LINV_BIJ,BIJ_DEF] ) >>
  pop_assum (strip_assume_tac o SIMP_RULE std_ss [Once cardleq_def]) >>
  qho_match_abbrev_tac`∃f. BIJ f a b` >>
  `∃f. BIJ f b a` suffices_by metis_tac[BIJ_LINV_BIJ] >>
  qunabbrev_tac`a` >>
  f"cardeq"
  simp[BIJ_DEF] >> qexists_tac`f` >> simp[] >>
  simp[Abbr`b`,SURJ_DEF] >>
  conj_tac >- fs[INJ_DEF]

  fs[
    fs[BIJ_DEF] >>
    first_assum(match_exists_tac o conc
*)

val minWO_exists = prove(
  ``∀s. ∃wo. elsOf wo = s ∧
             (∀x. x ∈ s ⇒ iseg wo x ≺ s)``,
  gen_tac >>
  qspec_then`s`strip_assume_tac allsets_wellorderable >>
  qho_match_abbrev_tac`∃wo. P wo ∧ Q wo` >>
  Cases_on`Q wo` >- metis_tac[] >>
  qunabbrev_tac`Q` >> pop_assum mp_tac >>
  simp[] >>
  qho_match_abbrev_tac`(∃x. A x) ⇒ B` >>
  `(∃x. A x ∧ ∀z. (z,x) WIN wo ⇒ ¬A z) ⇒ B` suffices_by (
    rw[] >> first_x_assum match_mp_tac >>
    qabbrev_tac`R = λp. p WIN wo` >>
    `wellfounded R` by (
      simp[Abbr`R`,WIN_WF] ) >>
    fs[wellfounded_def,Abbr`R`] >>
    pop_assum(qspec_then`A`mp_tac) >>
    simp[IN_DEF] >> metis_tac[]) >>
  strip_tac >>
  fs[Abbr`A`,Abbr`B`] >>
  `s ≈ iseg wo x` by (
    match_mp_tac cardleq_ANTISYM >> simp[] >>
    simp[cardleq_def] >>
    qexists_tac`I` >>
    simp[INJ_DEF] >>
    simp[iseg_def] >>
    metis_tac[WIN_elsOf] ) >>
  `∃f. BIJ f (iseg wo x) s` by metis_tac[cardeq_def,BIJ_LINV_BIJ] >>
  qabbrev_tac`wo2 = IMAGE (f ## f) (rrestrict (destWO wo) (iseg wo x))` >>
  `wellorder wo2` by (
    simp[Abbr`wo2`] >>
    match_mp_tac (GEN_ALL INJ_preserves_wellorder) >>
    REWRITE_TAC[RIGHT_EXISTS_AND_THM] >>
    conj_tac >- (
      metis_tac[wellorder_cases,wellorder_rrestrict,destWO_mkWO] ) >>
    qexists_tac`s` >>
    match_mp_tac INJ_SUBSET >>
    fs[BIJ_DEF] >>
    first_assum(match_exists_tac o concl) >>
    simp[] >>
    metis_tac[SUBSET_TRANS,SUBSET_INTER,domain_rrestrict_subset,range_rrestrict_subset]) >>
  qexists_tac`mkWO wo2` >>
  simp[Abbr`P`] >>
  conj_tac >- (
    simp[elsOf_def,destWO_mkWO] >>
    simp[Abbr`wo2`,domain_IMAGE_ff,range_IMAGE_ff] >>
    `s = IMAGE f (iseg wo x)` by (
      match_mp_tac EQ_SYM >>
      REWRITE_TAC[GSYM IMAGE_SURJ] >>
      metis_tac[BIJ_DEF] ) >>
    pop_assum SUBST1_TAC >>
    REWRITE_TAC[GSYM IMAGE_UNION] >>
    AP_TERM_TAC >>
    simp[SET_EQ_SUBSET] >>
    conj_tac >- (
      metis_tac[domain_rrestrict_subset,range_rrestrict_subset,SUBSET_TRANS,SUBSET_INTER] ) >>
    simp[SUBSET_DEF,set_relationTheory.domain_def,set_relationTheory.range_def,set_relationTheory.rrestrict_def] >>
    simp[iseg_def] >>
    qx_gen_tac`y` >> strip_tac >>
    simp[WLE_WIN_EQ] >>
    metis_tac[WIN_elsOf] ) >>
  qx_gen_tac`z` >> strip_tac >>
  `LINV f (iseg wo x) z ∈ iseg wo x` by (
    metis_tac[BIJ_LINV_BIJ,BIJ_DEF,INJ_DEF] ) >>
  `(LINV f (iseg wo x) z,x) WIN wo` by ( fs[iseg_def] ) >>
  first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  `LINV f (iseg wo x) z ∈ s` by (
    fs[iseg_def] >>
    metis_tac[WIN_elsOf] ) >>
  simp[] >>
  qabbrev_tac`invf = LINV f (iseg wo x)` >>
  qmatch_abbrev_tac`a ≺ s ⇒ a' ≺ s` >>
  `a ≈ a'` suffices_by metis_tac[cardleq_lt_trans,cardleq_lteq,cardeq_SYM] >>
  unabbrev_all_tac >>
  simp[cardeq_def] >>
  qexists_tac`f` >>
  qabbrev_tac`invf = LINV f (iseg wo x)` >>
  qmatch_abbrev_tac`BIJ f a b` >>
  `∃c. z = f c ∧ c ∈ iseg wo x` by PROVE_TAC[BIJ_DEF,SURJ_DEF] >>
  `invf z = c` by (
    fs[BIJ_DEF] >> imp_res_tac LINV_DEF >> rfs[] ) >>
  `b = IMAGE f a` by (
    map_every qunabbrev_tac[`a`,`b`] >>
    simp[EXTENSION,Once iseg_def,destWO_mkWO] >>
    simp[Once iseg_def,SimpRHS] >>
    qx_gen_tac`y` >>
    EQ_TAC >- (
      simp[Once set_relationTheory.strict_def,pairTheory.EXISTS_PROD] >>
      simp[set_relationTheory.rrestrict_def] >> strip_tac >>
      first_assum(match_exists_tac o concl) >> rw[] >>
      fs[BIJ_DEF] >> imp_res_tac LINV_DEF >> rfs[] >>
      metis_tac[WLE_WIN_EQ] ) >>
    strip_tac >>
    simp[Once set_relationTheory.strict_def,pairTheory.EXISTS_PROD] >>
    simp[set_relationTheory.rrestrict_def] >>
    fs[] >>
    qmatch_assum_rename_tac`(d,c) WIN wo` >>
    conj_tac >- (
      map_every qexists_tac[`d`,`c`] >> simp[] >>
      fs[iseg_def] >>
      metis_tac[WLE_WIN_EQ,WIN_TRANS] ) >>
    `d ∈ iseg wo x` by (
      fs[iseg_def] >>
      metis_tac[WIN_TRANS] ) >>
    metis_tac[BIJ_DEF,INJ_DEF,WIN_REFL] ) >>
  BasicProvers.VAR_EQ_TAC >>
  match_mp_tac (GEN_ALL INJ_BIJ_SUBSET) >>
  map_every qexists_tac[`s`,`iseg wo x`] >>
  fs[BIJ_DEF] >>
  simp[SUBSET_DEF,iseg_def,Abbr`a`] >>
  fs[iseg_def] >>
  metis_tac[WIN_TRANS])

val minWO_def = new_specification("minWO_def",["minWO"],
  minWO_exists |> SIMP_RULE std_ss [SKOLEM_THM] )

val wsup_def = Define`
  wsup wo Y = wleast wo (COMPL { b | ∀y. y ∈ Y ⇒ (y,b) WLE wo })`

val regular_cardinal_def = Define`
  regular_cardinal X ⇔
    ∀y. y ⊆ X ∧ y ≺ X ⇒ IS_SOME (wsup (minWO X) y)`

val larger_exists = store_thm("larger_exists",
  ``∀X x. INFINITE X ∧ x ∈ X ⇒ ∃y. (x,y) WIN (minWO X)``,
  rpt strip_tac >>
  imp_res_tac(CONJUNCT2(Q.SPEC`X`minWO_def)) >>
  spose_not_then strip_assume_tac >>
  `iseg (minWO X) x = X DELETE x` by (
    simp[EXTENSION,iseg_def,EQ_IMP_THM] >>
    gen_tac >> conj_tac >- (
      metis_tac[WIN_elsOf,minWO_def,WIN_REFL] ) >>
    strip_tac >>
    qmatch_assum_rename_tac`y ≠ x` >>
    qspecl_then[`minWO X`,`x`,`y`]mp_tac (GEN_ALL WIN_trichotomy) >>
    simp[minWO_def] ) >>
  `X = x INSERT (X DELETE x)` by simp[] >>
  fs[cardlt_lenoteq] >>
  metis_tac[cardeq_INSERT,FINITE_DELETE,cardeq_TRANS,cardeq_SYM])

val wsup_elsOf = store_thm("wsup_elsOf",
  ``wsup wo x = SOME y ⇒ y ∈ elsOf wo``,
  rw[wsup_def] >>
  imp_res_tac wleast_IN_wo)

val wsup_greater = store_thm("wsup_greater",
  ``wsup wo x = SOME y ⇒ ∀z. z ∈ x ⇒ (z,y) WLE wo``,
  rw[wsup_def] >>
  imp_res_tac wleast_IN_wo >> fs[] >>
  metis_tac[] )

val regular_cardinal_smaller = store_thm("regular_cardinal_smaller",
  ``regular_cardinal X ∧ INFINITE X ⇒
    ∀x f.
      x ⊆ X ∧ x ≺ X ∧ (∀a. a ∈ x ⇒ f a ⊆ X ∧ f a ≺ X) ⇒
        BIGUNION (IMAGE f x) ≺ X``,
  rw[regular_cardinal_def] >>
  `∃b. b ∈ X ∧ BIGUNION (IMAGE f x) ⊆ iseg (minWO X) b` suffices_by (
    strip_tac >>
    imp_res_tac(CONJUNCT2 (Q.SPEC`X`minWO_def)) >>
    metis_tac[SUBSET_CARDLEQ,cardleq_lt_trans] ) >>
  `∀a. a ∈ x ⇒ IS_SOME (wsup (minWO X) (f a))` by metis_tac[] >>
  qabbrev_tac`g = λa. THE(wsup(minWO X)(f a))` >>
  `IMAGE g x ⊆ X` by (
    simp[Abbr`g`,SUBSET_DEF,PULL_EXISTS] >>
    metis_tac[wsup_elsOf,minWO_def,
              miscTheory.IS_SOME_EXISTS,
              optionTheory.THE_DEF] ) >>
  `IMAGE g x ≺ X` by (
    metis_tac[cardleq_lt_trans,IMAGE_cardleq] ) >>
  last_x_assum(qspec_then`IMAGE g x`mp_tac) >>
  simp[miscTheory.IS_SOME_EXISTS] >>
  disch_then(qx_choose_then`b`strip_assume_tac) >>
  qspecl_then[`X`,`b`]mp_tac larger_exists >>
  `b ∈ X` by metis_tac[wsup_elsOf,minWO_def] >>
  simp[] >> strip_tac >>
  qexists_tac`y` >>
  conj_tac >- metis_tac[WIN_elsOf,minWO_def] >>
  `∀z. z ∈ BIGUNION (IMAGE f x) ⇒ (z,y) WIN minWO X` by (
    simp[PULL_EXISTS] >> gen_tac >>
    qx_gen_tac`a` >> strip_tac >>
    `(z,g a) WLE minWO X` by (
      simp[Abbr`g`] >>
      metis_tac[miscTheory.IS_SOME_EXISTS,
                optionTheory.THE_DEF,
                wsup_greater] ) >>
    `(g a,b) WLE minWO X` by (
      imp_res_tac wsup_greater >>
      fs[PULL_EXISTS] ) >>
    `(z,b) WLE minWO X` by metis_tac[WLE_TRANS] >>
    metis_tac[WLE_WIN_EQ,WIN_TRANS] ) >>
  REWRITE_TAC[SUBSET_DEF,iseg_def] >>
  rpt strip_tac >> res_tac >> simp[])

val my_regular_cardinal_def = Define`
  my_regular_cardinal X ⇔
    ∀x f.
      x ⊆ X ∧ x ≺ X ∧ (∀a. a ∈ x ⇒ f a ⊆ X ∧ f a ≺ X) ⇒
        BIGUNION (IMAGE f x) ≺ X`

val my_regular_cardinal_regular = store_thm("my_regular_cardinal_regular",
  ``∀X. my_regular_cardinal X ⇒ regular_cardinal X``,
  rw[regular_cardinal_def,my_regular_cardinal_def] >>
  spose_not_then strip_assume_tac >> fs[] >>
  first_x_assum(qspec_then`y`mp_tac) >> simp[] >>
  qexists_tac`λz. { x | (x,z) WIN minWO X }` >>
  simp[GSYM iseg_def] >>
  conj_tac >- (
    gen_tac >> strip_tac >>
    `a ∈ X` by fs[SUBSET_DEF] >>
    simp[minWO_def] >>
    simp[iseg_def,SUBSET_DEF] >>
    metis_tac[WIN_elsOf,minWO_def] ) >>
  match_mp_tac SUBSET_CARDLEQ >>
  simp[SUBSET_DEF] >>
  qx_gen_tac`b` >> strip_tac >>
  simp[PULL_EXISTS] >>
  spose_not_then strip_assume_tac >>
  `∀z. z ∈ y ⇒ (z,b) WLE minWO X` by (
    rw[] >> fs[iseg_def] >>
    simp[WLE_WIN_EQ,minWO_def] >>
    fs[SUBSET_DEF] >>
    metis_tac[WIN_trichotomy,minWO_def] ) >>
  fs[wsup_def] >>
  imp_res_tac wleast_EQ_NONE >> fs[minWO_def] >>
  fs[SUBSET_DEF] >>
  pop_assum(qspec_then`b`mp_tac) >> simp[] >>
  metis_tac[] )

val not_imp = PROVE[]``a ∨ b ⇔ ¬a ⇒ b``

val my_regular_cardinal_alt = prove(
  ``my_regular_cardinal X ⇔
    ¬∃(x:α set)(f:α -> α set).
      x ⊆ X ∧ x ≺ X ∧
      (∀a. a ∈ x ⇒ f a ≺ X) ∧
      (∀a. a ∈ X ⇒ ∃y. y ∈ x ∧ a ∈ f y)``,
  EQ_TAC >- (
    simp[my_regular_cardinal_def,not_imp,AND_IMP_INTRO] >>
    rpt strip_tac >>
    `∃g. ∀a. a ∈ x ⇒ g a ⊆ X ∧ g a ≺ X ∧ (g a = f a INTER X)` by (
      simp[GSYM SKOLEM_THM,RIGHT_EXISTS_IMP_THM] >> rw[] >>
      `f a ∩ X ≼ f a` suffices_by metis_tac[cardleq_lt_trans] >>
      simp[cardleq_def] >>
      qexists_tac`I` >> simp[INJ_DEF] ) >>
    first_x_assum(qspecl_then[`x`,`g`]mp_tac) >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`b ≺ X` >>
    `¬(X ⊆ b)` by metis_tac[SUBSET_CARDLEQ] >>
    pop_assum mp_tac >> simp[SUBSET_DEF] >>
    disch_then(qx_choose_then`a`strip_assume_tac) >>
    qexists_tac`a` >> simp[] >>
    rpt strip_tac >>
    `a ∈ g y` by (
      metis_tac[EXTENSION,IN_INTER] ) >>
    qpat_assum`a ∉ b`mp_tac >>
    simp[Abbr`b`] >>
    metis_tac[] ) >>
  simp[my_regular_cardinal_def,not_imp,AND_IMP_INTRO] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  simp[cardlt_lenoteq] >>
  conj_tac >- (
    match_mp_tac SUBSET_CARDLEQ >>
    fs[SUBSET_DEF,PULL_EXISTS] >>
    metis_tac[] ) >>
  simp[cardeq_def] >>
  qx_gen_tac`g` >> strip_tac >>
  qmatch_assum_abbrev_tac`BIJ g b X` >>
  first_x_assum(qspecl_then[`x`,`IMAGE g o f`]mp_tac) >>
  simp[not_imp,PULL_EXISTS] >>
  conj_tac >- (
    rw[] >> res_tac >> fs[cardleq_def] >>
    qx_gen_tac`h` >> strip_tac >>
    first_x_assum(qspec_then`LINV g b o h`mp_tac) >>
    fs[INJ_DEF] >>
    `∀x. x ∈ X ⇒ LINV g b (h x) = x` by (
      metis_tac[BIJ_LINV_INV] ) >>
    simp[] >> metis_tac[] ) >>
  rw[] >>
  `LINV g b a ∈ b` by (
    metis_tac[BIJ_LINV_BIJ,BIJ_DEF,INJ_DEF] ) >>
  pop_assum mp_tac >> simp[Abbr`b`,PULL_EXISTS] >>
  rw[] >>
  metis_tac[BIJ_LINV_INV])

(*
 false: see 3 = {0,1,2}
val my_regular_cardinal_supremums2 = prove(
  ``(∀y. y ⊆ X ∧ y ≺ X ⇒ IS_SOME (wsup (minWO X) y)) ⇒
    my_regular_cardinal X``,
  rw[my_regular_cardinal_def] >>
  `∃b. b ∈ X ∧ ∀z. z ∈ BIGUNION (IMAGE f x) ⇒ (z,b) WIN minWO X` suffices_by (
    strip_tac >>
    imp_res_tac(CONJUNCT2 (Q.SPEC`X`minWO_def)) >>
    qmatch_abbrev_tac`a ≺ X` >>
    `a ⊆ iseg (minWO X) b` suffices_by metis_tac[SUBSET_CARDLEQ,cardleq_lt_trans] >>
    simp[iseg_def,SUBSET_DEF] (* >>
    qx_gen_tac`z` >> strip_tac >>
    first_x_assum(qspec_then`z`mp_tac) >>
    rw[WLE_WIN_EQ,minWO_def] >>
    fs[Abbr`a`] >> rw[] >>
    qmatch_assum_rename_tac`z ∈ x` >>
    first_x_assum(qspec_then`z`mp_tac) >>
    rw[SUBSET_DEF]
    rw[] >> res_tac >>
    fs[WLE_WIN_EQ] >> rw[] >>
    fs[Abbr`a`] >> rw[] >>
    res_tac *)
    ) >>
*)

val wsuc_def = Define`
  wsuc wo x = wleast wo (COMPL {a | (x,a) WIN wo})`

val IS_SOME_wsuc = store_thm("IS_SOME_wsuc",
  ``INFINITE X ∧ x ∈ X ⇒ IS_SOME (wsuc (minWO X) x)``,
  rw[] >> imp_res_tac larger_exists >>
  simp[wsuc_def] >> spose_not_then strip_assume_tac >> fs[] >>
  imp_res_tac wleast_EQ_NONE >> fs[minWO_def] >>
  fs[SUBSET_DEF] >> metis_tac[WIN_elsOf,minWO_def])

val wsuc_elsOf = store_thm("wsuc_elsOf",
  ``wsuc wo x = SOME y ⇒ y ∈ elsOf wo``,
  rw[wsuc_def] >>
  imp_res_tac wleast_IN_wo)

val wsuc_WIN = store_thm("wsuc_WIN",
  ``wsuc wo x = SOME y ⇒ (x,y) WIN wo``,
  rw[wsuc_def] >>
  imp_res_tac wleast_IN_wo >>
  fs[])

val strong_regular_limitation = store_thm("strong_regular_limitation",
  ``strong_limit_cardinal X ∧ regular_cardinal X ⇒
    limitation_of_size X``,
  strip_tac >>
  Cases_on`X = ∅` >- ( rw[limitation_of_size_def] ) >>
  imp_res_tac strong_infinite >>
  fs[strong_limit_cardinal_def,regular_cardinal_def,limitation_of_size_def] >>
  simp[GSYM cardeq_def] >>
  match_mp_tac cardleq_ANTISYM >>
  conj_tac >- (
    simp[cardleq_def] >>
    qexists_tac`λa. {a}` >>
    simp[INJ_DEF] >> rw[] >>
    spose_not_then strip_assume_tac >>
    Cases_on`∃b. b ∈ X ∧ a ≠ b` >> fs[] >- metis_tac[] >>
    `X = {a}` by (
      simp[EXTENSION] >>
      metis_tac[] ) >>
    fs[] >>
    last_x_assum(qspec_then`{}`mp_tac) >>
    simp[CARDLEQ_CARD,POW_DEF] ) >>
  qmatch_abbrev_tac`a ≼ X` >>
  `a ≼ X × X` suffices_by metis_tac[cardleq_TRANS,SET_SQUARED_CARDEQ_SET,cardleq_lteq] >>
  qunabbrev_tac`a` >>
  `∃f. ∀x. x ∈ X ⇒ INJ (f x) (POW (iseg (minWO X) x)) X` by (
    simp[GSYM SKOLEM_THM] >> rw[RIGHT_EXISTS_IMP_THM] >>
    simp[GSYM cardleq_def] >>
    `POW (iseg (minWO X) x) ≺ X` suffices_by metis_tac[cardlt_lenoteq] >>
    first_x_assum match_mp_tac >>
    conj_tac >- (
      simp[iseg_def,SUBSET_DEF] >>
      metis_tac[WIN_elsOf,minWO_def] ) >>
    metis_tac[minWO_def] ) >>
  simp[Once cardleq_def] >>
  qexists_tac`λx. (THE (wsup (minWO X) x),
    f (THE (wsuc (minWO X) (THE (wsup (minWO X) x)))) x)` >>
  simp[INJ_DEF] >>
  conj_asm1_tac >- (
    gen_tac >> strip_tac >>
    conj_tac >- (
      metis_tac[miscTheory.IS_SOME_EXISTS,optionTheory.THE_DEF,
                wsup_elsOf,minWO_def] ) >>
    fsrw_tac[boolSimps.DNF_ss][INJ_DEF] >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    conj_tac >- (
      metis_tac[IS_SOME_wsuc,miscTheory.IS_SOME_EXISTS,optionTheory.THE_DEF,
                wsuc_elsOf,wsup_elsOf,minWO_def] ) >>
    simp[IN_POW,iseg_def,SUBSET_DEF] >> rw[] >>
    fs[miscTheory.IS_SOME_EXISTS] >> res_tac >> simp[] >>
    imp_res_tac wsup_greater >>
    imp_res_tac wsup_elsOf >>
    fs[minWO_def] >> rw[] >>
    imp_res_tac IS_SOME_wsuc >>
    fs[miscTheory.IS_SOME_EXISTS] >>
    imp_res_tac wsuc_WIN >>
    metis_tac[WLE_WIN_EQ,WIN_TRANS] ) >>
  fs[INJ_DEF] >>
  rw[] >> rfs[] >>
  fsrw_tac[boolSimps.DNF_ss][] >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  qmatch_assum_abbrev_tac`f a x1 = f a x2` >>
  qexists_tac`a` >> simp[] >>
  simp[Abbr`a`,IN_POW,SUBSET_DEF,iseg_def] >>
  conj_tac >- (
    metis_tac[miscTheory.IS_SOME_EXISTS,optionTheory.THE_DEF,IS_SOME_wsuc,
              wsuc_elsOf,wsup_elsOf,minWO_def] ) >>
  rw[] >>
  fs[miscTheory.IS_SOME_EXISTS] >> res_tac >> simp[] >>
  imp_res_tac wsup_greater >>
  imp_res_tac wsup_elsOf >>
  fs[minWO_def] >> rw[] >>
  imp_res_tac IS_SOME_wsuc >>
  fs[miscTheory.IS_SOME_EXISTS] >>
  imp_res_tac wsuc_WIN >>
  metis_tac[WLE_WIN_EQ,WIN_TRANS] )

val implies_set_theory = store_thm("implies_set_theory",
  ``strong_limit_cardinal (UNIV:'U set) ∧
    regular_cardinal (UNIV:'U set)
    ⇒
    ∃(mem:'U reln). is_set_theory mem ∧
      (∀s. s ≺ (UNIV:'U set) ⇒ ∃x. s = { a | a <: x }) ∧
      (¬countable (UNIV:'U set) ⇒ ∃inf. is_infinite mem inf)``,
  strip_tac >>
  imp_res_tac strong_regular_limitation >>
  fs[limitation_of_size_def] >>
  qexists_tac`combin$C f` >>
  reverse conj_tac >- (
    conj_asm1_tac >- (
      rw[] >>
      qmatch_assum_abbrev_tac`BIJ f a b` >>
      `s ∈ b` by ( simp[Abbr`b`] ) >>
      qexists_tac`LINV f a s` >>
      `f (LINV f a s) = s` by metis_tac[BIJ_LINV_INV] >>
      pop_assum SUBST1_TAC >>
      simp[EXTENSION,IN_DEF] ) >>
    strip_tac >>
    simp[is_infinite_def] >>
    `(UNIV:num set) ≺ (UNIV:'U set)` by (
      spose_not_then strip_assume_tac >>
      fs[cardleq_def,countable_def] ) >>
    pop_assum mp_tac >> rw[cardlt_lenoteq,cardleq_def] >>
    qmatch_assum_rename_tac`INJ g _ (UNIV:'U set)` >>
    qabbrev_tac`s = IMAGE g UNIV` >>
    first_x_assum(qspec_then`s`mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`s`] >>
      `(UNIV:num set) ≺ (UNIV:'U set)` by (
        simp[cardlt_lenoteq,cardleq_def] >>
        metis_tac[] ) >>
      metis_tac[IMAGE_cardleq,cardleq_lt_trans] ) >>
    simp[] >> strip_tac >>
    qexists_tac`x` >>
    pop_assum(SUBST1_TAC o SYM) >>
    simp[Abbr`s`] >>
    match_mp_tac (MP_CANON IMAGE_11_INFINITE) >>
    fs[INJ_DEF] ) >>
  simp[is_set_theory_def] >>
  conj_tac >- (
    simp[extensional_def] >>
    rw[Once EQ_IMP_THM] >>
    fs[BIJ_DEF,INJ_DEF,FUN_EQ_THM] ) >>
  conj_tac >- (
    simp[is_separation_def] >>
    fs[BIJ_IFF_INV] >>
    qexists_tac`λy P. g (λx. f y x ∧ P x)` >>
    rw[] >>
    qmatch_abbrev_tac`f (g z) a = R` >>
    `f (g z) = z` suffices_by rw[Abbr`R`] >>
    first_x_assum match_mp_tac >>
    rw[Abbr`z`] >>
    match_mp_tac (INST_TYPE[beta|->``:'U``]cardleq_lt_trans) >>
    qexists_tac`f x` >> simp[] >>
    match_mp_tac SUBSET_CARDLEQ >>
    simp[SUBSET_DEF,IN_DEF] ) >>
  conj_tac >- (
    simp[is_power_def] >>
    fs[strong_limit_cardinal_def] >>
    fs[BIJ_IFF_INV] >>
    qexists_tac`λy. g (λx. f x ⊆ f y)` >>
    simp[] >> qx_genl_tac[`a`,`b`] >>
    qmatch_abbrev_tac`f (g z) b ⇔ R` >>
    `f (g z) = z` by (
      first_x_assum match_mp_tac >>
      simp[Abbr`z`] >>
      match_mp_tac (INST_TYPE[beta|->``:'U set``]cardleq_lt_trans) >>
      qexists_tac`POW (f a)` >>
      conj_tac >- (
        simp[cardleq_def,INJ_DEF,IN_POW] >>
        qexists_tac`f` >> simp[] >>
        metis_tac[] ) >>
      metis_tac[] ) >>
    rw[Abbr`z`,Abbr`R`,SUBSET_DEF,IN_DEF] ) >>
  conj_tac >- (
    simp[is_union_def] >>
    fs[BIJ_IFF_INV] >>
    qexists_tac`λx. g (BIGUNION (IMAGE f (f x)))` >>
    simp[] >>
    rpt gen_tac >>
    qmatch_abbrev_tac`f (g z) c ⇔ R` >>
    `f (g z) = z` suffices_by (
      rw[Abbr`z`,PULL_EXISTS,IN_DEF] ) >>
    first_x_assum match_mp_tac >>
    rw[Abbr`z`] >>
    imp_res_tac strong_infinite >> fs[] >>
    imp_res_tac regular_cardinal_smaller >>
    fs[]) >>
  simp[is_upair_def] >>
  fs[BIJ_IFF_INV] >>
  qexists_tac`λx y. g (λa. (a = x) ∨ (a = y))` >>
  simp[] >>
  qx_genl_tac[`a`,`b`,`c`] >>
  qmatch_abbrev_tac`f (g z) c ⇔ R` >>
  `f (g z) = z` by (
    first_assum match_mp_tac >>
    simp[Abbr`z`] >>
    qmatch_abbrev_tac`z ≺ u` >>
    `z = {a;b}` by ( simp[Abbr`z`,EXTENSION] ) >>
    qpat_assum`Abbrev(z = X)`kall_tac >> rw[Abbr`u`] >>
    fs[strong_limit_cardinal_def] >>
    `({}:'U set) ≺ (UNIV:'U set)` by ( simp[cardleq_def] ) >>
    last_assum(qspec_then`{}`mp_tac) >>
    discharge_hyps >- rw[] >> strip_tac >>
    `IMAGE g (POW {}) ≺ (UNIV:'U set)` by (
      match_mp_tac (INST_TYPE[beta|->``:'U set``]cardleq_lt_trans) >>
      qexists_tac`POW {}` >> simp[] ) >>
    `POW (IMAGE g (POW {})) ≺ (UNIV:'U set)` by (
      first_x_assum match_mp_tac >> rw[] ) >>
    `IMAGE g (POW (IMAGE g (POW {}))) ≺ (UNIV:'U set)` by (
      match_mp_tac (INST_TYPE[beta|->``:'U set``]cardleq_lt_trans) >>
      qexists_tac`POW (IMAGE g (POW {}))` >> simp[]) >>
    `POW (IMAGE g (POW (IMAGE g (POW {})))) ≺ (UNIV:'U set)` by (
      first_x_assum match_mp_tac >> rw[] ) >>
    `IMAGE g (POW (IMAGE g (POW (IMAGE g (POW {}))))) ≺ (UNIV:'U set)` by (
      match_mp_tac (INST_TYPE[beta|->``:'U set``]cardleq_lt_trans) >>
      qexists_tac`POW (IMAGE g (POW (IMAGE g (POW {}))))` >> simp[]) >>
    match_mp_tac (INST_TYPE[gamma|->``:'U``]cardlt_TRANS) >>
    qexists_tac`IMAGE g (POW (IMAGE g (POW (IMAGE g (POW {})))))` >>
    simp[] >> simp[POW_DEF] >>
    `{s | s ⊆ {g ∅}} = {{};{g {}}}` by (
      simp[SUBSET_DEF,EXTENSION] >>
      metis_tac[] ) >>
    simp[] >>
    `{s | s ⊆ {g {}; g{g {}}}} = {{};{g {}};{g{g{}}};{g{};g{g{}}}}` by (
       simp[SUBSET_DEF] >>
       simp[EXTENSION,EQ_IMP_THM] >>
       metis_tac[] ) >>
    simp[] >>
    `f (g {}) = {}` by metis_tac[] >>
    `f (g {g ∅}) = {g ∅}` by (
      first_x_assum match_mp_tac >> fs[POW_DEF] ) >>
    `f (g {g {g ∅}}) = {g {g ∅}}` by (
      first_x_assum match_mp_tac >> fs[POW_DEF] >>
      `{g {g ∅}} ⊆ {g ∅; g {g ∅}}` by simp[SUBSET_DEF] >>
      metis_tac[SUBSET_CARDLEQ,cardleq_lt_trans]) >>
    simp[CARDLEQ_CARD] >>
    rw[] >> simp[] >>
    metis_tac[NOT_INSERT_EMPTY,EXTENSION,IN_INSERT] ) >>
  rw[Abbr`z`,Abbr`R`])
val strongly_inaccessible_def = Define`
  strongly_inaccessible X ⇔
    regular_cardinal X ∧
    strong_limit_cardinal X ∧
    ¬(countable X)`

val strongly_inaccessible_imp = store_thm("strongly_inaccessible_imp",
  ``strongly_inaccessible (UNIV:'U set) ⇒
    ∃(mem:'U reln). is_set_theory mem ∧
    (∀s. s ≺ (UNIV:'U set) ⇒ ∃x. s = { a | a <: x }) ∧
    (∃inf. is_infinite mem inf)``,
  rw[strongly_inaccessible_def] >> metis_tac[implies_set_theory])

val regular_imp_my_regular = prove(
  ``regular_cardinal X ∧ INFINITE X ⇒ my_regular_cardinal X``,
  metis_tac[regular_cardinal_smaller,my_regular_cardinal_def])

val my_regular_empty = prove(
  ``my_regular_cardinal ∅``,
  rw[my_regular_cardinal_def])

val strongly_inaccessible_alt = store_thm("strongly_inaccessible_alt",
  ``strongly_inaccessible X ⇔
      my_regular_cardinal X ∧
      strong_limit_cardinal X ∧
      ¬(countable X)``,
  rw[strongly_inaccessible_def,EQ_IMP_THM] >>
  metis_tac[regular_imp_my_regular,strong_infinite,
            my_regular_empty,my_regular_cardinal_regular])

val LCA_def = Define`
  (LCA P 0 ⇔ T) ∧
  (LCA P (SUC n) ⇔ strongly_inaccessible P ∧
     ∃Q. Q ⊆ P ∧ Q ≺ P ∧ LCA Q n)`

val _ = export_theory()
