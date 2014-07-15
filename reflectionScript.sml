open HolKernel boolLib bossLib lcsymtacs
open miscLib pred_setTheory setSpecTheory

val _ = temp_tight_equality()
val _ = new_theory"reflection"

val finv_def = Define`
  finv f x = @y. f y = x`

val mem = ``mem:'U->'U->bool``

val is_in_def = xDefine"is_in"`
  is_in0 ^mem f = ∃x. BIJ f UNIV {a | mem a x}`
val _ = Parse.overload_on("is_in",``is_in0 ^mem``)

val is_in_finv_left = store_thm("is_in_finv_left",
  ``∀ina.
    is_in ina ⇒ ∀x. finv ina (ina x) = x``,
  rw[finv_def] >>
  SELECT_ELIM_TAC >>
  conj_tac >-metis_tac[] >>
  fs[is_in_def,BIJ_DEF,INJ_DEF])

val ext_def = xDefine"ext"`
  ext0 ^mem s = { a | mem a s }`
val _ = Parse.overload_on("ext",``ext0 ^mem``)

val range_def = xDefine"range"`
  range0 ^mem (f : α -> 'U) = @x. BIJ f UNIV {a | mem a x}`
val _ = Parse.overload_on("range",``range0 ^mem``)

val is_in_bij_thm = store_thm("is_in_bij_thm",
  ``∀f. is_in f ⇒ BIJ f UNIV (ext (range f))``,
  rw[is_in_def,range_def] >>
  SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >>
  rw[ext_def])

val is_in_range_thm = store_thm("is_in_range_thm",
  ``∀f x. is_in f ⇒ f x <: range f``,
  rw[] >>
  imp_res_tac is_in_bij_thm >>
  fs[BIJ_DEF,ext_def,INJ_DEF])

val is_in_finv_right = store_thm("is_in_finv_right",
  ``∀ina.
    is_in ina ⇒ ∀x. x <: range ina ⇒
      (ina (finv ina x)) = x``,
  rw[finv_def] >>
  SELECT_ELIM_TAC >>
  conj_tac >-(
    imp_res_tac is_in_bij_thm >>
    fs[ext_def,BIJ_DEF,SURJ_DEF] ) >>
  rw[])

val in_bool_def = xDefine"in_bool"`
  in_bool0 ^mem = Boolean`
val _ = Parse.overload_on("in_bool",``in_bool0 ^mem``)

val is_in_in_bool = store_thm("is_in_in_bool",
  ``is_set_theory ^mem ⇒
    is_in in_bool``,
  rw[is_in_def,BIJ_IFF_INV] >>
  qexists_tac`boolset` >>
  rw[in_bool_def,boolean_in_boolset] >>
  qexists_tac`λx. x = True` >>
  rw[in_bool_def,boolean_eq_true] >>
  rfs[mem_boolset,boolean_eq_true,true_neq_false,boolean_def])

val in_fun_def = xDefine"in_fun"`
  in_fun0 ^mem ina inb f =
    Abstract (range ina) (range inb) (λx. inb (f (finv ina x)))`
val _ = Parse.overload_on("in_fun",``in_fun0 ^mem``)

val out_fun_def = xDefine"out_fun"`
  out_fun0 ^mem ina inb mf x = finv inb (mf ' (ina x))`
val _ = Parse.overload_on("out_fun",``out_fun0 ^mem``)

val is_in_in_fun = store_thm("is_in_in_fun",
  ``is_set_theory ^mem ⇒
    ∀ina inb. is_in ina ∧ is_in inb ⇒ is_in (in_fun ina inb)``,
  rw[] >>
  rw[is_in_def,BIJ_IFF_INV] >>
  qexists_tac`Funspace (range ina) (range inb)` >>
  conj_tac >- (
    rw[in_fun_def] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[range_def] >>
    SELECT_ELIM_TAC >>
    conj_tac >- metis_tac[is_in_def] >>
    rw[] >>
    SELECT_ELIM_TAC >>
    conj_tac >- metis_tac[is_in_def] >>
    rw[] >>
    fs[BIJ_IFF_INV] ) >>
  qexists_tac`out_fun ina inb` >>
  conj_tac >- (
    rw[out_fun_def,in_fun_def,FUN_EQ_THM] >>
    qmatch_abbrev_tac`finv invb (Abstract s t f ' a) = Z` >>
    rfs[] >>
    `Abstract s t f ' a = f a` by (
      match_mp_tac (UNDISCH apply_abstract) >>
      imp_res_tac is_in_bij_thm >>
      fs[ext_def,BIJ_IFF_INV] >>
      unabbrev_all_tac >> fs[] ) >>
    rw[Abbr`Z`,Abbr`f`,Abbr`a`,Abbr`invb`] >>
    imp_res_tac is_in_finv_left >>
    simp[] ) >>
  rw[in_fun_def,out_fun_def] >>
  first_x_assum(mp_tac o
    MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO](UNDISCH in_funspace_abstract))) >>
  simp[AND_IMP_INTRO] >>
  discharge_hyps >- (
    imp_res_tac is_in_bij_thm >>
    fs[ext_def,BIJ_IFF_INV] >>
    metis_tac[] ) >>
  rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  gen_tac >>
  qspecl_then[`f`,`ina (finv ina x)`,`range ina`,`range inb`]mp_tac
    (UNDISCH apply_abstract) >>
  discharge_hyps >- (
    imp_res_tac is_in_bij_thm >>
    fs[ext_def,BIJ_DEF,INJ_DEF] ) >>
  rw[] >>
  imp_res_tac is_in_finv_right >>
  rw[])

val range_in_bool = store_thm("range_in_bool",
  ``is_set_theory ^mem ⇒
    range in_bool = boolset``,
  strip_tac >>
  imp_res_tac is_in_in_bool >>
  imp_res_tac is_in_range_thm >>
  imp_res_tac is_extensional >>
  pop_assum mp_tac >>
  simp[extensional_def] >>
  disch_then kall_tac >>
  fs[ext_def,BIJ_IFF_INV,mem_boolset] >>
  fs[in_bool_def,boolean_def] >>
  metis_tac[] )

val range_in_fun = store_thm("range_in_fun",
  ``is_set_theory ^mem ∧ is_in ina ∧ is_in inb ⇒
    range (in_fun ina inb) = Funspace (range ina) (range inb)``,
  rw[] >>
  strip_assume_tac(SPEC_ALL (UNDISCH is_in_in_fun)) >> rfs[] >>
  imp_res_tac is_in_range_thm >>
  imp_res_tac is_extensional >>
  pop_assum mp_tac >>
  simp[extensional_def] >>
  disch_then kall_tac >>
  fs[ext_def,BIJ_IFF_INV] >>
  rw[EQ_IMP_THM] >- (
    fs[in_fun_def] >>
    res_tac >>
    pop_assum(SUBST1_TAC o SYM) >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    rw[] ) >>
  qspecl_then[`a`,`range ina`,`range inb`]mp_tac (UNDISCH in_funspace_abstract) >>
  simp[] >>
  discharge_hyps >- metis_tac[] >> strip_tac >>
  qpat_assum`a = X`(SUBST1_TAC) >>
  qsuff_tac`∃x. Abstract (range ina) (range inb) f = in_fun ina inb x` >- metis_tac[] >>
  rw[in_fun_def] >>
  qexists_tac`finv inb o f o ina` >>
  match_mp_tac (UNDISCH abstract_eq) >> simp[] >>
  metis_tac[is_in_finv_right,is_in_finv_left])

val _ = export_theory()
