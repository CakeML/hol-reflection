open HolKernel boolLib bossLib lcsymtacs
open miscLib basicReflectionLib pred_setTheory
open setSpecTheory holSyntaxTheory holSemanticsTheory holSemanticsExtraTheory

val _ = temp_tight_equality()
val _ = new_theory"reflection"

val finv_def = Define`
  finv f x = @y. f y = x`

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
  imp_res_tac is_in_bij_thm >>
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
  imp_res_tac is_in_bij_thm >>
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

val finv_in_bool_True = prove(
  ``is_set_theory ^mem ⇒ finv in_bool True``,
  rw[] >>
  imp_res_tac is_in_in_bool >>
  `True = (in_bool T)` by simp[in_bool_def,boolean_def] >>
  pop_assum SUBST1_TAC >>
  metis_tac[is_in_finv_left])

val provable_imp_eq_true = store_thm("provable_imp_eq_true",
  ``∀thy i v.
    is_set_theory ^mem ⇒
    i models thy ⇒
    is_valuation (tysof (sigof thy)) (tyaof i) v
    ⇒
    ∀p. (thy,[]) |- p ⇒ termsem (tmsof (sigof thy)) i v p = True``,
  rw[] >>
  imp_res_tac holSoundnessTheory.proves_sound >>
  fs[entails_def] >> res_tac >>
  fs[satisfies_def])

val mp_lemma = store_thm("mp_lemma",
  ``(a ==> b) /\ (c ==> a) ==> (c ==> b)``,
  metis_tac[])

val good_context_def = Define`
  good_context ^mem ^tysig ^tmsig ^tyass ^tmass ^tyval ^tmval ⇔
    is_set_theory ^mem ∧
    is_std_sig ^signatur ∧
    is_interpretation ^signatur ^interpretation ∧
    is_std_interpretation ^interpretation ∧
    is_valuation ^tysig ^tyass ^valuation`
val good_context = good_context_def |> concl |> strip_forall |> snd |> lhs

val finv_in_bool_True = prove(
``^good_context ⇒
  (finv in_bool x ⇒ y) ⇒ ((x = True) ⇒ y)``,
  metis_tac[finv_in_bool_True,good_context_def]) |> UNDISCH

val _ = save_thm("finv_in_bool_True",finv_in_bool_True)

val Var_thm = prove(
  ``^tmval (x,ty) = inty v ⇒
    ∀mem. inty v = termsem0 mem ^tmsig ^interpretation ^valuation (Var x ty)``,
  rw[termsem_def])

val Const_thm = prove(
  ``instance ^tmsig ^interpretation name ty ^tyval = inty c ⇒
    ∀mem. inty c = termsem0 mem ^tmsig ^interpretation ^valuation (Const name ty)``,
  rw[termsem_def])

val Comb_thm = prove(
  ``^good_context ⇒
    in_fun ina inb f = termsem ^tmsig ^interpretation ^valuation ftm ∧
    ina x = termsem ^tmsig ^interpretation ^valuation xtm ⇒
    is_in ina ⇒ is_in inb
    ⇒
    inb (f x) =
      termsem ^tmsig ^interpretation ^valuation (Comb ftm xtm)``,
  rw[good_context_def,termsem_def] >>
  rpt(first_x_assum(SUBST1_TAC o SYM)) >>
  rw[in_fun_def] >>
  match_mp_tac EQ_SYM >>
  match_mp_tac apply_abstract_matchable >>
  simp[] >>
  rw[is_in_range_thm] >>
  AP_TERM_TAC >>
  AP_TERM_TAC >>
  match_mp_tac is_in_finv_left >>
  simp[]) |> UNDISCH

val Abs_thm = prove(
  ``^good_context ⇒
    ∀ina inb f x ty b.
    range ina = typesem tyass tyval ty ⇒
    range inb = typesem tyass tyval (typeof b) ⇒
    is_in ina ⇒ is_in inb ⇒
    (∀m. m <: range ina ⇒
      inb (f (finv ina m)) =
        termsem tmsig (tyass,tmass) (tyval,((x,ty) =+ m) tmval) b) ⇒
    term_ok (tysig,tmsig) b
    ⇒
    in_fun ina inb f =
      termsem tmsig (tyass,tmass) (tyval,tmval) (Abs x ty b)``,
  rw[termsem_def,in_fun_def,good_context_def] >>
  match_mp_tac (UNDISCH abstract_eq) >> simp[] >>
  rw[] >>
  match_mp_tac (UNDISCH termsem_typesem) >>
  simp[] >>
  qexists_tac`(tysig,tmsig)` >> simp[] >>
  fs[is_std_interpretation_def] >>
  fs[is_valuation_def,is_term_valuation_def] >>
  simp[combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> metis_tac[]) |> UNDISCH

val save_thms = map2 (curry save_thm)
val _ = save_thms ["Var_thm","Const_thm","Comb_thm","Abs_thm"]
                  [ Var_thm , Const_thm , Comb_thm , Abs_thm ]

val good_context_is_in_in_bool = prove(mk_imp(good_context,rand(concl(is_in_in_bool))),
  rw[good_context_def,is_in_in_bool]) |> UNDISCH

val good_context_is_in_in_fun = prove(mk_imp(good_context,rand(concl(is_in_in_fun))),
  rw[good_context_def,is_in_in_fun]) |> UNDISCH

val good_context_lookup_bool = prove(
  ``^good_context ⇒ FLOOKUP ^tysig "bool" = SOME 0``,
  rw[good_context_def,is_std_sig_def]) |> UNDISCH

val good_context_lookup_fun = prove(
  ``^good_context ⇒ FLOOKUP ^tysig "fun" = SOME 2``,
  rw[good_context_def,is_std_sig_def]) |> UNDISCH

val good_context_extend_tmval = prove(
  ``^good_context ∧
     m <: typesem ^tyass ^tyval ty ⇒
     good_context ^mem ^tysig ^tmsig ^tyass ^tmass ^tyval (((x,ty) =+ m) ^tmval)``,
  rw[good_context_def,is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> rw[])

val good_context_instance_equality = prove(
  ``∀ty ina.
    ^good_context ∧
    type_ok ^tysig ty ∧
    typesem ^tyass ^tyval ty = range ina ∧
    is_in ina ⇒
    instance ^tmsig ^interpretation "=" (Fun ty (Fun ty Bool)) ^tyval =
      in_fun ina (in_fun ina in_bool) $=``,
  rw[good_context_def] >>
  fs[is_std_sig_def] >>
  imp_res_tac instance_def >>
  first_x_assum(qspec_then`[ty,Tyvar "A"]`mp_tac) >>
  simp[holSyntaxLibTheory.REV_ASSOCD] >>
  disch_then(mp_tac o SPEC interpretation) >>
  simp[] >> disch_then kall_tac >>
  EVAL_STRING_SORT >> simp[holSyntaxLibTheory.REV_ASSOCD] >>
  fs[is_std_interpretation_def,interprets_def] >>
  first_x_assum(qspec_then`("A"=+ typesem ^tyass ^tyval ty)(K boolset)`mp_tac) >>
  discharge_hyps >- (
    simp[is_type_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
    reverse(rw[mem_boolset]) >- metis_tac[] >>
    qpat_assum`X = Y` (SUBST1_TAC o SYM) >>
    match_mp_tac (UNDISCH typesem_inhabited) >>
    fs[is_valuation_def,is_interpretation_def] >>
    metis_tac[] ) >>
  simp[combinTheory.APPLY_UPDATE_THM] >>
  disch_then kall_tac >>
  simp[in_fun_def] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[] >> gen_tac >> strip_tac >>
  conj_tac >- (
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[boolean_in_boolset] ) >>
  Q.ISPECL_THEN[`mem`,`in_bool`,`ina`]mp_tac (GEN_ALL range_in_fun) >>
  discharge_hyps >- ( simp[is_in_in_bool] ) >>
  strip_tac >> simp[range_in_bool] >>
  Q.ISPECL_THEN[`mem`,`in_bool`,`ina`]mp_tac (GEN_ALL range_in_fun) >>
  discharge_hyps >- ( simp[is_in_in_bool] ) >>
  strip_tac >> simp[range_in_bool] >>
  conj_tac >- (
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[in_bool_def,boolean_in_boolset] ) >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[in_bool_def,boolean_in_boolset] >>
  simp[boolean_def] >> rw[true_neq_false] >>
  spose_not_then strip_assume_tac >>
  metis_tac[is_in_finv_right])

val _ = save_thms
  ["good_context_is_in_in_bool","good_context_is_in_in_fun",
   "good_context_lookup_bool","good_context_lookup_fun",
   "good_context_extend_tmval","good_context_instance_equality"]
  [ good_context_is_in_in_bool , good_context_is_in_in_fun ,
    good_context_lookup_bool , good_context_lookup_fun ,
    good_context_extend_tmval , good_context_instance_equality ]

val _ = export_theory()
