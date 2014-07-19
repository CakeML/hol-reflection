open HolKernel boolLib bossLib Parse lcsymtacs listSimps
open miscLib basicReflectionLib pred_setTheory listTheory pairTheory combinTheory finite_mapTheory alistTheory
open miscTheory setSpecTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory
open holBoolSyntaxTheory holBoolTheory holConsistencyTheory holAxiomsSyntaxTheory holAxiomsTheory

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

val finv_in_bool_eq_true = store_thm("finv_in_bool_eq_true",
  ``is_set_theory ^mem ⇒
    ∀x.
    ((x = True) ⇒ finv in_bool x) ∧
    (x <: boolset ∧ finv in_bool x ⇒ (x = True))``,
  metis_tac[is_in_finv_right,in_bool_def,boolean_def,range_in_bool,is_in_in_bool,is_in_finv_left])

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
  metis_tac[finv_in_bool_eq_true,good_context_def]) |> UNDISCH

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

val good_context_tyass_bool = prove(
  ``^good_context ==> (tyass "bool" [] = range in_bool)``,
  rw[good_context_def,is_std_interpretation_def,is_std_type_assignment_def,range_in_bool]) |> UNDISCH

val good_context_tyass_fun = prove(
  ``^good_context ==> !tya tyb ina inb.
      is_in ina /\ is_in inb /\ tya = range ina /\ tyb = range inb ==>
        tyass "fun" [tya; tyb] = range (in_fun ina inb)``,
  rw[good_context_def,is_std_interpretation_def,is_std_type_assignment_def,range_in_fun]
  ) |> UNDISCH

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
   "good_context_tyass_bool", "good_context_tyass_fun",
   "good_context_lookup_bool","good_context_lookup_fun",
   "good_context_extend_tmval","good_context_instance_equality"]
  [ good_context_is_in_in_bool , good_context_is_in_in_fun ,
    good_context_tyass_bool, good_context_tyass_fun, 
    good_context_lookup_bool , good_context_lookup_fun ,
    good_context_extend_tmval , good_context_instance_equality ]

val base_tyval_exists = prove(
  ``∃τ. ∀mem. is_set_theory mem ⇒ is_type_valuation0 mem (τ mem)``,
  rw[GSYM SKOLEM_THM,is_type_valuation_def] >>
  qexists_tac`K (one mem)` >> rw[] >>
  qexists_tac`empty mem` >>
  metis_tac[mem_one])
val base_tyval_prim_def = new_specification("base_tyval_prim_def",["base_tyval0"],base_tyval_exists)
val _ = overload_on("base_tyval",``base_tyval0 ^mem``)
val base_tyval_def = save_thm("base_tyval_def",base_tyval_prim_def |> ISPEC mem |> UNDISCH)

val is_type_valuation_update_list = store_thm("is_type_valuation_update_list",
  ``∀ls t. is_type_valuation t ∧ EVERY (inhabited o SND) ls ⇒ is_type_valuation (t =++ ls)``,
  Induct >> simp[UPDATE_LIST_THM] >> rw[] >>
  first_x_assum match_mp_tac >> rw[] >>
  fs[is_type_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> metis_tac[])

val inhabited_range = store_thm("inhabited_range",
  ``∀inx. is_in inx ⇒ inhabited (range inx)``,
  rw[] >> imp_res_tac is_in_range_thm >>
  metis_tac[] )

val init_model_def = new_specification("init_model_def",["init_model0"],
    SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] (GEN_ALL init_ctxt_has_model))
val _ = overload_on("init_model",``init_model0 ^mem``)

val bool_ctxt_no_new_axioms =
  ``(∀p. MEM (NewAxiom p) (mk_bool_ctxt init_ctxt) ⇒
         MEM (NewAxiom p) init_ctxt)``
  |> (EVAL THENC (SIMP_CONV std_ss []))
  |> EQT_ELIM

val bool_model_exists =
  extends_consistent
  |> UNDISCH
  |> Q.SPECL[`init_ctxt`,`mk_bool_ctxt init_ctxt`]
  |> C MATCH_MP bool_extends_init
  |> SPEC ``init_model``
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]
  |> C MATCH_MP init_theory_ok
  |> C MATCH_MP (UNDISCH (SPEC mem init_model_def))
  |> C MATCH_MP bool_ctxt_no_new_axioms
  |> DISCH_ALL |> GEN_ALL
  |> SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM]

val bool_model_def = new_specification("bool_model_def",["bool_model0"],
  bool_model_exists)
val _ = overload_on("bool_model",``bool_model0 ^mem``)
val bool_model_models = UNDISCH (SPEC mem bool_model_def)

val bool_theory_ok =
extends_theory_ok
|> Q.SPECL[`init_ctxt`,`mk_bool_ctxt init_ctxt`]
|> SIMP_RULE std_ss [bool_extends_init,init_theory_ok]

val bool_model_interpretation =
bool_has_bool_interpretation
|> UNDISCH
|> Q.SPEC`init_ctxt`
|> Q.SPEC`bool_model`
|> SIMP_RULE std_ss [bool_model_models,bool_theory_ok]

val _ = map2 (curry save_thm)
  ["bool_theory_ok","bool_model_interpretation","bool_model_models"]
  [ bool_theory_ok , bool_model_interpretation , bool_model_models]

val not_thm = prove(
  ``is_set_theory ^mem ⇒
    (Abstract boolset boolset (λx. Boolean (¬finv in_bool x)) =
     Abstract boolset boolset (λp. Boolean (p ≠ True)))``,
  rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[boolean_in_boolset] >>
  rw[boolean_def] >>
  metis_tac[finv_in_bool_eq_true])

val in_fun_not =
``in_fun in_bool in_bool $~``
  |> SIMP_CONV std_ss [Once in_bool_def,in_fun_def,UNDISCH range_in_bool,UNDISCH not_thm]

val in_bool_false =
  ``in_bool F``
  |> SIMP_CONV std_ss [in_bool_def,boolean_def]

val in_bool_true =
  ``in_bool T``
  |> SIMP_CONV std_ss [in_bool_def,boolean_def]

val range_in_fun_ina_in_bool =
range_in_fun |> GEN_ALL |> SPEC mem
  |> Q.ISPECL[`in_bool`,`ina:'a -> 'U`]
  |> SIMP_RULE std_ss [UNDISCH is_in_in_bool,GSYM AND_IMP_INTRO]
  |> UNDISCH |> UNDISCH

val forall_thm = prove(
  ``is_set_theory ^mem ⇒ is_in ina ⇒
    (Abstract (Funspace (range ina) boolset) boolset
       (λP. Boolean (∀x. x <: range ina ⇒ Holds P x)) =
     Abstract (Funspace (range ina) boolset) boolset
       (λx. in_bool ($! (finv (in_fun ina in_bool) x))))``,
  rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  rw[boolean_in_boolset,Once in_bool_def] >>
  rw[Once in_bool_def] >> AP_TERM_TAC >>
  `∃f. (x = in_fun ina Boolean (λa. (f (ina a)) = True)) ∧
       (∀a. f (ina a) <: boolset)` by (
    simp[UNDISCH range_in_bool,in_fun_def,GSYM in_bool_def] >>
    qspecl_then[`x`,`range ina`,`boolset`]mp_tac (UNDISCH in_funspace_abstract) >>
    discharge_hyps  >- metis_tac[inhabited_range,mem_boolset] >> rw[] >>
    qexists_tac`f` >> simp[in_bool_def] >>
    reverse conj_tac >- metis_tac[is_in_range_thm] >>
    match_mp_tac (UNDISCH abstract_eq) >>
    simp[boolean_in_boolset] >> rw[] >>
    simp[boolean_def] >> rw[] >>
    imp_res_tac is_in_finv_right >>
    metis_tac[mem_boolset] ) >>
  Q.ISPEC_THEN`in_fun ina Boolean`mp_tac is_in_finv_left >>
  discharge_hyps >- metis_tac[is_in_in_fun,is_in_in_bool,in_bool_def] >>
  simp[holds_def,GSYM in_bool_def] >>
  disch_then kall_tac >>
  rw[EQ_IMP_THM] >- (
    first_x_assum(qspec_then`ina a`mp_tac) >>
    discharge_hyps >- metis_tac[is_in_range_thm] >>
    simp[in_fun_def] >>
    disch_then (SUBST1_TAC o SYM) >>
    match_mp_tac EQ_SYM >>
    match_mp_tac apply_abstract_matchable >>
    simp[is_in_range_thm,GSYM in_bool_def,range_in_bool] >>
    simp[in_bool_def,boolean_in_boolset] >>
    Q.ISPEC_THEN`ina`mp_tac is_in_finv_left >> rw[] >>
    rw[boolean_def] >>
    metis_tac[mem_boolset] ) >>
  rw[in_fun_def] >>
  match_mp_tac apply_abstract_matchable >>
  simp[is_in_range_thm,GSYM in_bool_def,range_in_bool] >>
  simp[in_bool_def,boolean_in_boolset] >>
  rw[boolean_def]) |> UNDISCH |> UNDISCH

val in_fun_forall =
  ``in_fun (in_fun ina in_bool) in_bool $!``
  |> SIMP_CONV std_ss [in_fun_def,UNDISCH range_in_bool,range_in_fun_ina_in_bool,GSYM forall_thm]

val exists_thm = prove(
  ``is_set_theory ^mem ⇒ is_in ina ⇒
    (Abstract (Funspace (range ina) boolset) boolset
       (λP. Boolean (?x. x <: range ina ∧ Holds P x)) =
     Abstract (Funspace (range ina) boolset) boolset
       (λx. in_bool ($? (finv (in_fun ina in_bool) x))))``,
  rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  rw[boolean_in_boolset,Once in_bool_def] >>
  rw[Once in_bool_def] >> AP_TERM_TAC >>
  `∃f. (x = in_fun ina Boolean (λa. (f (ina a)) = True)) ∧
       (∀a. f (ina a) <: boolset)` by (
    simp[UNDISCH range_in_bool,in_fun_def,GSYM in_bool_def] >>
    qspecl_then[`x`,`range ina`,`boolset`]mp_tac (UNDISCH in_funspace_abstract) >>
    discharge_hyps  >- metis_tac[inhabited_range,mem_boolset] >> rw[] >>
    qexists_tac`f` >> simp[in_bool_def] >>
    reverse conj_tac >- metis_tac[is_in_range_thm] >>
    match_mp_tac (UNDISCH abstract_eq) >>
    simp[boolean_in_boolset] >> rw[] >>
    simp[boolean_def] >> rw[] >>
    imp_res_tac is_in_finv_right >>
    metis_tac[mem_boolset] ) >>
  Q.ISPEC_THEN`in_fun ina Boolean`mp_tac is_in_finv_left >>
  discharge_hyps >- metis_tac[is_in_in_fun,is_in_in_bool,in_bool_def] >>
  simp[holds_def,GSYM in_bool_def] >>
  disch_then kall_tac >>
  rw[EQ_IMP_THM] >- (
    qmatch_assum_rename_tac`z <: range ina`[] >>
    qexists_tac`finv ina z` >>
    pop_assum mp_tac >>
    simp[in_fun_def] >>
    disch_then (SUBST1_TAC o SYM) >>
    match_mp_tac EQ_SYM >>
    match_mp_tac apply_abstract_matchable >>
    simp[is_in_range_thm,GSYM in_bool_def,range_in_bool] >>
    simp[in_bool_def,boolean_in_boolset] >>
    rw[boolean_def] >>
    metis_tac[mem_boolset] ) >>
  rw[in_fun_def] >>
  qexists_tac`ina a` >>
  conj_tac >- metis_tac[is_in_range_thm] >>
  match_mp_tac apply_abstract_matchable >>
  simp[is_in_range_thm,GSYM in_bool_def,range_in_bool] >>
  simp[in_bool_def,boolean_in_boolset] >>
  rw[boolean_def] >>
  metis_tac[is_in_finv_left]) |> UNDISCH |> UNDISCH

val in_fun_exists =
  ``in_fun (in_fun ina in_bool) in_bool $?``
  |> SIMP_CONV std_ss [in_fun_def,UNDISCH range_in_bool,range_in_fun_ina_in_bool,GSYM exists_thm]

val range_in_fun_in_bool_in_bool =
range_in_fun |> GEN_ALL |> SPEC mem
  |> Q.ISPECL[`in_bool`,`in_bool`]
  |> SIMP_RULE std_ss [UNDISCH is_in_in_bool]
  |> UNDISCH

val binop_thm1 = prove(
  ``is_set_theory ^mem ∧ p <: boolset ⇒
    (Abstract boolset boolset (λx. in_bool (op (finv in_bool p) (finv in_bool x))) =
     Abstract boolset boolset (λq. Boolean (op (p = True) (q = True))))``,
  rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  rw[boolean_in_boolset] >>
  rw[Once in_bool_def,boolean_in_boolset] >>
  `EVERY (λz. z = True ⇔ finv in_bool z) [p;x]` by (
    simp[] >> metis_tac[finv_in_bool_eq_true]) >>
  fs[boolean_def])

val binop_thm = prove(
  ``is_set_theory ^mem ⇒
    (Abstract boolset (Funspace boolset boolset)
      (λy. Abstract boolset boolset (λx. in_bool (op (finv in_bool y) (finv in_bool x)))) =
     Abstract boolset (Funspace boolset boolset)
      (λp. Abstract boolset boolset (λq. Boolean (op (p = True) (q = True)))))``,
  rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  rw[binop_thm1] >>
  match_mp_tac (UNDISCH abstract_in_funspace) >>
  rw[boolean_in_boolset])

val in_fun_binop =
  ``in_fun in_bool (in_fun in_bool in_bool) op``
  |> SIMP_CONV std_ss [in_fun_def,UNDISCH range_in_bool,range_in_fun_in_bool_in_bool,UNDISCH binop_thm]

val in_fun_select = prove(
  ``is_set_theory ^mem ⇒ is_in ina ⇒
    (in_fun (in_fun ina in_bool) ina $@ =
     Abstract (range (in_fun ina in_bool)) (range ina)
       (λp. ina (@x. Holds p (ina x))))``,
  rw[in_fun_def] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[in_bool_def,boolean_in_boolset] >>
  simp[is_in_range_thm] >>
  simp[GSYM in_bool_def] >>
  Q.ISPEC_THEN`in_bool`mp_tac(Q.GEN`inb`range_in_fun) >>
  discharge_hyps >- metis_tac[is_in_in_bool] >> rw[] >>
  AP_TERM_TAC >> AP_TERM_TAC >>
  qmatch_abbrev_tac`l = r` >>
  qsuff_tac`in_fun ina in_bool l = in_fun ina in_bool r` >- (
    `is_in (in_fun ina in_bool)` by metis_tac[is_in_in_fun,is_in_in_bool] >>
    fs[is_in_def,BIJ_DEF,INJ_DEF] ) >>
  Q.ISPEC_THEN`in_fun ina in_bool`mp_tac is_in_finv_right >>
  discharge_hyps >- metis_tac[is_in_in_fun,is_in_in_bool] >>
  simp[range_in_fun] >> disch_then(qspec_then`x`mp_tac) >>
  discharge_hyps >- simp[] >>
  simp[Abbr`l`] >> disch_then kall_tac >>
  simp[Abbr`r`] >>
  Q.ISPECL_THEN[`x`,`range ina`,`range in_bool`]mp_tac(UNDISCH in_funspace_abstract) >>
  discharge_hyps >- ( metis_tac[inhabited_range,is_in_in_bool] ) >>
  rw[] >>
  simp[in_fun_def] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[range_in_bool] >>
  simp[in_bool_def,boolean_in_boolset] >>
  rw[holds_def] >>
  qmatch_abbrev_tac`f x = Boolean (b = True)` >>
  `b = f x` by (
    simp[Abbr`b`] >>
    match_mp_tac apply_abstract_matchable >>
    metis_tac[is_in_finv_right,range_in_bool] ) >>
  rw[boolean_def] >>
  metis_tac[range_in_bool,mem_boolset]) |> UNDISCH

val _ = map2 (curry save_thm)
  ["in_fun_not","in_fun_forall","in_fun_exists","in_fun_binop","in_bool_false","in_bool_true","in_fun_select"]
  [ in_fun_not , in_fun_forall , in_fun_exists , in_fun_binop , in_bool_false , in_bool_true , in_fun_select ]

val is_select_sig_def = Define`
  is_select_sig sig ⇔
  is_bool_sig sig ∧
  (FLOOKUP (tmsof sig) "@" = SOME (Fun (Fun (Tyvar "A") Bool) (Tyvar "A")))`

val select_sig_instances = store_thm("select_sig_instances",
  ``is_select_sig sig ⇒
    (instance (tmsof sig) i "@" (Fun (Fun ty Bool) ty) =
       (λτ. tmaof i "@" [typesem (tyaof i) τ ty]))``,
  rw[is_select_sig_def] >>
  Q.ISPECL_THEN[`tmsof sig`,`i`,`"@"`]mp_tac instance_def >> simp[] >>
  disch_then(qspec_then`[ty,Tyvar "A"]`mp_tac) >>
  EVAL_TAC >> rw[])

val select_has_select_sig = store_thm("select_has_select_sig",
  ``is_bool_sig (sigof ctxt) ⇒ is_select_sig (sigof (mk_select_ctxt ctxt))``,
  rw[is_select_sig_def] >- (
    fs[is_bool_sig_def,mk_select_ctxt_def,FLOOKUP_UPDATE] >>
    fs[is_std_sig_def,FLOOKUP_UPDATE] ) >>
  EVAL_TAC)

val select_model_exists = prove(
  ``∃f. ∀mem select. is_set_theory mem ⇒ good_select select ⇒
      subinterpretation (mk_bool_ctxt init_ctxt) (bool_model0 mem) (f mem select) ∧
      f mem select models thyof (mk_select_ctxt (mk_bool_ctxt init_ctxt)) ∧
      (tmaof (f mem select) "@" = λls.
        Abstract (Funspace (HD ls) boolset) (HD ls)
          (λp. select (HD ls) (Holds p)))``,
  rw[GSYM SKOLEM_THM,RIGHT_EXISTS_IMP_THM] >>
  qspec_then`mk_bool_ctxt init_ctxt`mp_tac(UNDISCH select_has_model_gen) >>
  discharge_hyps_keep >- (
    simp[bool_theory_ok] >>
    EVAL_TAC ) >>
  disch_then match_mp_tac >>
  conj_asm1_tac >- simp[bool_model_def] >>
  assume_tac bool_model_interpretation >>
  fs[is_bool_interpretation_def])

val select_model_def = new_specification("select_model_def",["select_model0"],
  select_model_exists)
val _ = overload_on("select_model",``select_model0 ^mem``)
val select_model_models = GEN_ALL (UNDISCH (SPEC_ALL (SPEC mem select_model_def)))

val select_extends_bool = prove(
  ``mk_select_ctxt (mk_bool_ctxt init_ctxt) extends mk_bool_ctxt init_ctxt``,
  match_mp_tac select_extends >>
  conj_tac >- (
    match_mp_tac is_bool_sig_std >>
    match_mp_tac bool_has_bool_sig >>
    ACCEPT_TAC (MATCH_MP theory_ok_sig init_theory_ok |> SIMP_RULE std_ss[]) ) >>
  EVAL_TAC )

val select_theory_ok =
extends_theory_ok
|> Q.SPECL[`mk_bool_ctxt init_ctxt`,`mk_select_ctxt (mk_bool_ctxt init_ctxt)`]
|> SIMP_RULE std_ss [bool_theory_ok,select_extends_bool]

val select_bool_interpretation = prove(
  ``is_set_theory ^mem ⇒
    good_select select ⇒
    is_bool_interpretation (select_model select)``,
  rw[] >>
  first_assum(strip_assume_tac o MATCH_MP select_model_models) >>
  assume_tac bool_model_interpretation >>
  fs[subinterpretation_def,is_bool_interpretation_def] >>
  conj_tac >- ( fs[models_def] ) >>
  fs[term_ok_def] >>
  rpt conj_tac >>
  qmatch_abbrev_tac`tmaof (select_model select) interprets name on args as val` >>
  first_x_assum(qspec_then`name`mp_tac) >>
  qunabbrev_tac`name` >>
  CONV_TAC(LAND_CONV(QUANT_CONV(LAND_CONV EVAL))) >>
  simp[Abbr`args`,Abbr`val`,type_ok_def,FLOOKUP_UPDATE] >>
  fs[interprets_def] >> rw[] >>
  TRY( first_x_assum match_mp_tac >>
       metis_tac[base_tyval_def] ) >>
  fs[PULL_EXISTS,type_ok_def,FLOOKUP_UPDATE] >>
  first_x_assum(qspec_then`[]`mp_tac)>>
  (discharge_hyps >- EVAL_TAC) >> rw[]) |> UNDISCH |> UNDISCH

val _ = map2 (curry save_thm)
  ["select_theory_ok","select_extends_bool","select_bool_interpretation","select_model_models"]
  [ select_theory_ok , select_extends_bool , select_bool_interpretation , select_model_models ]

val constrained_term_valuation_exists = store_thm("constrained_term_valuation_exists",
  ``is_set_theory ^mem ⇒
    ∀tysig δ τ.  is_type_valuation τ ⇒ is_type_assignment tysig δ ⇒
    ∀constraints.
    ALL_DISTINCT (MAP FST constraints) ∧
    EVERY (λ(k,v). type_ok tysig (SND k) ∧
                   v <: typesem δ τ (SND k)) constraints
    ⇒
    ∃σ.
      is_term_valuation tysig δ τ σ ∧
      EVERY (λ(k,v). σ k = v) constraints``,
  strip_tac >> ntac 3 gen_tac >> ntac 2 strip_tac >> Induct >> simp[] >-
    metis_tac[term_valuation_exists,is_valuation_def,FST,SND] >>
  qx_gen_tac`p` >>
  `∃k v. p = (k,v)` by metis_tac[pair_CASES] >>
  rw[] >> fs[] >>
  qexists_tac`(k =+ v) σ` >>
  simp[APPLY_UPDATE_THM] >>
  conj_tac >- (
    fs[is_term_valuation_def,APPLY_UPDATE_THM] >>
    rw[] >> fs[] ) >>
  fs[EVERY_MEM] >>
  Cases >> simp[] >>
  fs[MEM_MAP,Once FORALL_PROD] >>
  rw[] >> metis_tac[])

val rwt = MATCH_MP (PROVE[]``P x ⇒ ((∀x. P x ⇒ Q) ⇔ Q)``) base_tyval_def
val interprets_nil = save_thm("interprets_nil",
  interprets_def |> SPEC_ALL |> Q.GEN`vs` |> Q.SPEC`[]`
  |> SIMP_RULE (std_ss++LIST_ss) [rwt] |> GEN_ALL)

val interprets_one = store_thm("interprets_one",
  ``i interprets name on [v] as f ⇔
    (∀x. inhabited x ⇒ (i name [x] = f [x]))``,
  rw[interprets_def,EQ_IMP_THM] >>
  TRY (
    first_x_assum match_mp_tac >>
    fs[is_type_valuation_def] ) >>
  first_x_assum(qspec_then`K x`mp_tac) >>
  simp[] >> disch_then match_mp_tac >>
  rw[is_type_valuation_def] >> metis_tac[])

(* TODO: move *)

val boolean_of_eq_true = store_thm("boolean_of_eq_true",
  ``is_set_theory ^mem ⇒
    ∀b. b <: boolset ⇒ (Boolean (b = True) = b)``,
  rw[boolean_def] >> rw[] >>
  metis_tac[mem_boolset])

val is_std_sig_extends = store_thm("is_std_sig_extends",
  ``∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒ is_std_sig (sigof ctxt1) ⇒ is_std_sig (sigof ctxt2)``,
  ho_match_mp_tac extends_ind >>
  REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac updates_ind >>
  rw[is_std_sig_def,FLOOKUP_UPDATE,FLOOKUP_FUNION] >>
  TRY BasicProvers.CASE_TAC >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
  metis_tac[] )

val is_bool_sig_extends = store_thm("is_bool_sig_extends",
  ``∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒ is_bool_sig (sigof ctxt1) ⇒ is_bool_sig (sigof ctxt2)``,
  ho_match_mp_tac extends_ind >>
  REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac updates_ind >>
  conj_tac >- rw[is_bool_sig_def] >>
  conj_tac >- (
    rw[is_bool_sig_def,is_std_sig_def] >>
    rw[FLOOKUP_UPDATE] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,FORALL_PROD] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[is_bool_sig_def,is_std_sig_def] >>
    rw[FLOOKUP_UPDATE,FLOOKUP_FUNION] >>
    BasicProvers.CASE_TAC >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[is_bool_sig_def,is_std_sig_def] >>
    rw[FLOOKUP_UPDATE] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,FORALL_PROD] >>
    metis_tac[] ) >>
  rw[is_bool_sig_def,is_std_sig_def] >>
  rw[FLOOKUP_UPDATE,FLOOKUP_FUNION] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,FORALL_PROD] >>
  metis_tac[] )

val _ = export_theory()
