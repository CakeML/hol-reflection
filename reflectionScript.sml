open HolKernel boolLib bossLib Parse lcsymtacs listSimps countableLib countableTheory
open miscLib basicReflectionLib pred_setTheory listTheory pairTheory combinTheory finite_mapTheory alistTheory
open miscTheory setSpecTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory
open holBoolSyntaxTheory holBoolTheory holExtensionTheory holConsistencyTheory holAxiomsSyntaxTheory holAxiomsTheory
open holConstrainedExtensionTheory

val _ = temp_tight_equality()
val _ = new_theory"reflection"

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
  good_context ^mem (^tysig,^tmsig) (^tyass,^tmass) (^tyval,^tmval) ⇔
    is_set_theory ^mem ∧
    is_std_sig ^signatur ∧
    is_interpretation ^signatur ^interpretation ∧
    is_std_interpretation ^interpretation ∧
    is_valuation ^tysig ^tyass ^valuation`
val good_context = good_context_def |> concl |> strip_forall |> snd |> lhs

val good_context_unpaired = store_thm("good_context_unpaired",
  ``good_context mem sig i v ⇔
    is_set_theory mem ∧
    is_std_sig sig ∧
    is_interpretation sig i ∧
    is_std_interpretation i ∧
    is_valuation (tysof sig) (tyaof i) v``,
  map_every PairCases_on[`sig`,`i`,`v`]>>rw[good_context_def])

val finv_def = Define`
  finv f x = @y. f y = x`

val wf_to_inner_def = xDefine"wf_to_inner"`
  wf_to_inner0 ^mem f = ∃x. BIJ f UNIV {a | mem a x}`
val _ = Parse.overload_on("wf_to_inner",``wf_to_inner0 ^mem``)

val wf_to_inner_finv_left = store_thm("wf_to_inner_finv_left",
  ``∀ina.
    wf_to_inner ina ⇒ ∀x. finv ina (ina x) = x``,
  rw[finv_def] >>
  SELECT_ELIM_TAC >>
  conj_tac >-metis_tac[] >>
  fs[wf_to_inner_def,BIJ_DEF,INJ_DEF])

val ext_def = xDefine"ext"`
  ext0 ^mem s = { a | mem a s }`
val _ = Parse.overload_on("ext",``ext0 ^mem``)

val range_def = xDefine"range"`
  range0 ^mem (f : α -> 'U) = @x. BIJ f UNIV {a | mem a x}`
val _ = Parse.overload_on("range",``range0 ^mem``)

val wf_to_inner_bij_thm = store_thm("wf_to_inner_bij_thm",
  ``∀f. wf_to_inner f ⇒ BIJ f UNIV (ext (range f))``,
  rw[wf_to_inner_def,range_def] >>
  SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >>
  rw[ext_def])

val wf_to_inner_range_thm = store_thm("wf_to_inner_range_thm",
  ``∀f x. wf_to_inner f ⇒ f x <: range f``,
  rw[] >>
  imp_res_tac wf_to_inner_bij_thm >>
  fs[BIJ_DEF,ext_def,INJ_DEF])

val wf_to_inner_finv_right = store_thm("wf_to_inner_finv_right",
  ``∀ina.
    wf_to_inner ina ⇒ ∀x. x <: range ina ⇒
      (ina (finv ina x)) = x``,
  rw[finv_def] >>
  SELECT_ELIM_TAC >>
  conj_tac >-(
    imp_res_tac wf_to_inner_bij_thm >>
    fs[ext_def,BIJ_DEF,SURJ_DEF] ) >>
  rw[])

val bool_to_inner_def = xDefine"bool_to_inner"`
  bool_to_inner0 ^mem = Boolean`
val _ = Parse.overload_on("bool_to_inner",``bool_to_inner0 ^mem``)

val wf_to_inner_bool_to_inner = store_thm("wf_to_inner_bool_to_inner",
  ``is_set_theory ^mem ⇒
    wf_to_inner bool_to_inner``,
  rw[wf_to_inner_def,BIJ_IFF_INV] >>
  qexists_tac`boolset` >>
  rw[bool_to_inner_def,boolean_in_boolset] >>
  qexists_tac`λx. x = True` >>
  rw[bool_to_inner_def,boolean_eq_true] >>
  rfs[mem_boolset,boolean_eq_true,true_neq_false,boolean_def])

val fun_to_inner_def = xDefine"fun_to_inner"`
  fun_to_inner0 ^mem ina inb f =
    Abstract (range ina) (range inb) (λx. inb (f (finv ina x)))`
val _ = Parse.overload_on("fun_to_inner",``fun_to_inner0 ^mem``)

val out_fun_def = xDefine"out_fun"`
  out_fun0 ^mem ina inb mf x = finv inb (mf ' (ina x))`
val _ = Parse.overload_on("out_fun",``out_fun0 ^mem``)

val wf_to_inner_fun_to_inner = store_thm("wf_to_inner_fun_to_inner",
  ``is_set_theory ^mem ⇒
    ∀ina inb. wf_to_inner ina ∧ wf_to_inner inb ⇒ wf_to_inner (fun_to_inner ina inb)``,
  rw[] >>
  rw[wf_to_inner_def,BIJ_IFF_INV] >>
  qexists_tac`Funspace (range ina) (range inb)` >>
  conj_tac >- (
    rw[fun_to_inner_def] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[range_def] >>
    SELECT_ELIM_TAC >>
    conj_tac >- metis_tac[wf_to_inner_def] >>
    rw[] >>
    SELECT_ELIM_TAC >>
    conj_tac >- metis_tac[wf_to_inner_def] >>
    rw[] >>
    fs[BIJ_IFF_INV] ) >>
  qexists_tac`out_fun ina inb` >>
  conj_tac >- (
    rw[out_fun_def,fun_to_inner_def,FUN_EQ_THM] >>
    qmatch_abbrev_tac`finv invb (Abstract s t f ' a) = Z` >>
    rfs[] >>
    `Abstract s t f ' a = f a` by (
      match_mp_tac (UNDISCH apply_abstract) >>
      imp_res_tac wf_to_inner_bij_thm >>
      fs[ext_def,BIJ_IFF_INV] >>
      unabbrev_all_tac >> fs[] ) >>
    rw[Abbr`Z`,Abbr`f`,Abbr`a`,Abbr`invb`] >>
    imp_res_tac wf_to_inner_finv_left >>
    simp[] ) >>
  rw[fun_to_inner_def,out_fun_def] >>
  first_x_assum(mp_tac o
    MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO](UNDISCH in_funspace_abstract))) >>
  rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  gen_tac >>
  qspecl_then[`f`,`ina (finv ina x)`,`range ina`,`range inb`]mp_tac
    (UNDISCH apply_abstract) >>
  discharge_hyps >- (
    imp_res_tac wf_to_inner_bij_thm >>
    fs[ext_def,BIJ_DEF,INJ_DEF] ) >>
  rw[] >>
  imp_res_tac wf_to_inner_finv_right >>
  rw[])

val range_bool_to_inner = store_thm("range_bool_to_inner",
  ``is_set_theory ^mem ⇒
    range bool_to_inner = boolset``,
  strip_tac >>
  imp_res_tac wf_to_inner_bool_to_inner >>
  imp_res_tac wf_to_inner_bij_thm >>
  imp_res_tac is_extensional >>
  pop_assum mp_tac >>
  simp[extensional_def] >>
  disch_then kall_tac >>
  fs[ext_def,BIJ_IFF_INV,mem_boolset] >>
  fs[bool_to_inner_def,boolean_def] >>
  metis_tac[] )

val range_fun_to_inner = store_thm("range_fun_to_inner",
  ``is_set_theory ^mem ∧ wf_to_inner ina ∧ wf_to_inner inb ⇒
    range (fun_to_inner ina inb) = Funspace (range ina) (range inb)``,
  rw[] >>
  strip_assume_tac(SPEC_ALL (UNDISCH wf_to_inner_fun_to_inner)) >> rfs[] >>
  imp_res_tac wf_to_inner_bij_thm >>
  imp_res_tac is_extensional >>
  pop_assum mp_tac >>
  simp[extensional_def] >>
  disch_then kall_tac >>
  fs[ext_def,BIJ_IFF_INV] >>
  rw[EQ_IMP_THM] >- (
    fs[fun_to_inner_def] >>
    res_tac >>
    pop_assum(SUBST1_TAC o SYM) >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    rw[] ) >>
  qspecl_then[`a`,`range ina`,`range inb`]mp_tac (UNDISCH in_funspace_abstract) >>
  simp[] >> strip_tac >>
  qpat_assum`a = X`(SUBST1_TAC) >>
  qsuff_tac`∃x. Abstract (range ina) (range inb) f = fun_to_inner ina inb x` >- metis_tac[] >>
  rw[fun_to_inner_def] >>
  qexists_tac`finv inb o f o ina` >>
  match_mp_tac (UNDISCH abstract_eq) >> simp[] >>
  metis_tac[wf_to_inner_finv_right,wf_to_inner_finv_left])

val finv_bool_to_inner_eq_true = store_thm("finv_bool_to_inner_eq_true",
  ``is_set_theory ^mem ⇒
    ∀x.
    ((x = True) ⇒ finv bool_to_inner x) ∧
    (x <: boolset ∧ finv bool_to_inner x ⇒ (x = True))``,
  metis_tac[wf_to_inner_finv_right,bool_to_inner_def,boolean_def,range_bool_to_inner,wf_to_inner_bool_to_inner,wf_to_inner_finv_left])

val finv_bool_to_inner_True = prove(
``^good_context ⇒
  (finv bool_to_inner x ⇒ y) ⇒ ((x = True) ⇒ y)``,
  metis_tac[finv_bool_to_inner_eq_true,good_context_def]) |> UNDISCH
val _ = save_thm("finv_bool_to_inner_True",finv_bool_to_inner_True)

val [count_mlstring_aux_inj_rwt] = mk_count_aux_inj_rwt[``:mlstring``]
val [count_type_aux_inj_rwt] = mk_count_aux_inj_rwt_ttac[``:type``]
  (SOME(WF_REL_TAC`measure type_size`>>gen_tac>>Induct>>
        rw[type_size_def]>>res_tac>>simp[]))
val countable_type = inj_rwt_to_countable count_type_aux_inj_rwt
val type_rep_def = new_specification("type_rep_def",["type_rep"],
  countable_type |> REWRITE_RULE[countable_def])

val num_def = xDefine"num"`
  (num0 ^mem (0:num) = empty mem) ∧
  (num0 ^mem (SUC n) = num0 mem n + one mem)`
val _ = Parse.overload_on("num",``num0 ^mem``)

val num_not_one = store_thm("num_not_one",
  ``is_set_theory ^mem ⇒ ∀n. num n ≠ One``,
  strip_tac >> Induct >> rw[num_def] >>
  imp_res_tac is_extensional >> fs[extensional_def] >> pop_assum kall_tac >>
  rfs[mem_empty,mem_one,mem_upair] >>
  `One ≠ ∅` by (
    imp_res_tac is_extensional >> fs[extensional_def] >> pop_assum kall_tac >>
    simp[mem_one,mem_empty] ) >>
  fs[EQ_IMP_THM] >> metis_tac[])

val num_suc_not_empty = store_thm("num_suc_not_empty",
  ``is_set_theory ^mem ⇒ ∀n. num (SUC n) ≠ ∅``,
  rw[num_def] >>
  imp_res_tac is_extensional >> fs[extensional_def] >> pop_assum kall_tac >>
  simp[mem_empty,mem_upair] >> metis_tac[])

val num_inj = store_thm("num_inj",
  ``is_set_theory ^mem ⇒
    ∀m n. (num m = num n) ⇔ (m = n)``,
  strip_tac >>
  Induct >> simp[num_def] >- (
    Cases >> simp[num_def] >> rw[] >>
    imp_res_tac is_extensional >>
    fs[extensional_def] >> pop_assum kall_tac >>
    simp[mem_empty,mem_upair] >>
    metis_tac[] ) >>
  Cases >> rw[num_def] >- (
    imp_res_tac is_extensional >>
    fs[extensional_def] >> pop_assum kall_tac >>
    simp[mem_empty,mem_upair] >>
    metis_tac[] ) >>
  fs[EQ_IMP_THM] >> rw[] >>
  first_x_assum match_mp_tac >>
  imp_res_tac is_extensional >>
  fs[extensional_def] >> pop_assum kall_tac >>
  rfs[mem_upair] >> metis_tac[num_not_one])

val pair_not_empty = store_thm("pair_not_empty",
  ``is_set_theory ^mem ⇒ ∀x y. (x,y) ≠ ∅``,
  rw[] >>
  imp_res_tac is_extensional >> fs[extensional_def] >> pop_assum kall_tac >>
  simp[mem_empty,pair_def,mem_upair] >> metis_tac[])

val pair_not_one = store_thm("pair_not_one",
  ``is_set_theory ^mem ⇒ ∀x y. (x,y) ≠ One``,
  rw[] >>
  imp_res_tac is_extensional >> fs[extensional_def] >> pop_assum kall_tac >>
  rfs[mem_one,mem_empty,mem_upair,pair_def] >> rw[] >>
  spose_not_then strip_assume_tac >>
  first_x_assum(qspec_then`∅`mp_tac) >> simp[] >>
  imp_res_tac is_extensional >> fs[extensional_def] >> pop_assum kall_tac >>
  simp[mem_empty,mem_unit,mem_upair] >>
  metis_tac[])

val tag_exists = prove(
  ``∃tag:('U->'U->bool)->type->'U->'U.
      ∀mem. is_set_theory mem ⇒
        (∀ty1 v1 ty2 v2.
           (((ty1,v1) ≠ (ty2,v2)) ⇒ tag mem ty1 v1 ≠ tag mem ty2 v2)) ∧
        (∀ty v. ∃u. IMAGE (tag mem ty) (ext v) = ext u) ∧
        (∀ty v. ¬ (tag mem ty v <: boolset) ∧
                (∀x y. ¬ (tag mem ty v <: Funspace x y)))``,
  qexists_tac`λmem ty x. Two ∪ (Unit(num (type_rep ty), x))` >>
  gen_tac >> strip_tac >> simp[] >>
  conj_tac >- (
    rpt gen_tac >>
    qmatch_abbrev_tac`p ⇒ q` >> strip_tac >>
    qunabbrev_tac`q` >>
    imp_res_tac is_extensional >>
    pop_assum mp_tac >>
    simp[extensional_def] >>
    disch_then kall_tac >>
    simp[mem_binary_union,mem_boolset,mem_unit] >>
    qexists_tac`num(type_rep ty1),v1` >>
    simp[pair_inj,num_inj] >>
    conj_tac >- (
      simp[true_def,false_def,pair_not_empty,pair_not_one] ) >>
    fs[Abbr`p`] >>
    metis_tac[type_rep_def,INJ_DEF,IN_UNIV]) >>
  conj_tac >- (
    rw[EXTENSION,PULL_EXISTS,ext_def] >>
    qexists_tac`Pow (boolset ∪ Unit(num (type_rep ty)) × v) suchthat
                λx. ∃a. a <: v ∧ x = boolset ∪ Unit (num (type_rep ty),a)` >>
    simp[mem_sub,mem_power] >> gen_tac >>
    reverse EQ_TAC >- metis_tac[] >> strip_tac >>
    reverse conj_tac >- metis_tac[] >>
    rfs[mem_binary_union,mem_unit,mem_product] >> rw[] >>
    rw[pair_inj]) >>
  rw[] >- (
    simp[mem_boolset,true_def,false_def] >>
    imp_res_tac is_extensional >> fs[extensional_def] >> pop_assum kall_tac >>
    simp[mem_binary_union,mem_unit,mem_boolset,true_def,false_def,mem_empty,mem_one] >>
    simp[EQ_IMP_THM] >>
    metis_tac[pair_not_empty] ) >>
  strip_tac >>
  imp_res_tac (UNDISCH in_funspace_abstract) >>
  qpat_assum`X = Y`mp_tac >>
  imp_res_tac is_extensional >> fs[extensional_def] >> pop_assum kall_tac >>
  simp[EQ_IMP_THM,EXISTS_OR_THM] >> disj1_tac >>
  srw_tac[boolSimps.DNF_ss][mem_binary_union,mem_boolset,true_def] >> disj1_tac >>
  simp[abstract_def,mem_sub,mem_product,pair_not_empty])

val tag_def =
  new_specification("tag_def",["tag0"],tag_exists)
  |> SPEC mem
val _ = overload_on("tag",``tag0 ^mem``)
val _ = save_thm("tag_def",tag_def)

val to_inner_def = xDefine"to_inner"`
  to_inner0 ^mem (ty:type) = (tag ty) o (@f. wf_to_inner f)`
val _ = overload_on("to_inner",``to_inner0 ^mem``)

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
    termsem ^tmsig ^interpretation ^valuation ftm =
      fun_to_inner ina inb f ∧
    termsem ^tmsig ^interpretation ^valuation xtm = ina x ⇒
    wf_to_inner ina ⇒ wf_to_inner inb
    ⇒
    termsem ^tmsig ^interpretation ^valuation (Comb ftm xtm) =
      inb (f x)``,
  rw[good_context_def,termsem_def] >>
  first_assum(SUBST1_TAC o SYM) >>
  rw[fun_to_inner_def] >>
  match_mp_tac apply_abstract_matchable >>
  simp[] >>
  rw[wf_to_inner_range_thm] >>
  AP_TERM_TAC >>
  AP_TERM_TAC >>
  match_mp_tac wf_to_inner_finv_left >>
  simp[]) |> UNDISCH

val Abs_thm = prove(
  ``^good_context ⇒
    ∀ina inb f x xty b bty.
    typesem tyass tyval xty = range ina ∧
    typesem tyass tyval bty = range inb ⇒
    (*
    wf_to_inner ina ⇒ (* these are unnecessary for this theorem *)
    wf_to_inner inb ⇒ (* but useful for the automation *)
    *)
    term_ok (tysig,tmsig) b ∧
    typeof b = bty ∧
    (∀m. m <: range ina ⇒
      termsem tmsig (tyass,tmass) (tyval,((x,xty) =+ m) tmval) b =
        inb (f (finv ina m)))
    ⇒
    termsem tmsig (tyass,tmass) (tyval,tmval) (Abs (Var x xty) b) =
      fun_to_inner ina inb f
      ``,
  rw[termsem_def,fun_to_inner_def,good_context_def] >>
  match_mp_tac (UNDISCH abstract_eq) >> simp[] >>
  rw[] >>
  res_tac >> first_x_assum(SUBST1_TAC o SYM) >>
  first_assum(SUBST1_TAC o SYM) >>
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

val good_context_wf_to_inner_bool_to_inner = prove(mk_imp(good_context,rand(concl(wf_to_inner_bool_to_inner))),
  rw[good_context_def,wf_to_inner_bool_to_inner]) |> UNDISCH

val good_context_wf_to_inner_fun_to_inner = prove(mk_imp(good_context,rand(concl(wf_to_inner_fun_to_inner))),
  rw[good_context_def,wf_to_inner_fun_to_inner]) |> UNDISCH

val good_context_tyass_bool = prove(
  ``^good_context ==> (tyass (strlit"bool") [] = range bool_to_inner)``,
  rw[good_context_def,is_std_interpretation_def,is_std_type_assignment_def,range_bool_to_inner]) |> UNDISCH

val good_context_tyass_fun = prove(
  ``^good_context ==> !tya tyb ina inb.
      wf_to_inner ina /\ wf_to_inner inb /\ tya = range ina /\ tyb = range inb ==>
        tyass (strlit"fun") [tya; tyb] = range (fun_to_inner ina inb)``,
  rw[good_context_def,is_std_interpretation_def,is_std_type_assignment_def,range_fun_to_inner]
  ) |> UNDISCH

val good_context_lookup_bool = prove(
  ``^good_context ⇒ FLOOKUP ^tysig (strlit "bool") = SOME 0``,
  rw[good_context_def,is_std_sig_def]) |> UNDISCH

val good_context_lookup_fun = prove(
  ``^good_context ⇒ FLOOKUP ^tysig (strlit "fun") = SOME 2``,
  rw[good_context_def,is_std_sig_def]) |> UNDISCH

val good_context_extend_tmval = prove(
  ``^good_context ∧
     m <: typesem ^tyass ^tyval ty ⇒
     good_context ^mem (^tysig,^tmsig) (^tyass,^tmass) (^tyval,(((x,ty) =+ m) ^tmval))``,
  rw[good_context_def,is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> rw[])

val good_context_instance_equality = prove(
  ``∀ty ina.
    ^good_context ∧
    type_ok ^tysig ty ∧
    typesem ^tyass ^tyval ty = range ina ∧
    wf_to_inner ina ⇒
    instance ^tmsig ^interpretation (strlit"=") (Fun ty (Fun ty Bool)) ^tyval =
      fun_to_inner ina (fun_to_inner ina bool_to_inner) $=``,
  rw[good_context_def] >>
  fs[is_std_sig_def] >>
  imp_res_tac instance_def >>
  first_x_assum(qspec_then`[ty,Tyvar (strlit"A")]`mp_tac) >>
  simp[holSyntaxLibTheory.REV_ASSOCD] >>
  disch_then(mp_tac o SPEC interpretation) >>
  simp[] >> disch_then kall_tac >>
  EVAL_STRING_SORT >> simp[holSyntaxLibTheory.REV_ASSOCD] >>
  fs[is_std_interpretation_def,interprets_def] >>
  first_x_assum(qspec_then`(strlit"A"=+ typesem ^tyass ^tyval ty)(K boolset)`mp_tac) >>
  discharge_hyps >- (
    simp[is_type_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
    reverse(rw[mem_boolset]) >- metis_tac[] >>
    qpat_assum`X = Y` (SUBST1_TAC o SYM) >>
    match_mp_tac (UNDISCH typesem_inhabited) >>
    fs[is_valuation_def,is_interpretation_def] >>
    metis_tac[] ) >>
  simp[combinTheory.APPLY_UPDATE_THM,mlstringTheory.implode_def] >>
  disch_then kall_tac >>
  simp[fun_to_inner_def] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[] >> gen_tac >> strip_tac >>
  conj_tac >- (
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[boolean_in_boolset] ) >>
  Q.ISPECL_THEN[`mem`,`bool_to_inner`,`ina`]mp_tac (GEN_ALL range_fun_to_inner) >>
  discharge_hyps >- ( simp[wf_to_inner_bool_to_inner] ) >>
  strip_tac >> simp[range_bool_to_inner] >>
  Q.ISPECL_THEN[`mem`,`bool_to_inner`,`ina`]mp_tac (GEN_ALL range_fun_to_inner) >>
  discharge_hyps >- ( simp[wf_to_inner_bool_to_inner] ) >>
  strip_tac >> simp[range_bool_to_inner] >>
  conj_tac >- (
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[bool_to_inner_def,boolean_in_boolset] ) >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[bool_to_inner_def,boolean_in_boolset] >>
  simp[boolean_def] >> rw[true_neq_false] >>
  spose_not_then strip_assume_tac >>
  metis_tac[wf_to_inner_finv_right])

val _ = save_thms
  ["good_context_wf_to_inner_bool_to_inner",
   "good_context_wf_to_inner_fun_to_inner",
   "good_context_tyass_bool", "good_context_tyass_fun",
   "good_context_lookup_bool","good_context_lookup_fun",
   "good_context_extend_tmval","good_context_instance_equality"]
  [ good_context_wf_to_inner_bool_to_inner ,
    good_context_wf_to_inner_fun_to_inner ,
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
  ``∀inx. wf_to_inner inx ⇒ inhabited (range inx)``,
  rw[] >> imp_res_tac wf_to_inner_range_thm >>
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
    (Abstract boolset boolset (λx. Boolean (¬finv bool_to_inner x)) =
     Abstract boolset boolset (λp. Boolean (p ≠ True)))``,
  rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[boolean_in_boolset] >>
  rw[boolean_def] >>
  metis_tac[finv_bool_to_inner_eq_true])

val fun_to_inner_not =
``fun_to_inner bool_to_inner bool_to_inner $~``
  |> SIMP_CONV std_ss [Once bool_to_inner_def,fun_to_inner_def,UNDISCH range_bool_to_inner,UNDISCH not_thm]

val bool_to_inner_false =
  ``bool_to_inner F``
  |> SIMP_CONV std_ss [bool_to_inner_def,boolean_def]

val bool_to_inner_true =
  ``bool_to_inner T``
  |> SIMP_CONV std_ss [bool_to_inner_def,boolean_def]

val range_fun_to_inner_ina_bool_to_inner =
range_fun_to_inner |> GEN_ALL |> SPEC mem
  |> Q.ISPECL[`bool_to_inner`,`ina:'a -> 'U`]
  |> SIMP_RULE std_ss [UNDISCH wf_to_inner_bool_to_inner,GSYM AND_IMP_INTRO]
  |> UNDISCH |> UNDISCH

val forall_thm = prove(
  ``is_set_theory ^mem ⇒ wf_to_inner ina ⇒
    (Abstract (Funspace (range ina) boolset) boolset
       (λP. Boolean (∀x. x <: range ina ⇒ Holds P x)) =
     Abstract (Funspace (range ina) boolset) boolset
       (λx. bool_to_inner ($! (finv (fun_to_inner ina bool_to_inner) x))))``,
  rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  rw[boolean_in_boolset,Once bool_to_inner_def] >>
  rw[Once bool_to_inner_def] >> AP_TERM_TAC >>
  `∃f. (x = fun_to_inner ina Boolean (λa. (f (ina a)) = True)) ∧
       (∀a. f (ina a) <: boolset)` by (
    simp[UNDISCH range_bool_to_inner,fun_to_inner_def,GSYM bool_to_inner_def] >>
    qspecl_then[`x`,`range ina`,`boolset`]mp_tac (UNDISCH in_funspace_abstract) >>
    discharge_hyps  >- metis_tac[inhabited_range,mem_boolset] >> rw[] >>
    qexists_tac`f` >> simp[bool_to_inner_def] >>
    reverse conj_tac >- metis_tac[wf_to_inner_range_thm] >>
    match_mp_tac (UNDISCH abstract_eq) >>
    simp[boolean_in_boolset] >> rw[] >>
    simp[boolean_def] >> rw[] >>
    imp_res_tac wf_to_inner_finv_right >>
    metis_tac[mem_boolset] ) >>
  Q.ISPEC_THEN`fun_to_inner ina Boolean`mp_tac wf_to_inner_finv_left >>
  discharge_hyps >- metis_tac[wf_to_inner_fun_to_inner,wf_to_inner_bool_to_inner,bool_to_inner_def] >>
  simp[holds_def,GSYM bool_to_inner_def] >>
  disch_then kall_tac >>
  rw[EQ_IMP_THM] >- (
    first_x_assum(qspec_then`ina a`mp_tac) >>
    discharge_hyps >- metis_tac[wf_to_inner_range_thm] >>
    simp[fun_to_inner_def] >>
    disch_then (SUBST1_TAC o SYM) >>
    match_mp_tac EQ_SYM >>
    match_mp_tac apply_abstract_matchable >>
    simp[wf_to_inner_range_thm,GSYM bool_to_inner_def,range_bool_to_inner] >>
    simp[bool_to_inner_def,boolean_in_boolset] >>
    Q.ISPEC_THEN`ina`mp_tac wf_to_inner_finv_left >> rw[] >>
    rw[boolean_def] >>
    metis_tac[mem_boolset] ) >>
  rw[fun_to_inner_def] >>
  match_mp_tac apply_abstract_matchable >>
  simp[wf_to_inner_range_thm,GSYM bool_to_inner_def,range_bool_to_inner] >>
  simp[bool_to_inner_def,boolean_in_boolset] >>
  rw[boolean_def]) |> UNDISCH |> UNDISCH

val fun_to_inner_forall =
  ``fun_to_inner (fun_to_inner ina bool_to_inner) bool_to_inner $!``
  |> SIMP_CONV std_ss [fun_to_inner_def,UNDISCH range_bool_to_inner,range_fun_to_inner_ina_bool_to_inner,GSYM forall_thm]

val exists_thm = prove(
  ``is_set_theory ^mem ⇒ wf_to_inner ina ⇒
    (Abstract (Funspace (range ina) boolset) boolset
       (λP. Boolean (?x. x <: range ina ∧ Holds P x)) =
     Abstract (Funspace (range ina) boolset) boolset
       (λx. bool_to_inner ($? (finv (fun_to_inner ina bool_to_inner) x))))``,
  rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  rw[boolean_in_boolset,Once bool_to_inner_def] >>
  rw[Once bool_to_inner_def] >> AP_TERM_TAC >>
  `∃f. (x = fun_to_inner ina Boolean (λa. (f (ina a)) = True)) ∧
       (∀a. f (ina a) <: boolset)` by (
    simp[UNDISCH range_bool_to_inner,fun_to_inner_def,GSYM bool_to_inner_def] >>
    qspecl_then[`x`,`range ina`,`boolset`]mp_tac (UNDISCH in_funspace_abstract) >>
    discharge_hyps  >- metis_tac[inhabited_range,mem_boolset] >> rw[] >>
    qexists_tac`f` >> simp[bool_to_inner_def] >>
    reverse conj_tac >- metis_tac[wf_to_inner_range_thm] >>
    match_mp_tac (UNDISCH abstract_eq) >>
    simp[boolean_in_boolset] >> rw[] >>
    simp[boolean_def] >> rw[] >>
    imp_res_tac wf_to_inner_finv_right >>
    metis_tac[mem_boolset] ) >>
  Q.ISPEC_THEN`fun_to_inner ina Boolean`mp_tac wf_to_inner_finv_left >>
  discharge_hyps >- metis_tac[wf_to_inner_fun_to_inner,wf_to_inner_bool_to_inner,bool_to_inner_def] >>
  simp[holds_def,GSYM bool_to_inner_def] >>
  disch_then kall_tac >>
  rw[EQ_IMP_THM] >- (
    qmatch_assum_rename_tac`z <: range ina`[] >>
    qexists_tac`finv ina z` >>
    pop_assum mp_tac >>
    simp[fun_to_inner_def] >>
    disch_then (SUBST1_TAC o SYM) >>
    match_mp_tac EQ_SYM >>
    match_mp_tac apply_abstract_matchable >>
    simp[wf_to_inner_range_thm,GSYM bool_to_inner_def,range_bool_to_inner] >>
    simp[bool_to_inner_def,boolean_in_boolset] >>
    rw[boolean_def] >>
    metis_tac[mem_boolset] ) >>
  rw[fun_to_inner_def] >>
  qexists_tac`ina a` >>
  conj_tac >- metis_tac[wf_to_inner_range_thm] >>
  match_mp_tac apply_abstract_matchable >>
  simp[wf_to_inner_range_thm,GSYM bool_to_inner_def,range_bool_to_inner] >>
  simp[bool_to_inner_def,boolean_in_boolset] >>
  rw[boolean_def] >>
  metis_tac[wf_to_inner_finv_left]) |> UNDISCH |> UNDISCH

val fun_to_inner_exists =
  ``fun_to_inner (fun_to_inner ina bool_to_inner) bool_to_inner $?``
  |> SIMP_CONV std_ss [fun_to_inner_def,UNDISCH range_bool_to_inner,range_fun_to_inner_ina_bool_to_inner,GSYM exists_thm]

val range_fun_to_inner_bool_to_inner_bool_to_inner =
range_fun_to_inner |> GEN_ALL |> SPEC mem
  |> Q.ISPECL[`bool_to_inner`,`bool_to_inner`]
  |> SIMP_RULE std_ss [UNDISCH wf_to_inner_bool_to_inner]
  |> UNDISCH

val binop_thm1 = prove(
  ``is_set_theory ^mem ∧ p <: boolset ⇒
    (Abstract boolset boolset (λx. bool_to_inner (op (finv bool_to_inner p) (finv bool_to_inner x))) =
     Abstract boolset boolset (λq. Boolean (op (p = True) (q = True))))``,
  rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  rw[boolean_in_boolset] >>
  rw[Once bool_to_inner_def,boolean_in_boolset] >>
  `EVERY (λz. z = True ⇔ finv bool_to_inner z) [p;x]` by (
    simp[] >> metis_tac[finv_bool_to_inner_eq_true]) >>
  fs[boolean_def])

val binop_thm = prove(
  ``is_set_theory ^mem ⇒
    (Abstract boolset (Funspace boolset boolset)
      (λy. Abstract boolset boolset (λx. bool_to_inner (op (finv bool_to_inner y) (finv bool_to_inner x)))) =
     Abstract boolset (Funspace boolset boolset)
      (λp. Abstract boolset boolset (λq. Boolean (op (p = True) (q = True)))))``,
  rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  rw[binop_thm1] >>
  match_mp_tac (UNDISCH abstract_in_funspace) >>
  rw[boolean_in_boolset])

val fun_to_inner_binop =
  ``fun_to_inner bool_to_inner (fun_to_inner bool_to_inner bool_to_inner) op``
  |> SIMP_CONV std_ss [fun_to_inner_def,UNDISCH range_bool_to_inner,range_fun_to_inner_bool_to_inner_bool_to_inner,UNDISCH binop_thm]

val fun_to_inner_select = prove(
  ``is_set_theory ^mem ⇒ wf_to_inner ina ⇒
    (fun_to_inner (fun_to_inner ina bool_to_inner) ina $@ =
     Abstract (range (fun_to_inner ina bool_to_inner)) (range ina)
       (λp. ina (@x. Holds p (ina x))))``,
  rw[fun_to_inner_def] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[bool_to_inner_def,boolean_in_boolset] >>
  simp[wf_to_inner_range_thm] >>
  simp[GSYM bool_to_inner_def] >>
  Q.ISPEC_THEN`bool_to_inner`mp_tac(Q.GEN`inb`range_fun_to_inner) >>
  discharge_hyps >- metis_tac[wf_to_inner_bool_to_inner] >> rw[] >>
  AP_TERM_TAC >> AP_TERM_TAC >>
  qmatch_abbrev_tac`l = r` >>
  qsuff_tac`fun_to_inner ina bool_to_inner l = fun_to_inner ina bool_to_inner r` >- (
    `wf_to_inner (fun_to_inner ina bool_to_inner)` by metis_tac[wf_to_inner_fun_to_inner,wf_to_inner_bool_to_inner] >>
    fs[wf_to_inner_def,BIJ_DEF,INJ_DEF] ) >>
  Q.ISPEC_THEN`fun_to_inner ina bool_to_inner`mp_tac wf_to_inner_finv_right >>
  discharge_hyps >- metis_tac[wf_to_inner_fun_to_inner,wf_to_inner_bool_to_inner] >>
  simp[range_fun_to_inner] >> disch_then(qspec_then`x`mp_tac) >>
  discharge_hyps >- simp[] >>
  simp[Abbr`l`] >> disch_then kall_tac >>
  simp[Abbr`r`] >>
  Q.ISPECL_THEN[`x`,`range ina`,`range bool_to_inner`]mp_tac(UNDISCH in_funspace_abstract) >>
  discharge_hyps >- ( metis_tac[inhabited_range,wf_to_inner_bool_to_inner] ) >>
  rw[] >>
  simp[fun_to_inner_def] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[range_bool_to_inner] >>
  simp[bool_to_inner_def,boolean_in_boolset] >>
  rw[holds_def] >>
  qmatch_abbrev_tac`f x = Boolean (b:'U = True)` >>
  `b = f x` by (
    simp[Abbr`b`] >>
    match_mp_tac apply_abstract_matchable >>
    metis_tac[wf_to_inner_finv_right,range_bool_to_inner] ) >>
  rw[boolean_def] >>
  metis_tac[range_bool_to_inner,mem_boolset]) |> UNDISCH

local
  val dest_fun_to_inner = dest_triop ``fun_to_inner0`` (mk_HOL_ERR"""dest_fun_to_inner""")
  val range_fun_to_inner0 =
    range_fun_to_inner
    |> Q.GENL[`inb`,`ina`,`mem`]
    |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
in
  fun range_fun_to_inner_conv tm =
    let
      val fun_to_inner_ina_inb = rand tm
      val (mem,ina,inb) = dest_fun_to_inner fun_to_inner_ina_inb
      val th = ISPECL[mem,ina,inb] range_fun_to_inner0 |> funpow 3 UNDISCH
    in
      REWR_CONV th tm
    end
end

val fun_to_inner_equals = prove(
  ``is_set_theory ^mem ⇒ wf_to_inner ina ⇒
    (fun_to_inner ina (fun_to_inner ina bool_to_inner) $= =
     Abstract (range ina) (Funspace (range ina) boolset)
       (λx. Abstract (range ina) boolset (λy. Boolean (x = y))))``,
  rw[] >>
  rw[fun_to_inner_def] >>
  assume_tac (UNDISCH wf_to_inner_bool_to_inner) >>
  CONV_TAC(DEPTH_CONV range_fun_to_inner_conv) >>
  simp[range_bool_to_inner] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[] >> rw[] >>
  TRY (
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[bool_to_inner_def,boolean_in_boolset] ) >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[bool_to_inner_def,boolean_in_boolset] >>
  rw[boolean_def] >>
  metis_tac[wf_to_inner_finv_right]) |> funpow 2 UNDISCH

val _ = map2 (curry save_thm)
  ["fun_to_inner_not","fun_to_inner_forall","fun_to_inner_exists","fun_to_inner_binop","bool_to_inner_false","bool_to_inner_true","fun_to_inner_select","fun_to_inner_equals"]
  [ fun_to_inner_not , fun_to_inner_forall , fun_to_inner_exists , fun_to_inner_binop , bool_to_inner_false , bool_to_inner_true , fun_to_inner_select , fun_to_inner_equals ]

val std_sig_instances = store_thm("std_sig_instances",
  ``is_std_sig sig ⇒
    (instance (tmsof sig) i (strlit"=") (Fun ty (Fun ty Bool)) =
       (λτ. tmaof i (strlit"=") [typesem (tyaof i) τ ty]))``,
  rw[is_std_sig_def] >>
  Q.ISPECL_THEN[`tmsof sig`,`i`,`strlit"="`]mp_tac instance_def >> simp[] >>
  disch_then(qspec_then`[ty,Tyvar (strlit"A")]`mp_tac) >>
  EVAL_TAC >> simp[])

val is_select_sig_def = Define`
  is_select_sig sig ⇔
  is_bool_sig sig ∧
  (FLOOKUP (tmsof sig) (strlit"@") = SOME (Fun (Fun (Tyvar (strlit"A")) Bool) (Tyvar (strlit"A"))))`

val select_sig_instances = store_thm("select_sig_instances",
  ``is_select_sig sig ⇒
    (instance (tmsof sig) i (strlit"@") (Fun (Fun ty Bool) ty) =
       (λτ. tmaof i (strlit"@") [typesem (tyaof i) τ ty]))``,
  rw[is_select_sig_def] >>
  Q.ISPECL_THEN[`tmsof sig`,`i`,`strlit"@"`]mp_tac instance_def >> simp[] >>
  disch_then(qspec_then`[ty,Tyvar (strlit"A")]`mp_tac) >>
  EVAL_TAC >> rw[])

val bool_sig_defs = [is_true_sig_def,is_false_sig_def,is_implies_sig_def,
  is_and_sig_def,is_or_sig_def,is_not_sig_def,is_forall_sig_def,is_exists_sig_def]

val select_has_select_sig = store_thm("select_has_select_sig",
  ``is_bool_sig (sigof ctxt) ⇒ is_select_sig (sigof (mk_select_ctxt ctxt))``,
  rw[is_select_sig_def] >- (
    fs([is_bool_sig_def,mk_select_ctxt_def,FLOOKUP_UPDATE]@bool_sig_defs) >>
    fs[is_std_sig_def,FLOOKUP_UPDATE] ) >>
  EVAL_TAC)

val eta_theory_ok = prove(
  ``theory_ok (thyof (mk_eta_ctxt (mk_bool_ctxt init_ctxt)))``,
  match_mp_tac (MP_CANON extends_theory_ok) >>
  REWRITE_TAC[Once CONJ_COMM] >>
  match_exists_tac (concl bool_theory_ok) >>
  conj_tac >- ACCEPT_TAC bool_theory_ok >>
  match_mp_tac eta_extends >>
  match_mp_tac is_bool_sig_std >>
  match_mp_tac bool_has_bool_sig >>
  ACCEPT_TAC (MATCH_MP theory_ok_sig init_theory_ok |> SIMP_RULE std_ss[]) )

val select_model_exists = prove(
  ``∃f. ∀mem select. is_set_theory mem ⇒ good_select select ⇒
      equal_on (sigof (mk_eta_ctxt (mk_bool_ctxt init_ctxt))) (bool_model0 mem) (f mem select) ∧
      f mem select models thyof (mk_select_ctxt (mk_eta_ctxt (mk_bool_ctxt init_ctxt))) ∧
      (tmaof (f mem select) (strlit"@") = λls.
        Abstract (Funspace (HD ls) boolset) (HD ls)
          (λp. select (HD ls) (Holds p)))``,
  rw[GSYM SKOLEM_THM,RIGHT_EXISTS_IMP_THM] >>
  qspec_then`mk_eta_ctxt (mk_bool_ctxt init_ctxt)`mp_tac(UNDISCH select_has_model_gen) >>
  discharge_hyps_keep >- (
    simp[eta_theory_ok] >>
    EVAL_TAC ) >>
  disch_then match_mp_tac >>
  conj_asm1_tac >- (
    match_mp_tac (MP_CANON (UNDISCH eta_has_model)) >>
    conj_tac >- (
      match_mp_tac is_bool_sig_std >>
      match_mp_tac bool_has_bool_sig >>
      ACCEPT_TAC (MATCH_MP theory_ok_sig init_theory_ok |> SIMP_RULE std_ss[]) ) >>
    simp[bool_model_def] ) >>
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

val select_extends_eta = prove(
  ``mk_select_ctxt (mk_eta_ctxt (mk_bool_ctxt init_ctxt)) extends mk_eta_ctxt (mk_bool_ctxt init_ctxt)``,
  match_mp_tac select_extends >>
  conj_tac >- (
    ACCEPT_TAC (MATCH_MP theory_ok_sig eta_theory_ok |> SIMP_RULE std_ss[])) >>
  EVAL_TAC )

val select_theory_ok =
extends_theory_ok
|> Q.SPECL[`mk_eta_ctxt (mk_bool_ctxt init_ctxt)`,`mk_select_ctxt (mk_eta_ctxt (mk_bool_ctxt init_ctxt))`]
|> SIMP_RULE std_ss [eta_theory_ok,select_extends_eta]

val bool_interpretation_defs =
  [is_true_interpretation_def,
   is_and_interpretation_def,
   is_implies_interpretation_def,
   is_forall_interpretation_def,
   is_exists_interpretation_def,
   is_or_interpretation_def,
   is_false_interpretation_def,
   is_not_interpretation_def]

val extends_bool_interpretation = prove(
  ``is_set_theory ^mem ⇒
    ∀model.
    is_std_interpretation model ∧
    equal_on (sigof (mk_bool_ctxt init_ctxt)) bool_model model ⇒
    is_bool_interpretation model``,
  rw[] >>
  assume_tac bool_model_interpretation >>
  fs([equal_on_def,is_bool_interpretation_def]@bool_interpretation_defs) >>
  fs[term_ok_def] >>
  rpt conj_tac >>
  qmatch_abbrev_tac`tmaof model interprets name on args as val` >>
  first_x_assum(qspec_then`name`mp_tac) >>
  qunabbrev_tac`name` >>
  CONV_TAC(LAND_CONV(LAND_CONV EVAL)) >>
  simp[Abbr`args`,Abbr`val`,type_ok_def,FLOOKUP_UPDATE] >>
  fs[interprets_def] >> rw[] >>
  TRY( first_x_assum match_mp_tac >>
       metis_tac[base_tyval_def] ) >>
  fs[PULL_EXISTS,type_ok_def,FLOOKUP_UPDATE] >>
  first_x_assum(qspec_then`[]`mp_tac)>>
  (discharge_hyps >- EVAL_TAC) >> rw[]) |> UNDISCH

val select_bool_interpretation = prove(
  ``is_set_theory ^mem ⇒
    good_select select ⇒
    is_bool_interpretation (select_model select)``,
  rw[] >>
  match_mp_tac (MP_CANON extends_bool_interpretation) >>
  first_assum(strip_assume_tac o MATCH_MP select_model_models) >>
  conj_tac >- fs[models_def] >>
  match_mp_tac equal_on_reduce >>
  fs[mk_eta_ctxt_def] >>
  qexists_tac`[]`>>simp[]) |> UNDISCH |> UNDISCH

val infinity_extends_select = prove(
  ``mk_infinity_ctxt (mk_select_ctxt (mk_eta_ctxt (mk_bool_ctxt init_ctxt))) extends
    (mk_select_ctxt (mk_eta_ctxt (mk_bool_ctxt init_ctxt)))``,
  match_mp_tac infinity_extends >>
  conj_tac >- (
    ACCEPT_TAC select_theory_ok ) >>
  EVAL_TAC)

val hol_theory_ok = save_thm("hol_theory_ok",
extends_theory_ok
|> Q.SPECL[`mk_select_ctxt (mk_eta_ctxt (mk_bool_ctxt init_ctxt))`,`mk_infinity_ctxt (mk_select_ctxt (mk_eta_ctxt (mk_bool_ctxt init_ctxt)))`]
|> SIMP_RULE std_ss [select_theory_ok,infinity_extends_select]
|> SIMP_RULE std_ss [GSYM hol_ctxt_def])

(* probably not true
val is_bool_interpretation_subinterpretation = store_thm("is_bool_interpretation_subinterpretation",
  ``is_set_theory ^mem ⇒
    (is_bool_interpretation model ⇔
     subinterpretation (mk_bool_ctxt init_ctxt) bool_model model)``,
  strip_tac >> EQ_TAC >> strip_tac >- (
    simp[subinterpretation_def] >>
    assume_tac bool_model_interpretation >>
    simp[term_ok_def,type_ok_def] >>
    conj_tac >> rpt gen_tac >>
    CONV_TAC(LAND_CONV EVAL) >>
    rw[] >>
    fs[is_bool_interpretation_def,is_std_interpretation_def,is_std_type_assignment_def] >>
    fs[interprets_nil,type_ok_def,FLOOKUP_UPDATE] >>
    fs[]
    )
*)

val good_select_extend_base_select = store_thm("good_select_extend_base_select",
  ``∀ina. wf_to_inner ina ⇒
      ∀s. good_select s ⇒
      good_select ((range ina =+ (λp. ina (@x. p (ina x)))) s)``,
  rw[good_select_def,APPLY_UPDATE_THM] >> rw[] >>
  TRY (
    SELECT_ELIM_TAC >> simp[] >>
    qexists_tac`finv ina x` >>
    metis_tac[wf_to_inner_finv_right] ) >>
  metis_tac[wf_to_inner_range_thm])

val select_instance_thm = prove(
  ``is_set_theory ^mem ⇒
    is_select_sig ^signatur ⇒
    good_select select_fun ⇒
    (select_fun (range inty) = λp. inty (@x. p (inty x))) ⇒
    (typesem (tyaof (select_model select_fun)) ^tyval ty = range inty) ⇒
    wf_to_inner inty
    ⇒
    (instance ^tmsig (select_model select_fun) (strlit "@") (Fun (Fun ty Bool) ty) ^tyval =
     fun_to_inner (fun_to_inner inty bool_to_inner) inty $@)``,
  rw[is_select_sig_def] >>
  qspecl_then[`tmsig`,`select_model select_fun`,`strlit"@"`]mp_tac instance_def >>
  simp[] >>
  disch_then(qspec_then`[ty,Tyvar (strlit"A")]`mp_tac) >>
  CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV EVAL))) >>
  simp[] >> disch_then kall_tac >>
  CONV_TAC(LAND_CONV(RAND_CONV EVAL)) >>
  first_assum(assume_tac o MATCH_MP select_model_models) >>
  simp[] >> pop_assum kall_tac >>
  first_assum(mp_tac o MATCH_MP fun_to_inner_select) >>
  simp[] >> disch_then kall_tac >>
  (range_fun_to_inner |> Q.GEN`inb` |> Q.ISPEC`bool_to_inner` |> Q.GEN`ina` |> Q.SPEC_THEN`inty`mp_tac) >>
  simp[wf_to_inner_bool_to_inner] >> disch_then kall_tac >>
  simp[range_bool_to_inner]) |> funpow 2 UNDISCH

val _ = map2 (curry save_thm)
  ["select_theory_ok","select_extends_bool","select_bool_interpretation","select_model_models","select_instance_thm","extends_bool_interpretation"]
  [ select_theory_ok , select_extends_bool , select_bool_interpretation , select_model_models , select_instance_thm , extends_bool_interpretation ]

val is_infinity_sig_def = Define`
  is_infinity_sig sig ⇔
  is_select_sig sig ∧
  (FLOOKUP (tysof sig) (strlit"ind") = SOME 0) ∧
  (FLOOKUP (tmsof sig) (strlit"ONTO") = SOME (Fun (Fun (Tyvar (strlit"A")) (Tyvar (strlit"B"))) Bool)) ∧
  (FLOOKUP (tmsof sig) (strlit"ONE_ONE") = SOME (Fun (Fun (Tyvar (strlit"A")) (Tyvar (strlit"B"))) Bool))`

val infinity_has_infinity_sig = store_thm("infinity_has_infinity_sig",
  ``is_select_sig (sigof ctxt) ⇒ is_infinity_sig (sigof (mk_infinity_ctxt ctxt))``,
  rw[is_infinity_sig_def] >- (
    fs[is_select_sig_def,mk_infinity_ctxt_def,FLOOKUP_UPDATE] >>
    fs([is_bool_sig_def,is_std_sig_def,FLOOKUP_UPDATE]@bool_sig_defs)) >>
  EVAL_TAC)

val is_infinity_sig_hol_ctxt = store_thm("is_infinity_sig_hol_ctxt",
  ``is_infinity_sig (sigof hol_ctxt)``,
  simp[hol_ctxt_def,fhol_ctxt_def] >>
  match_mp_tac infinity_has_infinity_sig >>
  match_mp_tac select_has_select_sig >>
  match_mp_tac (MP_CANON is_bool_sig_extends) >>
  qexists_tac`mk_bool_ctxt init_ctxt` >>
  conj_asm2_tac >- (
    match_mp_tac eta_extends >>
    fs[is_bool_sig_def] ) >>
  match_mp_tac bool_has_bool_sig >>
  ACCEPT_TAC (MATCH_MP theory_ok_sig init_theory_ok |> SIMP_RULE std_ss[]))

val wf_to_inner_ind_to_inner_implies_infinite = store_thm("wf_to_inner_ind_to_inner_implies_infinite",
  ``wf_to_inner (ind_to_inner:ind->'U) ⇒ is_infinite ^mem (range ind_to_inner)``,
  rw[] >>
  imp_res_tac wf_to_inner_bij_thm >>
  rw[is_infinite_def] >>
  `ext (range ind_to_inner) = IMAGE ind_to_inner UNIV` by (
    fs[EXTENSION,BIJ_DEF,INJ_DEF,SURJ_DEF,ext_def] >>
    metis_tac[wf_to_inner_range_thm]) >>
  fs[ext_def] >>
  match_mp_tac (MP_CANON IMAGE_11_INFINITE) >>
  conj_tac >- ( fs[BIJ_DEF,INJ_DEF] ) >>
  match_mp_tac (snd(EQ_IMP_RULE INFINITE_UNIV)) >>
  metis_tac[INFINITY_AX,ONE_ONE_DEF,ONTO_DEF])

val hol_model_exists = prove(
  ``∃i. ∀^mem select ind_to_inner.
        is_set_theory ^mem ∧ good_select select ∧ wf_to_inner (ind_to_inner:ind->'U) ⇒
        i mem select ind_to_inner models (thyof hol_ctxt) ∧
        equal_on (sigof (mk_select_ctxt (mk_eta_ctxt (mk_bool_ctxt init_ctxt))))
          (select_model select) (i mem select ind_to_inner) ∧
        (tyaof (i mem select ind_to_inner) (strlit"ind") [] = range ind_to_inner)``,
  simp[GSYM SKOLEM_THM] >>
  simp[RIGHT_EXISTS_IMP_THM] >> rpt strip_tac >>
  mp_tac (UNDISCH infinity_has_model_gen) >>
  disch_then(qspec_then`mk_select_ctxt (mk_eta_ctxt (mk_bool_ctxt init_ctxt))`mp_tac) >>
  discharge_hyps >- (
    conj_tac >- ACCEPT_TAC select_theory_ok >>
    EVAL_TAC ) >>
  disch_then(qspecl_then[`select_model select`,`range ind_to_inner`]mp_tac) >>
  discharge_hyps >- (
    conj_tac >- (
      Q.SPEC_THEN`select`(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o UNDISCH)
      select_model_models ) >>
    simp[UNDISCH wf_to_inner_ind_to_inner_implies_infinite] >>
    assume_tac select_bool_interpretation >>
    fs[is_bool_interpretation_def] ) >>
  disch_then(qx_choose_then`i`strip_assume_tac) >>
  fs[GSYM hol_ctxt_def,GSYM fhol_ctxt_def] >>
  qexists_tac`i` >> simp[])

val hol_model_def = new_specification("hol_model_def",["hol_model0"],hol_model_exists)
val _ = overload_on("hol_model",``hol_model0 ^mem``)
val hol_model_models = SPEC mem hol_model_def |> SPEC_ALL |>
  SIMP_RULE bool_ss [GSYM AND_IMP_INTRO] |> funpow 3 UNDISCH
val _ = save_thm("hol_model_models",hol_model_models)

val hol_bool_interpretation = prove(
  ``is_set_theory ^mem ⇒
    good_select select ⇒
    wf_to_inner ind_to_inner ⇒
    is_bool_interpretation (hol_model select ind_to_inner)``,
  rw[] >>
  strip_assume_tac hol_model_models >>
  match_mp_tac (MP_CANON extends_bool_interpretation) >>
  conj_tac >- fs[models_def] >>
  qspec_then`select`(mp_tac o CONJUNCT1 o UNDISCH)select_model_models >>
  strip_tac >>
  fs[equal_on_def,type_ok_def,term_ok_def] >>
  conj_tac  >- (
    rpt gen_tac >>
    rpt(first_x_assum(qspec_then`name`mp_tac)) >>
    CONV_TAC(LAND_CONV(LAND_CONV EVAL)) >> strip_tac >>
    CONV_TAC(LAND_CONV(LAND_CONV EVAL)) >> strip_tac >>
    CONV_TAC(LAND_CONV EVAL) >> strip_tac >>
    CONV_TAC(LAND_CONV EVAL) >> strip_tac >>
    CONV_TAC(LAND_CONV EVAL) >> strip_tac >>
    rw[] >> fs[] >> rfs[]) >>
  rpt gen_tac >>
  rpt(first_x_assum(qspec_then`name`mp_tac)) >>
  CONV_TAC(LAND_CONV(LAND_CONV(EVAL))) >> strip_tac >>
  CONV_TAC(LAND_CONV(EVAL)) >> strip_tac >>
  CONV_TAC(LAND_CONV(EVAL)) >> strip_tac >>
  CONV_TAC(LAND_CONV(EVAL)) >> strip_tac >>
  CONV_TAC(LAND_CONV EVAL) >>
  rw[] >> fs[] >> rfs[] >> fs[LENGTH_NIL_SYM] >>
  metis_tac[]) |> funpow 3 UNDISCH
val _ = save_thm("hol_bool_interpretation",hol_bool_interpretation)

val tmaof_constrain_interpretation_lemma = store_thm("tmaof_constrain_interpretation_lemma",
  ``(csi inst = SOME(w,results)) ⇒
    ALL_DISTINCT (MAP FST (consts_of_upd upd)) ⇒
    (LENGTH (consts_of_upd upd) = LENGTH results)
    ⇒ LIST_REL (λname result.
        tmaof (constrain_interpretation upd csi int0) name inst = result)
      (MAP FST (consts_of_upd upd)) results``,
    rw[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
    Cases_on`int0`>>
    rw[EL_MAP,constrain_interpretation_def,constrain_assignment_def] >>
    BasicProvers.CASE_TAC >- (
      imp_res_tac alistTheory.ALOOKUP_FAILS >>
      rfs[MEM_ZIP] >>
      metis_tac[EL_MAP] ) >>
    qsuff_tac`SOME x = SOME (EL n results)`>-rw[]>>
    pop_assum(SUBST1_TAC o SYM) >>
    match_mp_tac alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
    simp[MAP_ZIP,MEM_ZIP] >>
    qexists_tac`n`>>simp[EL_MAP])

val tyaof_constrain_interpretation_lemma = store_thm("tyaof_constrain_interpretation_lemma",
  ``(csi inst = SOME(results,w)) ⇒
    ALL_DISTINCT (MAP FST (types_of_upd upd)) ⇒
    (LENGTH (types_of_upd upd) = LENGTH results)
    ⇒ LIST_REL (λname result.
        tyaof (constrain_interpretation upd csi int0) name inst = result)
      (MAP FST (types_of_upd upd)) results``,
    rw[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
    Cases_on`int0`>>
    rw[EL_MAP,constrain_interpretation_def,constrain_assignment_def] >>
    BasicProvers.CASE_TAC >- (
      imp_res_tac alistTheory.ALOOKUP_FAILS >>
      rfs[MEM_ZIP] >>
      metis_tac[EL_MAP] ) >>
    qsuff_tac`SOME x = SOME (EL n results)`>-rw[]>>
    pop_assum(SUBST1_TAC o SYM) >>
    match_mp_tac alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
    simp[MAP_ZIP,MEM_ZIP] >>
    qexists_tac`n`>>simp[EL_MAP])

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

val axiom_simplifier = store_thm("axiom_simplifier",
  ``p ∧ (termsem tmsig i v t = bool_to_inner p) ⇒
    (termsem tmsig i v t = True)``,
  rpt strip_tac >>
  pop_assum(SUBST1_TAC) >>
  rw[bool_to_inner_def,boolean_def])

val base_valuation_def = new_specification("base_valuation_def",
  ["base_valuation0"],
  prove(``∃v0. ∀mem tysig δ. is_set_theory mem ∧
    is_type_assignment0 mem tysig δ ⇒
    is_valuation0 mem tysig δ (v0 mem tysig δ)``,
    rw[GSYM SKOLEM_THM] >>
    metis_tac[valuation_exists]))
val _ = overload_on("base_valuation",``base_valuation0 ^mem``)

val theory_ok_hol_ctxt = save_thm("theory_ok_hol_ctxt",
  hol_theory_ok |> REWRITE_RULE[
    GSYM holConsistencyTheory.hol_ctxt_def,
    GSYM holConsistencyTheory.fhol_ctxt_def])

val good_context_base_case = prove(
  ``is_set_theory ^mem
    ⇒ wf_to_inner ind_to_inner
    ⇒ good_select select
    ⇒
    good_context mem (sigof hol_ctxt) (hol_model select ind_to_inner)
      (base_valuation (tysof hol_ctxt) (tyaof (hol_model select ind_to_inner)))``,
    ntac 3 strip_tac >>
    simp[good_context_unpaired] >>
    conj_tac >- (
      mp_tac(MATCH_MP theory_ok_sig theory_ok_hol_ctxt) >>
      simp[] ) >>
    conj_asm1_tac >- (
      imp_res_tac hol_model_def >>
      fs[models_def]) >>
    conj_tac >- (
      imp_res_tac hol_model_def >>
      fs[models_def]) >>
    match_mp_tac base_valuation_def >>
    fs[is_interpretation_def]) |> funpow 2 UNDISCH
val _ = save_thm("good_context_base_case",good_context_base_case)

val update_interpretation_def = new_specification("update_interpretation_def",["update_interpretation0"],
  prove(``∃u. ∀mem ctxt upd i.
            sound_update0 mem ctxt upd ∧ models0 mem i (thyof ctxt) ⇒
            equal_on (sigof ctxt) i (u mem ctxt upd i) ∧
            models0 mem (u mem ctxt upd i) (thyof (upd::ctxt))``,
        rw[GSYM SKOLEM_THM] >>
        rw[RIGHT_EXISTS_IMP_THM,holExtensionTheory.sound_update_def]))
val _ = Parse.overload_on("update_interpretation",``update_interpretation0 ^mem``)
val update_interpretation_def = save_thm("update_interpretation_def",update_interpretation_def |> ISPEC mem)

val extend_type_assignment = store_thm("extend_type_assignment",
  ``∀tysig δ v δ'.
    is_valuation tysig δ v ∧
    (∀name. name ∈ FDOM tysig ⇒ δ' name = δ name)
    ⇒ is_valuation tysig δ' v``,
  rw[is_valuation_def,is_term_valuation_def] >>
  metis_tac[typesem_sig])

val update_valuation_def = new_specification("update_valuation_def",["update_valuation0"],
  prove(``∃v. ∀mem ctxt upd δ0 δ v0.
               is_set_theory mem ∧ upd updates ctxt ∧
               is_valuation0 mem (tysof ctxt) δ0 v0 ∧
               (∀name. name ∈ FDOM (tysof ctxt) ⇒ δ name = δ0 name) ∧
               is_type_assignment (tysof (upd::ctxt)) δ
               ⇒
               is_valuation0 mem (tysof (upd::ctxt)) δ (v mem ctxt upd δ0 δ v0) ∧
               tyvof (v mem ctxt upd δ0 δ v0) = tyvof v0 ∧
               ∀x ty. type_ok (tysof ctxt) ty ⇒ tmvof v0 (x,ty) = tmvof (v mem ctxt upd δ0 δ v0) (x,ty)``,
    rw[GSYM SKOLEM_THM] >>
    rw[RIGHT_EXISTS_IMP_THM] >>
    imp_res_tac extend_type_assignment >>
    match_mp_tac (UNDISCH extend_valuation_exists) >>
    simp[] >>
    match_mp_tac (CONJUNCT2 SUBMAP_FUNION_ID) >>
    simp[] >>
    metis_tac[updates_upd_DISJOINT]))
val _ = Parse.overload_on("update_valuation",``update_valuation0 ^mem``)
val update_valuation_def = save_thm("update_valuation_def",update_valuation_def |> ISPEC mem)

val good_context_extend = store_thm("good_context_extend",
  ``∀mem upd ctxt i v.
    good_context mem (sigof ctxt) i v ∧
    upd updates ctxt ∧ sound_update ctxt upd ∧
    i models thyof ctxt
    ⇒
    good_context mem (sigof (upd::ctxt)) (update_interpretation ctxt upd i)
      (update_valuation ctxt upd (tyaof i) (tyaof (update_interpretation ctxt upd i)) v)``,
  rpt gen_tac >>
  PairCases_on`i` >>
  PairCases_on`v` >>
  rw[good_context_def] >>
  imp_res_tac update_interpretation_def >>
  Q.PAT_ABBREV_TAC`δ = tyaof (update_interpretation X Y Z)` >>
  qspecl_then[`ctxt`,`upd`,`i0`,`δ`,`v0,v1`]mp_tac update_valuation_def >>
  simp[] >>
  discharge_hyps >- (
    conj_tac >- ( fs[equal_on_def] ) >>
    fs[models_def,is_interpretation_def] ) >>
  rw[] >>
  qmatch_abbrev_tac`good_context mem sig2 i2 v2` >>
  `∃i3 i4. i2 = (i3,i4) ∧ ∃v3 v4. v2 = (v3,v4)` by metis_tac[pair_CASES] >>
  simp[good_context_def,Abbr`sig2`] >>
  fs[Abbr`i2`,Abbr`v2`,Abbr`δ`] >>
  conj_tac >- (
    qspecl_then[`ctxt`,`upd::ctxt`]mp_tac is_std_sig_extends >>
    simp[extends_def] ) >>
  fs[models_def])

val hol_extends_init = store_thm("hol_extends_init",
  ``hol_ctxt extends init_ctxt``,
  metis_tac[holConsistencyTheory.hol_extends_bool,holBoolSyntaxTheory.bool_extends_init,extends_trans])

val updates_extends_trans = store_thm("updates_extends_trans",
  ``upd updates ctxt ∧ ctxt extends ctxt0 ⇒ upd::ctxt extends ctxt0``,
  rw[extends_def] >>
  rw[Once relationTheory.RTC_CASES1])

(*
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
  |> CONV_RULE (RAND_CONV (REWR_CONV (SYM fun_to_inner_equals)))
val truth_thm =
  truth_thm0 |> CONV_RULE(REWR_CONV is_true_interpretation_def)
  |> CONV_RULE(RAND_CONV(REWR_CONV(SYM bool_to_inner_true)))
val and_thm =
  and_thm0 |> CONV_RULE(RAND_CONV(REWR_CONV(SYM fun_to_inner_binop)))
val implies_thm =
  implies_thm0 |> CONV_RULE(RAND_CONV(REWR_CONV(SYM fun_to_inner_binop)))
val forall_thm =
  forall_thm0|> Q.SPEC`range ina`
  |> C MATCH_MP (UNDISCH (Q.SPEC`ina` inhabited_range))
  |> CONV_RULE (RAND_CONV (REWR_CONV (SYM fun_to_inner_forall)))
val exists_thm =
  exists_thm0|> Q.SPEC`range ina`
  |> C MATCH_MP (UNDISCH (Q.SPEC`ina` inhabited_range))
  |> CONV_RULE (RAND_CONV (REWR_CONV (SYM fun_to_inner_exists)))
val or_thm =
  or_thm0 |> CONV_RULE(RAND_CONV(REWR_CONV(SYM fun_to_inner_binop)))
val falsity_thm =
  falsity_thm0 |> CONV_RULE(RAND_CONV(REWR_CONV(SYM bool_to_inner_false)))
val not_thm =
  not_thm0 |> CONV_RULE(RAND_CONV(REWR_CONV(SYM fun_to_inner_not)))

val _ = map2 (curry save_thm)
  ["equality_thm","truth_thm","and_thm","implies_thm","forall_thm","exists_thm","or_thm","falsity_thm","not_thm"]
  [ equality_thm , truth_thm , and_thm , implies_thm , forall_thm , exists_thm , or_thm , falsity_thm , not_thm ]
*)

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

(*
(* TODO: move *)
val bool_sig_quant_instances = store_thm("bool_sig_quant_instances",
  ``is_bool_sig sig ⇒
    (instance (tmsof sig) i "!" (Fun (Fun ty Bool) Bool) =
       (λτ. tmaof i "!" [typesem (tyaof i) τ ty])) ∧
    (instance (tmsof sig) i "?" (Fun (Fun ty Bool) Bool) =
       (λτ. tmaof i "?" [typesem (tyaof i) τ ty]))``,
  rw[is_bool_sig_def] >>
  Q.ISPECL_THEN[`tmsof sig`,`i`,`"!"`]mp_tac instance_def >> simp[] >>
  disch_then(qspec_then`[ty,Tyvar "A"]`mp_tac) >>
  Q.ISPECL_THEN[`tmsof sig`,`i`,`"?"`]mp_tac instance_def >> simp[] >>
  disch_then(qspec_then`[ty,Tyvar "A"]`mp_tac) >>
  EVAL_TAC >> rw[])

val exists_REV_ASSOCD_thm = store_thm("exists_REV_ASSOCD_thm",
  ``∃i. ty = REV_ASSOCD (Tyvar a) i (Tyvar a)``,
  qexists_tac`[ty,Tyvar a]` >>
  EVAL_TAC )

val hol_is_bool_sig = store_thm("hol_is_bool_sig",
  ``is_bool_sig (sigof hol_ctxt)``,
  match_mp_tac (MP_CANON is_bool_sig_extends) >>
  match_exists_tac(concl hol_extends_bool) >>
  simp[hol_extends_bool] >>
  match_mp_tac bool_has_bool_sig >>
  ACCEPT_TAC (MATCH_MP theory_ok_sig init_theory_ok |> SIMP_RULE std_ss[]))

(* TODO: move *)

(*
val LCA_def = Define`
  LCA l f ⇔
    ∀m. m < l ⇒
      ∀n. POW (f m n) ≼ f m (n+1) ∧
          f m n ≼ f (m+1) 0`

          is_set_theory_V
          type_of``V_mem``
          IN_POW
          type_of``POW``
          SUBSET_DEF
*)

val transitive_set_def = xDefine"transitive_set"`
  transitive_set0 ^mem x = ∀y. y <: x ⇒ (∀z. z <: y ⇒ z <: x)`
val _ = overload_on("transitive_set",``transitive_set0 ^mem``)

val is_universe_def = xDefine"is_universe"`
  is_universe0 ^mem u ⇔
    inhabited u ∧
    transitive_set u ∧
    (∀x. x <: u ⇒ Pow x <: u) ∧
    (∀x. x <: u ⇒ union mem x <: u) ∧
    (∀x y. x <: u ∧ y <: u ⇒ x + y <: u)`
val _ = overload_on("is_universe",``is_universe0 ^mem``)

open setModelTheory

val is_set_theory_pred_universe = store_thm("is_set_theory_pred_universe",
  ``is_set_theory ^mem ⇒
      ∀u. is_universe u ⇒
        is_set_theory_pred (combin$C mem u) ^mem``,
  rw[] >>
  simp[is_set_theory_pred_def] >>
  conj_tac >- metis_tac[is_universe_def] >>
  conj_tac >- (
    imp_res_tac is_extensional >>
    fs[extensional_def,is_universe_def,transitive_set_def] >>
    metis_tac[] ) >>
  conj_tac >- (
    assume_tac(UNDISCH mem_power) >> rw[] >>
    qexists_tac`x suchthat P` >>
    metis_tac[mem_sub,is_universe_def,transitive_set_def]) >>
  conj_tac >- (
    rw[] >>
    qexists_tac`Pow x` >>
    metis_tac[mem_power,is_universe_def,transitive_set_def] ) >>
  conj_tac >- (
    rw[] >>
    qexists_tac`union mem x` >>
    metis_tac[mem_union,is_universe_def,transitive_set_def]) >>
  conj_tac >- (
    rw[] >>
    qexists_tac`x + y` >>
    metis_tac[mem_upair,is_universe_def,transitive_set_def]) >>
  metis_tac[])

(* {n_universes x n} says that there is a tower of n universes
 * such that the lowest universe contains the set x
 * (in our application, we use {x = range in_ind})
 *)
val n_universes_def = xDefine"n_universes"`
  n_universes0 ^mem x n ⇔
    ∃f. (f 0 = x) ∧
        ∀k. k < n ⇒ is_universe (f (k+1)) ∧
                    f k <: f (k+1)`
val _ = overload_on("n_universes",``n_universes0 ^mem``)

val boolean_of_eq_true = store_thm("boolean_of_eq_true",
  ``is_set_theory ^mem ⇒
    ∀b. b <: boolset ⇒ (Boolean (b = True) = b)``,
  rw[boolean_def] >> rw[] >>
  metis_tac[mem_boolset])
*)

val bool_cert_thm = prove(
  ``^good_context ==>
      (wf_to_inner bool_to_inner /\
       typesem tyass tyval (Tyapp (strlit"bool") []) = range bool_to_inner)``,
  rw[good_context_def,is_std_interpretation_def,is_std_type_assignment_def] >>
  rw[wf_to_inner_bool_to_inner,range_bool_to_inner,typesem_def]) |> UNDISCH;

val fun_cert_thm = prove(
  ``^good_context ==>
    (wf_to_inner ty1_to_inner /\ typesem tyass tyval ty1 = range ty1_to_inner) ==>
    (wf_to_inner ty2_to_inner /\ typesem tyass tyval ty2 = range ty2_to_inner) ==>
      (wf_to_inner (fun_to_inner ty1_to_inner ty2_to_inner) /\
       typesem tyass tyval (Tyapp (strlit"fun") [ty1; ty2]) = range (fun_to_inner ty1_to_inner ty2_to_inner))``,
  rw[good_context_def,typesem_def,is_std_interpretation_def,is_std_type_assignment_def] >>
  rw[wf_to_inner_fun_to_inner,range_fun_to_inner]) |> UNDISCH;

(*
val tag_def = Define`
  (tag : (type # 'U) -> 'U) = @f. INJ f UNIV UNIV`

val in_def_def = Define`
  in_def0 ^mem ty x = tag (ty, ((@f. is_in f) x))`
val _ = Parse.overload_on("in_def",``in_def0 ^mem``)
*)

val tyvar_cert_thm = prove(
  ``^good_context ==>
    wf_to_inner (to_inner (Tyvar v) : 'a -> 'U) ==>
    tyval v = range (to_inner (Tyvar v) : 'a -> 'U) ==>
      (wf_to_inner (to_inner (Tyvar v) : 'a -> 'U) /\
       typesem tyass tyval (Tyvar v) = range (to_inner (Tyvar v) : 'a -> 'U))``,
  rw[typesem_def]) |> UNDISCH |> UNDISCH |> UNDISCH;

val tycon_cert_thm = prove(
  ``^good_context ==>
    wf_to_inner (to_inner (Tyapp con args) : 'a -> 'U) ==>
    tyass con (MAP (typesem tyass tyval) args) = range (to_inner (Tyapp con args) : 'a -> 'U) ==>
      (wf_to_inner (to_inner (Tyapp con args) : 'a -> 'U) /\
       typesem tyass tyval (Tyapp con args) = range (to_inner (Tyapp con args) : 'a -> 'U))``,
  rw[typesem_def] >> metis_tac[]) |> UNDISCH |> UNDISCH |> UNDISCH;

val _ = save_thms ["bool_cert_thm", "fun_cert_thm", "tyvar_cert_thm", "tycon_cert_thm"]
                  [ bool_cert_thm,   fun_cert_thm,   tyvar_cert_thm,   tycon_cert_thm ]

val _ = export_theory()
