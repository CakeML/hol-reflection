open preamble countableLib countableTheory
open basicReflectionLib
open setSpecTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory
open holBoolSyntaxTheory holBoolTheory holExtensionTheory holConsistencyTheory holAxiomsSyntaxTheory holAxiomsTheory
open holConstrainedExtensionTheory
local open holSyntaxLib in end

val _ = temp_tight_equality()
val _ = new_theory"reflection"

val _ = Parse.remove_type_abbrev"reln"

(* TODO: this is a hack... *)
val tyvar_inst_exists2 = store_thm("tyvar_inst_exists2",
  ``∃i. tyvar = REV_ASSOCD b1 i b1 ∧
        tyvar = REV_ASSOCD b2 i b2``,
  qexists_tac`[(tyvar,b1);(tyvar,b2)]` >>
  EVAL_TAC)
val tyvar_inst_exists2_diff = store_thm("tyvar_inst_exists2_diff",
  ``b1 ≠ b2 ⇒
    ∃i. ty1 = REV_ASSOCD b1 i b1 ∧
        ty2 = REV_ASSOCD b2 i b2``,
  strip_tac >>
  qexists_tac`[(ty1,b1);(ty2,b2)]` >>
  EVAL_TAC >> rw[])
(* -- *)

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
  good_context ^mem (^tysig,^tmsig) (^tyass,^tmass) ⇔
    is_set_theory ^mem ∧
    is_std_sig ^signatur ∧
    is_interpretation ^signatur ^interpretation ∧
    is_std_interpretation ^interpretation`
val good_context = good_context_def |> concl |> strip_forall |> snd |> lhs
val is_valuation = ``is_valuation ^tysig ^tyass ^valuation``

val good_context_unpaired = store_thm("good_context_unpaired",
  ``good_context mem sig i ⇔
    is_set_theory mem ∧
    is_std_sig sig ∧
    is_interpretation sig i ∧
    is_std_interpretation i``,
  map_every PairCases_on[`sig`,`i`]>>rw[good_context_def])

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
  impl_tac >- (
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
  ``^good_context ⇒ ^is_valuation ⇒
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
  rw[] >> metis_tac[]) |> funpow 2 UNDISCH

val save_thms = map2 (curry save_thm)
val _ = save_thms ["Var_thm","Const_thm","Comb_thm","Abs_thm"]
                  [ Var_thm , Const_thm , Comb_thm , Abs_thm ]

val tyass_bool_thm = prove(
  ``is_set_theory ^mem ⇒ is_std_type_assignment tyass ==> (tyass (strlit"bool") [] = range bool_to_inner)``,
  rw[is_std_type_assignment_def,range_bool_to_inner]) |> funpow 2 UNDISCH

val tyass_fun_thm = prove(
  ``is_set_theory ^mem ⇒ is_std_type_assignment tyass ==> !tya tyb ina inb.
      wf_to_inner ina /\ wf_to_inner inb /\ tya = range ina /\ tyb = range inb ==>
        tyass (strlit"fun") [tya; tyb] = range (fun_to_inner ina inb)``,
  rw[is_std_type_assignment_def,range_fun_to_inner]
  ) |> funpow 2 UNDISCH

val good_context_lookup_bool = prove(
  ``^good_context ⇒ FLOOKUP ^tysig (strlit "bool") = SOME 0``,
  rw[good_context_def,is_std_sig_def]) |> UNDISCH

val good_context_lookup_fun = prove(
  ``^good_context ⇒ FLOOKUP ^tysig (strlit "fun") = SOME 2``,
  rw[good_context_def,is_std_sig_def]) |> UNDISCH

val is_valuation_extend = prove(
  ``^is_valuation ∧ m <: typesem ^tyass ^tyval ty ⇒
     is_valuation ^tysig ^tyass (^tyval,(((x,ty) =+ m) ^tmval))``,
  rw[is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> rw[])

val good_context_instance_equality = prove(
  ``∀ty ina.
    ^good_context ∧ ^is_valuation ∧
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
  impl_tac >- (
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
  impl_tac >- ( simp[wf_to_inner_bool_to_inner] ) >>
  strip_tac >> simp[range_bool_to_inner] >>
  Q.ISPECL_THEN[`mem`,`bool_to_inner`,`ina`]mp_tac (GEN_ALL range_fun_to_inner) >>
  impl_tac >- ( simp[wf_to_inner_bool_to_inner] ) >>
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
  ["tyass_bool_thm", "tyass_fun_thm",
   "good_context_lookup_bool","good_context_lookup_fun",
   "is_valuation_extend", "good_context_instance_equality"]
  [ tyass_bool_thm ,  tyass_fun_thm ,
    good_context_lookup_bool , good_context_lookup_fun ,
    is_valuation_extend, good_context_instance_equality ]

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
  ``∀ls t. is_type_valuation t ⇒ EVERY (inhabited o SND) ls ⇒ is_type_valuation (t =++ ls)``,
  simp[AND_IMP_INTRO] >>
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
    impl_tac  >- metis_tac[inhabited_range,mem_boolset] >> rw[] >>
    qexists_tac`f` >> simp[bool_to_inner_def] >>
    reverse conj_tac >- metis_tac[wf_to_inner_range_thm] >>
    match_mp_tac (UNDISCH abstract_eq) >>
    simp[boolean_in_boolset] >> rw[] >>
    simp[boolean_def] >> rw[] >>
    imp_res_tac wf_to_inner_finv_right >>
    metis_tac[mem_boolset] ) >>
  Q.ISPEC_THEN`fun_to_inner ina Boolean`mp_tac wf_to_inner_finv_left >>
  impl_tac >- metis_tac[wf_to_inner_fun_to_inner,wf_to_inner_bool_to_inner,bool_to_inner_def] >>
  simp[holds_def,GSYM bool_to_inner_def] >>
  disch_then kall_tac >>
  rw[EQ_IMP_THM] >- (
    first_x_assum(qspec_then`ina a`mp_tac) >>
    impl_tac >- metis_tac[wf_to_inner_range_thm] >>
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
    impl_tac  >- metis_tac[inhabited_range,mem_boolset] >> rw[] >>
    qexists_tac`f` >> simp[bool_to_inner_def] >>
    reverse conj_tac >- metis_tac[wf_to_inner_range_thm] >>
    match_mp_tac (UNDISCH abstract_eq) >>
    simp[boolean_in_boolset] >> rw[] >>
    simp[boolean_def] >> rw[] >>
    imp_res_tac wf_to_inner_finv_right >>
    metis_tac[mem_boolset] ) >>
  Q.ISPEC_THEN`fun_to_inner ina Boolean`mp_tac wf_to_inner_finv_left >>
  impl_tac >- metis_tac[wf_to_inner_fun_to_inner,wf_to_inner_bool_to_inner,bool_to_inner_def] >>
  simp[holds_def,GSYM bool_to_inner_def] >>
  disch_then kall_tac >>
  rw[EQ_IMP_THM] >- (
    qmatch_assum_rename_tac`z <: range ina` >>
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
  impl_tac >- metis_tac[wf_to_inner_bool_to_inner] >> rw[] >>
  AP_TERM_TAC >> AP_TERM_TAC >>
  qmatch_abbrev_tac`l = r` >>
  qsuff_tac`fun_to_inner ina bool_to_inner l = fun_to_inner ina bool_to_inner r` >- (
    `wf_to_inner (fun_to_inner ina bool_to_inner)` by metis_tac[wf_to_inner_fun_to_inner,wf_to_inner_bool_to_inner] >>
    fs[wf_to_inner_def,BIJ_DEF,INJ_DEF] ) >>
  Q.ISPEC_THEN`fun_to_inner ina bool_to_inner`mp_tac wf_to_inner_finv_right >>
  impl_tac >- metis_tac[wf_to_inner_fun_to_inner,wf_to_inner_bool_to_inner] >>
  simp[range_fun_to_inner] >> disch_then(qspec_then`x`mp_tac) >>
  impl_tac >- simp[] >>
  simp[Abbr`l`] >> disch_then kall_tac >>
  simp[Abbr`r`] >>
  Q.ISPECL_THEN[`x`,`range ina`,`range bool_to_inner`]mp_tac(UNDISCH in_funspace_abstract) >>
  impl_tac >- ( metis_tac[inhabited_range,wf_to_inner_bool_to_inner] ) >>
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
  impl_keep_tac >- (
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
  (impl_tac >- EVAL_TAC) >> rw[]) |> UNDISCH

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

val wf_to_inner_can_be_tagged = store_thm("wf_to_inner_can_be_tagged",
  ``is_set_theory ^mem ⇒
    ∀f t. wf_to_inner f ⇒ wf_to_inner (tag t o f)``,
  rw[] >>
  imp_res_tac tag_def >>
  fs[wf_to_inner_def] >>
  ntac 2 (pop_assum kall_tac) >>
  first_x_assum(qspecl_then[`x`,`t`]strip_assume_tac) >>
  qexists_tac`u` >>
  match_mp_tac BIJ_COMPOSE >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  fs[ext_def] >>
  fs[GSYM IMAGE_SURJ] >>
  simp[BIJ_DEF,INJ_DEF] >>
  fs[SURJ_DEF] >>
  metis_tac[])

val wf_to_inner_defined_type = save_thm("wf_to_inner_defined_type",
  prove(
  ``is_set_theory ^mem ⇒
    ∀abs rep.
    (∀a:α. abs ((rep a):β) = a) ⇒
    ∀tya tyb_to_inner.
    wf_to_inner (tyb_to_inner:β -> 'U) ⇒
    wf_to_inner ((to_inner tya):α -> 'U)``,
  rw[] >>
  pop_assum(fn th =>
    assume_tac th >>
    strip_assume_tac (SIMP_RULE std_ss [wf_to_inner_def] th)) >>
  pop_assum(strip_assume_tac o SIMP_RULE std_ss [BIJ_IFF_INV]) >>
  simp[to_inner_def] >>
  SELECT_ELIM_TAC >>
  conj_tac >- (
    qexists_tac`tyb_to_inner o rep` >>
    simp[wf_to_inner_def] >>
    qexists_tac`x suchthat (λb. g b = rep (abs (g b)))` >>
    simp[BIJ_IFF_INV] >> fs[] >>
    simp[mem_sub] >>
    qexists_tac`abs o g` >>
    simp[] >>
    metis_tac[] ) >>
  match_mp_tac wf_to_inner_can_be_tagged >>
  rw[]) |> UNDISCH)

val wf_to_inner_TYPE_DEFINITION = save_thm("wf_to_inner_TYPE_DEFINITION",
  prove(
  ``is_set_theory ^mem ⇒
    (∃(rep:α -> β). TYPE_DEFINITION P rep) ⇒
     ∀tya tyb_to_inner.
     wf_to_inner (tyb_to_inner:β -> 'U) ⇒
     wf_to_inner ((to_inner tya):α -> 'U)``,
  rw[]
  \\ match_mp_tac (MP_CANON wf_to_inner_defined_type)
  \\ fs[boolTheory.TYPE_DEFINITION]
  \\ qexists_tac`finv rep`
  \\ qexists_tac`rep`
  \\ qexists_tac`tyb_to_inner`
  \\ rw[finv_def]
  \\ metis_tac[]) |> UNDISCH);

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
  impl_tac >- (
    conj_tac >- ACCEPT_TAC select_theory_ok >>
    EVAL_TAC ) >>
  disch_then(qspecl_then[`select_model select`,`range ind_to_inner`]mp_tac) >>
  impl_tac >- (
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

val tmaof_hol_model_select = prove(
  ``is_set_theory ^mem ⇒ wf_to_inner ind_to_inner ⇒
    wf_to_inner a ⇒
    good_select select ⇒
    (∀p. select (range a) (Holds p) = a (@x. Holds p (a x))) ⇒
    (tmaof (hol_model select ind_to_inner) (strlit"@") [range a] =
     fun_to_inner (fun_to_inner a bool_to_inner) a $@)``,
  rw[] >> imp_res_tac hol_model_def >> fs[equal_on_def] >>
  first_x_assum(qspec_then`strlit"@"`mp_tac) >>
  impl_tac >- EVAL_TAC >>
  disch_then(SUBST1_TAC) >>
  imp_res_tac select_model_def >>
  pop_assum SUBST1_TAC >> rw[] >>
  first_assum(SUBST1_TAC o MATCH_MP fun_to_inner_select) >>
  (range_fun_to_inner_ina_bool_to_inner |> Q.DISCH`wf_to_inner ina`
   |> Q.GEN`ina` |> Q.ISPEC_THEN`a`(fn th => first_assum(SUBST1_TAC o MATCH_MP th))) >>
  SUBST1_TAC(UNDISCH range_bool_to_inner) >>
  match_mp_tac(UNDISCH abstract_eq) >>
  gen_tac >> strip_tac >>
  imp_res_tac inhabited_range >>
  simp[] >>
  metis_tac[wf_to_inner_range_thm] ) |> funpow 2 UNDISCH
val _ = save_thm("tmaof_hol_model_select",tmaof_hol_model_select)

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

val termsem_comb1_ax = store_thm("termsem_comb1_ax",
  ``is_set_theory ^mem ⇒
    ∀ctxt i v f ty tyin a ty0 a0 t x tya.
    (Const f ty0) === (Abs (Var x tya) t) ∈ axsof ctxt ∧
    theory_ok (thyof ctxt) ∧
    i models thyof ctxt ∧
    is_valuation (tysof ctxt) (tyaof i) v ∧
    FLOOKUP (tmsof ctxt) f = SOME ty0 ∧
    (ty = TYPE_SUBST tyin ty0) ∧
    EVERY (type_ok (tysof ctxt)) (MAP FST tyin) ∧
    term_ok (sigof ctxt) a0 ∧
    a0 has_type tya ∧
    (a = INST tyin a0)
    ⇒
    (termsem (tmsof ctxt) i v (Comb (Const f ty) a) =
     termsem (tmsof ctxt) i v
       (INST tyin (VSUBST [(a0,Var x tya)] t)))``,
  rpt strip_tac >>
  Q.PAT_ABBREV_TAC`s = [(a0,Var x tyia)]` >>
  `term_ok (sigof ctxt) t` by (
    fs[theory_ok_def] >> res_tac >>
    qpat_assum`is_std_sig X`assume_tac >>
    fs[term_ok_equation,term_ok_def] ) >>
  `term_ok (sigof ctxt) (VSUBST s t)` by (
    match_mp_tac term_ok_VSUBST >>
    simp[Abbr`s`] >> metis_tac[] ) >>
  simp[SIMP_RULE std_ss [] (Q.SPEC`sigof ctxt`termsem_INST)] >>
  Q.PAT_ABBREV_TAC`vvv:'U valuation = X Y` >>
  qspecl_then[`t`,`s`]mp_tac termsem_VSUBST >>
  impl_tac >- (
    simp[Abbr`s`] >> metis_tac[term_ok_welltyped] ) >>
  simp[] >> disch_then kall_tac >>
  rw[termsem_def] >>
  imp_res_tac instance_def >>
  first_x_assum(qspec_then`tyin`mp_tac) >>
  simp[] >> disch_then kall_tac >>
  qmatch_assum_abbrev_tac`MEM eq axs` >>
  `i satisfies (sigof ctxt,[],eq)` by (
    fs[models_def] ) >>
  Q.PAT_ABBREV_TAC`vv:'U valuation = X Y` >>
  `is_valuation (tysof ctxt) (tyaof i) vvv` by (
    simp[Abbr`vvv`] >>
    fs[is_valuation_def,is_type_valuation_def,is_term_valuation_def] >>
    conj_tac >- (
      gen_tac >>
      match_mp_tac(UNDISCH typesem_inhabited) >>
      qexists_tac`tysof ctxt` >>
      simp[is_type_valuation_def] >>
      fs[models_def,is_interpretation_def] >>
      simp[holSyntaxLibTheory.REV_ASSOCD_ALOOKUP] >>
      BasicProvers.CASE_TAC >> simp[type_ok_def] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[EVERY_MEM,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
      metis_tac[] ) >>
    qx_genl_tac[`z`,`ty`] >> strip_tac >>
    first_x_assum(qspecl_then[`z`,`TYPE_SUBST tyin ty`]mp_tac) >>
    simp[type_ok_TYPE_SUBST,Once typesem_TYPE_SUBST] ) >>
  `is_valuation (tysof ctxt) (tyaof i) vv` by (
    simp[Abbr`vv`,Abbr`s`,miscTheory.UPDATE_LIST_THM] >>
    match_mp_tac is_valuation_extend >>
    reverse conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem_matchable) >> simp[] >>
      qexists_tac`sigof ctxt` >> simp[] >>
      fs[models_def,is_std_interpretation_def] >>
      metis_tac[WELLTYPED_LEMMA] ) >>
    simp[]) >>
  `termsem (tmsof ctxt) i vv eq = True` by (
    fs[satisfies_def] ) >>
  qmatch_assum_abbrev_tac`Abbrev(eq = l === r)` >>
  qspecl_then[`sigof ctxt`,`i`,`vv`,`l`,`r`]mp_tac (UNDISCH termsem_equation) >>
  simp[] >> impl_keep_tac >- (
    fs[theory_ok_def] >>
    fs[is_structure_def,models_def] ) >>
  simp[boolean_eq_true,Abbr`l`,termsem_def] >>
  simp[identity_instance] >>
  Q.PAT_ABBREV_TAC`tv:'U tyval = (typesem A X o Y o Tyvar)` >>
  `tv = tyvof vv` by (
    unabbrev_all_tac >> simp[FUN_EQ_THM] ) >>
  qunabbrev_tac`tv`>>simp[] >> disch_then kall_tac >>
  pop_assum kall_tac >>
  simp[Abbr`r`,termsem_def] >>
  `is_std_type_assignment (tyaof i)` by (
    fs[models_def,is_std_interpretation_def] ) >>
  imp_res_tac typesem_Fun >> simp[] >>
  pop_assum kall_tac >>
  match_mp_tac apply_abstract_matchable >>
  simp[SIMP_RULE std_ss [] (Q.SPEC`sigof ctxt`termsem_INST)] >>
  Q.PAT_ABBREV_TAC`vv':'U valuation = X Y` >>
  `vv' = vv` by (
    simp[Abbr`vv`,Abbr`vv'`,Abbr`s`,UPDATE_LIST_THM] >>
    simp[FUN_EQ_THM,combinTheory.APPLY_UPDATE_THM] ) >>
  simp[] >>
  conj_tac >- (
    match_mp_tac (UNDISCH termsem_typesem_matchable) >> simp[] >>
    qexists_tac`sigof ctxt` >> simp[Abbr`vv`] >>
    fs[models_def] >> metis_tac[WELLTYPED_LEMMA] ) >>
  match_mp_tac (UNDISCH termsem_typesem) >>
  qexists_tac`sigof ctxt` >> simp[] >>
  fs[models_def])

val termsem_comb2_ax = store_thm("termsem_comb2_ax",
  ``is_set_theory ^mem ⇒
    ∀ctxt i v f ty tyin a b ty0 a0 b0 t x y tya tyb.
    (Const f ty0) === (Abs (Var x tya) (Abs (Var y tyb) t)) ∈ axsof ctxt ∧
    theory_ok (thyof ctxt) ∧
    i models thyof ctxt ∧
    is_valuation (tysof ctxt) (tyaof i) v ∧
    FLOOKUP (tmsof ctxt) f = SOME ty0 ∧
    (ty = TYPE_SUBST tyin ty0) ∧
    EVERY (type_ok (tysof ctxt)) (MAP FST tyin) ∧
    term_ok (sigof ctxt) a0 ∧ term_ok (sigof ctxt) b0 ∧
    a0 has_type tya ∧ b0 has_type tyb ∧
    (a = INST tyin a0) ∧ (b = INST tyin b0) ∧ x ≠ y
    ⇒
    (termsem (tmsof ctxt) i v (Comb (Comb (Const f ty) a) b) =
     termsem (tmsof ctxt) i v
       (INST tyin (VSUBST [(a0,Var x tya);(b0,Var y tyb)] t)))``,
  rpt strip_tac >>
  Q.PAT_ABBREV_TAC`s = [(a0,Var x tyia);Y]` >>
  `term_ok (sigof ctxt) t` by (
    fs[theory_ok_def] >> res_tac >>
    qpat_assum`is_std_sig X`assume_tac >>
    fs[term_ok_equation,term_ok_def] ) >>
  `term_ok (sigof ctxt) (VSUBST s t)` by (
    match_mp_tac term_ok_VSUBST >>
    simp[Abbr`s`] >> metis_tac[] ) >>
  simp[SIMP_RULE std_ss [] (Q.SPEC`sigof ctxt`termsem_INST)] >>
  Q.PAT_ABBREV_TAC`vvv:'U valuation = X Y` >>
  qspecl_then[`t`,`s`]mp_tac termsem_VSUBST >>
  impl_tac >- (
    simp[Abbr`s`] >> metis_tac[term_ok_welltyped] ) >>
  simp[] >> disch_then kall_tac >>
  rw[termsem_def] >>
  imp_res_tac instance_def >>
  first_x_assum(qspec_then`tyin`mp_tac) >>
  simp[] >> disch_then kall_tac >>
  qmatch_assum_abbrev_tac`MEM eq axs` >>
  `i satisfies (sigof ctxt,[],eq)` by (
    fs[models_def] ) >>
  Q.PAT_ABBREV_TAC`vv:'U valuation = X Y` >>
  `is_valuation (tysof ctxt) (tyaof i) vvv` by (
    simp[Abbr`vvv`] >>
    fs[is_valuation_def,is_type_valuation_def,is_term_valuation_def] >>
    conj_tac >- (
      gen_tac >>
      match_mp_tac(UNDISCH typesem_inhabited) >>
      qexists_tac`tysof ctxt` >>
      simp[is_type_valuation_def] >>
      fs[models_def,is_interpretation_def] >>
      simp[holSyntaxLibTheory.REV_ASSOCD_ALOOKUP] >>
      BasicProvers.CASE_TAC >> simp[type_ok_def] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[EVERY_MEM,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
      metis_tac[] ) >>
    qx_genl_tac[`z`,`ty`] >> strip_tac >>
    first_x_assum(qspecl_then[`z`,`TYPE_SUBST tyin ty`]mp_tac) >>
    simp[type_ok_TYPE_SUBST,Once typesem_TYPE_SUBST] ) >>
  `is_valuation (tysof ctxt) (tyaof i) vv` by (
    simp[Abbr`vv`,Abbr`s`,miscTheory.UPDATE_LIST_THM] >>
    match_mp_tac is_valuation_extend >>
    reverse conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem_matchable) >> simp[] >>
      qexists_tac`sigof ctxt` >> simp[] >>
      fs[models_def,is_std_interpretation_def] >>
      metis_tac[WELLTYPED_LEMMA] ) >>
    match_mp_tac is_valuation_extend >> simp[] >>
    match_mp_tac (UNDISCH termsem_typesem_matchable) >> simp[] >>
    qexists_tac`sigof ctxt` >> simp[] >>
    fs[models_def,is_std_interpretation_def] >>
    metis_tac[WELLTYPED_LEMMA] ) >>
  `termsem (tmsof ctxt) i vv eq = True` by (
    fs[satisfies_def] ) >>
  qmatch_assum_abbrev_tac`Abbrev(eq = l === r)` >>
  qspecl_then[`sigof ctxt`,`i`,`vv`,`l`,`r`]mp_tac (UNDISCH termsem_equation) >>
  simp[] >> impl_keep_tac >- (
    fs[theory_ok_def] >>
    fs[is_structure_def,models_def] ) >>
  simp[boolean_eq_true,Abbr`l`,termsem_def] >>
  simp[identity_instance] >>
  Q.PAT_ABBREV_TAC`tv:'U tyval = (typesem A X o Y o Tyvar)` >>
  `tv = tyvof vv` by (
    unabbrev_all_tac >> simp[FUN_EQ_THM] ) >>
  qunabbrev_tac`tv`>>simp[] >> disch_then kall_tac >>
  pop_assum kall_tac >>
  simp[Abbr`r`,termsem_def] >>
  `is_std_type_assignment (tyaof i)` by (
    fs[models_def,is_std_interpretation_def] ) >>
  imp_res_tac typesem_Fun >> simp[] >>
  pop_assum kall_tac >>
  qmatch_abbrev_tac`Abstract aa fs ff ' ma ' mb = zz` >>
  `ma <: aa` by (
    simp[Abbr`ma`,Abbr`aa`] >>
    simp[SIMP_RULE std_ss [] (Q.SPEC`sigof ctxt`termsem_INST)] >>
    `tya = typeof a0` by metis_tac[WELLTYPED_LEMMA] >> rw[] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    qexists_tac`sigof ctxt` >> simp[] >>
    fs[Abbr`vv`,models_def] ) >>
  qmatch_assum_abbrev_tac`Abbrev(fs = Funspace bb tt)` >>
  `mb <: bb` by (
    simp[Abbr`mb`,Abbr`bb`] >>
    simp[SIMP_RULE std_ss [] (Q.SPEC`sigof ctxt`termsem_INST)] >>
    `tyb = typeof b0` by metis_tac[WELLTYPED_LEMMA] >> rw[] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    qexists_tac`sigof ctxt` >> simp[] >>
    fs[Abbr`vv`,models_def] ) >>
  `Abstract aa fs ff ' ma = ff ma` by (
    match_mp_tac apply_abstract_matchable >> simp[] >>
    simp[Abbr`ff`,Abbr`fs`] >>
    match_mp_tac(UNDISCH abstract_in_funspace) >>
    simp[Abbr`tt`] >> rw[] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    qexists_tac`sigof ctxt` >> simp[] >>
    fs[models_def] >>
    match_mp_tac is_valuation_extend >> simp[] >>
    match_mp_tac is_valuation_extend >> simp[] ) >>
  pop_assum SUBST1_TAC >>
  simp[Abbr`ff`] >>
  match_mp_tac apply_abstract_matchable >>
  simp[Abbr`zz`] >>
  Q.PAT_ABBREV_TAC`vv':'U valuation = X Y` >>
  `vv' = vv` by (
    simp[Abbr`vv`,Abbr`vv'`,Abbr`s`,UPDATE_LIST_THM,Abbr`ma`,Abbr`mb`] >>
    simp[SIMP_RULE std_ss [] (Q.SPEC`sigof ctxt`termsem_INST)] >>
    simp[FUN_EQ_THM,combinTheory.APPLY_UPDATE_THM] >>
    rw[] ) >>
  simp[] >>
  simp[Abbr`tt`] >>
  match_mp_tac (UNDISCH termsem_typesem) >>
  qexists_tac`sigof ctxt` >> simp[] >>
  fs[models_def])

val termsem_comb3_ax = store_thm("termsem_comb3_ax",
  ``is_set_theory ^mem ⇒
    ∀ctxt i v f ty tyin a b c ty0 a0 b0 c0 t x y z tya tyb tyc.
    (Const f ty0) === (Abs (Var x tya) (Abs (Var y tyb) (Abs (Var z tyc) t))) ∈ axsof ctxt ∧
    theory_ok (thyof ctxt) ∧
    i models thyof ctxt ∧
    is_valuation (tysof ctxt) (tyaof i) v ∧
    FLOOKUP (tmsof ctxt) f = SOME ty0 ∧
    (ty = TYPE_SUBST tyin ty0) ∧
    EVERY (type_ok (tysof ctxt)) (MAP FST tyin) ∧
    term_ok (sigof ctxt) a0 ∧ term_ok (sigof ctxt) b0 ∧ term_ok (sigof ctxt) c0 ∧
    a0 has_type tya ∧ b0 has_type tyb ∧ c0 has_type tyc ∧
    (a = INST tyin a0) ∧ (b = INST tyin b0) ∧ (c = INST tyin c0) ∧ ALL_DISTINCT [x;y;z]
    ⇒
    (termsem (tmsof ctxt) i v (Comb (Comb (Comb (Const f ty) a) b) c) =
     termsem (tmsof ctxt) i v
       (INST tyin (VSUBST [(a0,Var x tya);(b0,Var y tyb);(c0,Var z tyc)] t)))``,
  rpt strip_tac >>
  Q.PAT_ABBREV_TAC`s = (a0,Var x tyia)::Y	` >>
  `term_ok (sigof ctxt) t` by (
    fs[theory_ok_def] >> res_tac >>
    qpat_assum`is_std_sig X`assume_tac >>
    fs[term_ok_equation,term_ok_def] ) >>
  `term_ok (sigof ctxt) (VSUBST s t)` by (
    match_mp_tac term_ok_VSUBST >>
    simp[Abbr`s`] >> metis_tac[] ) >>
  simp[SIMP_RULE std_ss [] (Q.SPEC`sigof ctxt`termsem_INST)] >>
  Q.PAT_ABBREV_TAC`vvv:'U valuation = X Y` >>
  qspecl_then[`t`,`s`]mp_tac termsem_VSUBST >>
  impl_tac >- (
    simp[Abbr`s`] >> metis_tac[term_ok_welltyped] ) >>
  simp[] >> disch_then kall_tac >>
  rw[termsem_def] >>
  imp_res_tac instance_def >>
  first_x_assum(qspec_then`tyin`mp_tac) >>
  simp[] >> disch_then kall_tac >>
  qmatch_assum_abbrev_tac`MEM eq axs` >>
  `i satisfies (sigof ctxt,[],eq)` by (
    fs[models_def] ) >>
  Q.PAT_ABBREV_TAC`vv:'U valuation = X Y` >>
  `is_valuation (tysof ctxt) (tyaof i) vvv` by (
    simp[Abbr`vvv`] >>
    fs[is_valuation_def,is_type_valuation_def,is_term_valuation_def] >>
    conj_tac >- (
      gen_tac >>
      match_mp_tac(UNDISCH typesem_inhabited) >>
      qexists_tac`tysof ctxt` >>
      simp[is_type_valuation_def] >>
      fs[models_def,is_interpretation_def] >>
      simp[holSyntaxLibTheory.REV_ASSOCD_ALOOKUP] >>
      BasicProvers.CASE_TAC >> simp[type_ok_def] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[EVERY_MEM,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
      metis_tac[] ) >>
    qx_genl_tac[`z`,`ty`] >> strip_tac >>
    first_x_assum(qspecl_then[`z`,`TYPE_SUBST tyin ty`]mp_tac) >>
    simp[type_ok_TYPE_SUBST,Once typesem_TYPE_SUBST] ) >>
  `is_valuation (tysof ctxt) (tyaof i) vv` by (
    simp[Abbr`vv`,Abbr`s`,miscTheory.UPDATE_LIST_THM] >>
    match_mp_tac is_valuation_extend >>
    reverse conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem_matchable) >> simp[] >>
      qexists_tac`sigof ctxt` >> simp[] >>
      fs[models_def,is_std_interpretation_def] >>
      metis_tac[WELLTYPED_LEMMA] ) >>
    match_mp_tac is_valuation_extend >>
    reverse conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem_matchable) >> simp[] >>
      qexists_tac`sigof ctxt` >> simp[] >>
      fs[models_def,is_std_interpretation_def] >>
      metis_tac[WELLTYPED_LEMMA] ) >>
    match_mp_tac is_valuation_extend >> simp[] >>
    match_mp_tac (UNDISCH termsem_typesem_matchable) >> simp[] >>
    qexists_tac`sigof ctxt` >> simp[] >>
    fs[models_def,is_std_interpretation_def] >>
    metis_tac[WELLTYPED_LEMMA] ) >>
  `termsem (tmsof ctxt) i vv eq = True` by (
    fs[satisfies_def] ) >>
  qmatch_assum_abbrev_tac`Abbrev(eq = l === r)` >>
  qspecl_then[`sigof ctxt`,`i`,`vv`,`l`,`r`]mp_tac (UNDISCH termsem_equation) >>
  simp[] >> impl_keep_tac >- (
    fs[theory_ok_def] >>
    fs[is_structure_def,models_def] ) >>
  simp[boolean_eq_true,Abbr`l`,termsem_def] >>
  simp[identity_instance] >>
  Q.PAT_ABBREV_TAC`tv:'U tyval = (typesem A X o Y o Tyvar)` >>
  `tv = tyvof vv` by (
    unabbrev_all_tac >> simp[FUN_EQ_THM] ) >>
  qunabbrev_tac`tv`>>simp[] >> disch_then kall_tac >>
  pop_assum kall_tac >>
  simp[Abbr`r`,termsem_def] >>
  `is_std_type_assignment (tyaof i)` by (
    fs[models_def,is_std_interpretation_def] ) >>
  imp_res_tac typesem_Fun >> simp[] >>
  pop_assum kall_tac >>
  qmatch_abbrev_tac`Abstract aa fs ff ' ma ' mb ' mc = zz` >>
  `ma <: aa` by (
    simp[Abbr`ma`,Abbr`aa`] >>
    simp[SIMP_RULE std_ss [] (Q.SPEC`sigof ctxt`termsem_INST)] >>
    `tya = typeof a0` by metis_tac[WELLTYPED_LEMMA] >> rw[] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    qexists_tac`sigof ctxt` >> simp[] >>
    fs[Abbr`vv`,models_def] ) >>
  qmatch_assum_abbrev_tac`Abbrev(fs = Funspace bb tt)` >>
  `mb <: bb` by (
    simp[Abbr`mb`,Abbr`bb`] >>
    simp[SIMP_RULE std_ss [] (Q.SPEC`sigof ctxt`termsem_INST)] >>
    `tyb = typeof b0` by metis_tac[WELLTYPED_LEMMA] >> rw[] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    qexists_tac`sigof ctxt` >> simp[] >>
    fs[Abbr`vv`,models_def] ) >>
  qmatch_assum_abbrev_tac`Abbrev(tt = Funspace cc uu)` >>
  `mc <: cc` by (
    simp[Abbr`mc`,Abbr`cc`] >>
    simp[SIMP_RULE std_ss [] (Q.SPEC`sigof ctxt`termsem_INST)] >>
    `tyc = typeof c0` by metis_tac[WELLTYPED_LEMMA] >> rw[] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    qexists_tac`sigof ctxt` >> simp[] >>
    fs[Abbr`vv`,models_def] ) >>
  `Abstract aa fs ff ' ma = ff ma` by (
    match_mp_tac apply_abstract_matchable >> simp[] >>
    simp[Abbr`ff`,Abbr`fs`] >>
    match_mp_tac(UNDISCH abstract_in_funspace) >>
    simp[Abbr`tt`] >> rw[] >>
    match_mp_tac(UNDISCH abstract_in_funspace) >>
    simp[Abbr`uu`] >> rw[] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    qexists_tac`sigof ctxt` >> simp[] >>
    fs[models_def] >>
    match_mp_tac is_valuation_extend >> simp[] >>
    match_mp_tac is_valuation_extend >> simp[] >>
    match_mp_tac is_valuation_extend >> simp[]) >>
  pop_assum SUBST1_TAC >>
  simp[Abbr`ff`] >>
  qmatch_abbrev_tac`Abstract bb tt ff ' mb ' mc = zz` >>
  `Abstract bb tt ff ' mb = ff mb` by (
    match_mp_tac apply_abstract_matchable >> simp[] >>
    simp[Abbr`ff`,Abbr`tt`] >>
    match_mp_tac(UNDISCH abstract_in_funspace) >>
    simp[Abbr`uu`] >> rw[] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    qexists_tac`sigof ctxt` >> simp[] >>
    fs[models_def] >>
    match_mp_tac is_valuation_extend >> simp[] >>
    match_mp_tac is_valuation_extend >> simp[] >>
    match_mp_tac is_valuation_extend >> simp[]) >>
  pop_assum SUBST1_TAC >>
  simp[Abbr`ff`] >>
  match_mp_tac apply_abstract_matchable >>
  simp[Abbr`zz`] >>
  Q.PAT_ABBREV_TAC`vv':'U valuation = X Y` >>
  `vv' = vv` by (
    simp[Abbr`vv`,Abbr`vv'`,Abbr`s`,UPDATE_LIST_THM,Abbr`ma`,Abbr`mb`,Abbr`mc`] >>
    simp[SIMP_RULE std_ss [] (Q.SPEC`sigof ctxt`termsem_INST)] >>
    simp[FUN_EQ_THM,combinTheory.APPLY_UPDATE_THM] >> fs[] >> rw[] ) >>
  simp[] >>
  simp[Abbr`uu`] >>
  match_mp_tac (UNDISCH termsem_typesem) >>
  qexists_tac`sigof ctxt` >> simp[] >>
  fs[models_def])

val good_context_base_case = prove(
  ``is_set_theory ^mem
    ⇒ wf_to_inner ind_to_inner
    ⇒ good_select select
    ⇒
    good_context mem (sigof hol_ctxt) (hol_model select ind_to_inner)
      (* (base_valuation (tysof hol_ctxt) (tyaof (hol_model select ind_to_inner))) *)``,
    ntac 3 strip_tac >>
    simp[good_context_unpaired] >>
    conj_tac >- (
      mp_tac(MATCH_MP theory_ok_sig theory_ok_hol_ctxt) >>
      simp[] ) >>
    conj_asm1_tac >- (
      imp_res_tac hol_model_def >>
      fs[models_def]) >>
    (* conj_tac >- ( *)
      imp_res_tac hol_model_def >>
      fs[models_def] (* ) >>
    match_mp_tac base_valuation_def >>
    fs[is_interpretation_def]*)) |> funpow 2 UNDISCH
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

val is_type_valuation_base = prove(
  ``is_set_theory ^mem ⇒ is_type_valuation (K boolset)``,
  rw[is_type_valuation_def] >> metis_tac[mem_boolset])
  |> UNDISCH
  |> curry save_thm "is_type_valuation_base"

val a_valuation_def = new_specification("a_valuation_def",["a_valuation0"],
  prove(``∃v.
          ∀mem tyenv δ τ.
          is_set_theory ^mem ⇒
          is_type_assignment tyenv δ ⇒
          is_type_valuation τ ⇒
          is_valuation tyenv δ (v mem tyenv δ τ) ∧
          (tyvof (v mem tyenv δ τ) = τ)``,
    rw[GSYM SKOLEM_THM] >>
    rw[RIGHT_EXISTS_IMP_THM] >>
    imp_res_tac (UNDISCH term_valuation_exists) >>
    first_assum(match_exists_tac o concl) >> simp[]))
val _ = overload_on("a_valuation",``a_valuation0 ^mem``)

val good_context_is_type_assignment = store_thm("good_context_is_type_assignment",
  ``good_context mem s i ⇒ is_type_assignment (tysof s) (tyaof i)``,
  rw[good_context_unpaired,is_interpretation_def])

val is_std_interpretation_equal_on = store_thm("is_std_interpretation_equal_on",
  ``is_std_interpretation i ∧ equal_on sig i i' ∧ is_std_sig sig ⇒
    is_std_interpretation i'``,
  rw[is_std_interpretation_def] >- (
    fs[is_std_type_assignment_def,equal_on_def,is_std_sig_def,finite_mapTheory.FLOOKUP_DEF] ) >>
  fs[interprets_def,equal_on_def,is_std_sig_def,finite_mapTheory.FLOOKUP_DEF])

val good_context_extend = store_thm("good_context_extend",
  ``∀mem upd ctxt i.
    good_context mem (sigof ctxt) i ∧
    upd updates ctxt ∧ sound_update ctxt upd ∧
    i models thyof ctxt
    ⇒
    good_context mem (sigof (upd::ctxt)) (update_interpretation ctxt upd i)
      (* (update_valuation ctxt upd (tyaof i) (tyaof (update_interpretation ctxt upd i)) v)*)``,
  rpt gen_tac >>
  PairCases_on`i` >>
  (* PairCases_on`v` >> *)
  rw[good_context_def] >>
  imp_res_tac update_interpretation_def >>
  (* Q.PAT_ABBREV_TAC`δ = tyaof (update_interpretation X Y Z)` >> *)
  (* qspecl_then[`ctxt`,`upd`,`i0`,`δ`,`v0,v1`]mp_tac update_valuation_def >> *)
  simp[] >>
  (*
  impl_tac >- (
    conj_tac >- ( fs[equal_on_def] ) >>
    fs[models_def,is_interpretation_def] ) >>
  *)
  rw[] >>
  qmatch_abbrev_tac`good_context mem sig2 i2` >>
  `∃i3 i4. i2 = (i3,i4) (*∧ ∃v3 v4. v2 = (v3,v4)*)` by metis_tac[pair_CASES] >>
  simp[good_context_def,Abbr`sig2`] >>
  fs[Abbr`i2`(*,Abbr`v2`,Abbr`δ`*)] >>
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

val ConstSpec_updates_welltyped = store_thm("ConstSpec_updates_welltyped",
  ``ConstSpec eqs prop updates ctxt ⇒ welltyped prop``,
  rw[updates_cases] >>
  imp_res_tac proves_term_ok >> fs[welltyped_def] >>
  PROVE_TAC[])

(*
val IN_FDOM_implies_type_ok = store_thm("IN_FDOM_implies_type_ok",
  ``name ∈ FDOM tysig ⇒ ∃args. type_ok tysig (Tyapp name args)``,
  rw[type_ok_def,finite_mapTheory.FLOOKUP_DEF] >>
  qexists_tac`GENLIST (K (Tyvar ARB)) (tysig ' name)` >>
  rw[listTheory.EVERY_MEM,listTheory.MEM_GENLIST] >>
  rw[type_ok_def])
*)

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
  equality_thm0
  |> Q.SPEC`range ina`
  |> C MATCH_MP (UNDISCH (Q.SPEC`ina` inhabited_range))
  |> CONV_RULE (RAND_CONV (REWR_CONV (SYM fun_to_inner_equals)))
val truth_thm =
  truth_thm0
  |> CONV_RULE(REWR_CONV is_true_interpretation_def)
  |> CONV_RULE(REWR_CONV interprets_nil)
  |> REWRITE_RULE[combinTheory.K_THM]
  |> CONV_RULE(RAND_CONV(REWR_CONV(SYM bool_to_inner_true)))
val and_thm =
  and_thm0
  |> CONV_RULE(REWR_CONV is_and_interpretation_def)
  |> CONV_RULE(REWR_CONV interprets_nil)
  |> REWRITE_RULE[Boolrel_def,combinTheory.K_THM]
  |> CONV_RULE(RAND_CONV(REWR_CONV(SYM fun_to_inner_binop)))
val implies_thm =
  implies_thm0
  |> CONV_RULE(REWR_CONV is_implies_interpretation_def)
  |> CONV_RULE(REWR_CONV interprets_nil)
  |> REWRITE_RULE[Boolrel_def,combinTheory.K_THM]
  |> CONV_RULE(RAND_CONV(REWR_CONV(SYM fun_to_inner_binop)))
val forall_thm =
  forall_thm0
  |> CONV_RULE(REWR_CONV is_forall_interpretation_def)
  |> CONV_RULE(REWR_CONV interprets_one)
  |> Q.SPEC`range ina`
  |> C MATCH_MP (UNDISCH (Q.SPEC`ina` inhabited_range))
  |> CONV_RULE (RAND_CONV BETA_CONV) |> REWRITE_RULE[HD]
  |> CONV_RULE (RAND_CONV (REWR_CONV (SYM fun_to_inner_forall)))
val exists_thm =
  exists_thm0
  |> CONV_RULE(REWR_CONV is_exists_interpretation_def)
  |> CONV_RULE(REWR_CONV interprets_one)
  |> Q.SPEC`range ina`
  |> C MATCH_MP (UNDISCH (Q.SPEC`ina` inhabited_range))
  |> CONV_RULE (RAND_CONV BETA_CONV) |> REWRITE_RULE[HD]
  |> CONV_RULE (RAND_CONV (REWR_CONV (SYM fun_to_inner_exists)))
val or_thm =
  or_thm0
  |> CONV_RULE(REWR_CONV is_or_interpretation_def)
  |> CONV_RULE(REWR_CONV interprets_nil)
  |> REWRITE_RULE[Boolrel_def,combinTheory.K_THM]
  |> CONV_RULE(RAND_CONV(REWR_CONV(SYM fun_to_inner_binop)))
val falsity_thm =
  falsity_thm0
  |> CONV_RULE(REWR_CONV is_false_interpretation_def)
  |> CONV_RULE(REWR_CONV interprets_nil)
  |> REWRITE_RULE[combinTheory.K_THM]
  |> CONV_RULE(RAND_CONV(REWR_CONV(SYM bool_to_inner_false)))
val not_thm =
  not_thm0
  |> CONV_RULE(REWR_CONV is_not_interpretation_def)
  |> CONV_RULE(REWR_CONV interprets_nil)
  |> REWRITE_RULE[combinTheory.K_THM]
  |> CONV_RULE(RAND_CONV(REWR_CONV(SYM fun_to_inner_not)))

val _ = map2 (curry save_thm)
  ["equality_thm","truth_thm","and_thm","implies_thm","forall_thm","exists_thm","or_thm","falsity_thm","not_thm"]
  [ equality_thm , truth_thm , and_thm , implies_thm , forall_thm , exists_thm , or_thm , falsity_thm , not_thm ]

val hol_of_sigof = prove(``tmsof (sigof hol_ctxt) = tmsof hol_ctxt``,rw[])

val (EVAL_type_ok0,EVAL_term_ok0) =
  holSyntaxLib.EVAL_type_ok_term_ok
    EVAL (MATCH_MP theory_ok_sig theory_ok_hol_ctxt |> SIMP_RULE std_ss[])
val th = prove(``tysof hol_ctxt = tysof(sigof hol_ctxt)``,rw[])
val EVAL_type_ok =
  (RATOR_CONV(RAND_CONV(REWR_CONV th))) THENC EVAL_type_ok0
val EVAL_term_ok =
  EVAL_term_ok0 THENC
  SIMP_CONV (srw_ss()) [
    holSyntaxLibTheory.tyvar_inst_exists,
    tyvar_inst_exists2,
    tyvar_inst_exists2_diff]

val hol_is_bool_sig = store_thm("hol_is_bool_sig",
  ``is_bool_sig (sigof hol_ctxt)``,
  match_mp_tac (MP_CANON is_bool_sig_extends) >>
  match_exists_tac(concl hol_extends_bool) >>
  simp[hol_extends_bool] >>
  match_mp_tac bool_has_bool_sig >>
  ACCEPT_TAC (MATCH_MP theory_ok_sig init_theory_ok |> SIMP_RULE std_ss[]))

val hol_is_std_sig = Q.store_thm("hol_is_std_sig",
  `is_std_sig (sigof hol_ctxt)`,
  metis_tac[hol_is_bool_sig,is_bool_sig_std]);

fun use_termsem_equation (g as (asl,w)) =
  let
    val tm = find_term(can(match_term``termsem s i v (a === b)``)) w
    val (_,args) = strip_comb tm
    val eq = el 5 args
    val p1 = eq |> rator |> rand
    val p2 = eq |> rand
    val s = el 2 args |> REWR_CONV(SYM hol_of_sigof) |> concl |> rhs |> rand
    val th =
      UNDISCH termsem_equation
      |> SPECL[s, el 3 args, el 4 args, p1, p2, el 2 args]
      |> CONV_RULE(DEPTH_CONV(REWR_CONV hol_of_sigof))
  in
    mp_tac th >>
    impl_tac >- (
      conj_tac >- (
        simp[is_structure_def] >>
        fs[models_def] >>
        assume_tac theory_ok_hol_ctxt >>
        imp_res_tac theory_ok_sig >>
        fs[] ) >>
      conj_tac >- (
        simp[equation_def] >>
        CONV_TAC EVAL_term_ok ) >>
      REFL_TAC ) >>
    disch_then(CHANGED_TAC o SUBST1_TAC)
  end g

(*
val (g as (asl,w)) = top_goal()
*)

fun use_termsem_forall (g as (asl,w)) =
  let
    val tm = find_term(can(match_term``termsem s i v (Forall x y z)``)) w
    val (_,args) = strip_comb tm
    val eq = el 5 args
    val p1 = eq |> rand |> rator |> rand |> rator |> rand
    val p2 = eq |> rand |> rator |> rand |> rand
    val p3 = eq |> rand |> rand
    val s = el 2 args |> REWR_CONV(SYM hol_of_sigof) |> concl |> rhs |> rand
    val th =
      UNDISCH termsem_forall
      |> SPECL[s, el 3 args, el 4 args, p1, p2, p3]
      |> CONV_RULE(DEPTH_CONV(REWR_CONV hol_of_sigof))
  in
    mp_tac th >>
    impl_tac >- (
      conj_tac >- simp[] >>
      conj_tac >- fs[models_def] >>
      conj_tac >- fs[models_def] >>
      conj_tac >- (CONV_TAC EVAL_type_ok0) >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      conj_tac >- (CONV_TAC(LAND_CONV holSyntaxLib.EVAL_typeof) >> REFL_TAC) >>
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
    val s = el 2 args |> REWR_CONV(SYM hol_of_sigof) |> concl |> rhs |> rand
    val th =
      UNDISCH termsem_exists
      |> SPECL[s, el 3 args, el 4 args, p1, p2, p3]
      |> CONV_RULE(DEPTH_CONV(REWR_CONV hol_of_sigof))
  in
    mp_tac th >>
    impl_tac >- (
      conj_tac >- simp[] >>
      conj_tac >- fs[models_def] >>
      conj_tac >- fs[models_def] >>
      conj_tac >- (CONV_TAC EVAL_type_ok0) >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      conj_tac >- (CONV_TAC(LAND_CONV holSyntaxLib.EVAL_typeof) >> REFL_TAC) >>
      fs[is_bool_interpretation_def,is_bool_sig_def]) >>
    disch_then(CHANGED_TAC o SUBST1_TAC)
  end g

fun use_termsem_implies (g as (asl,w)) =
  let
    val tm = find_term(can(match_term``termsem s i v (Implies a b)``)) w
    val (_,args) = strip_comb tm
    val imp = el 5 args
    val p1 = imp |> rator |> rand |> rand
    val p2 = imp |> rand
    val s = el 2 args |> REWR_CONV(SYM hol_of_sigof) |> concl |> rhs |> rand
    val th =
      UNDISCH termsem_implies
      |> SPECL[s, el 3 args, el 4 args, p1, p2]
      |> CONV_RULE(DEPTH_CONV(REWR_CONV hol_of_sigof))
  in
    mp_tac th >>
    impl_tac >- (
      conj_tac >- simp[] >>
      conj_tac >- fs[models_def] >>
      conj_tac >- fs[models_def,is_std_interpretation_def] >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      conj_tac >- (CONV_TAC EVAL_term_ok) >>
      conj_tac >- (CONV_TAC (LAND_CONV holSyntaxLib.EVAL_typeof) >> REFL_TAC) >>
      conj_tac >- (CONV_TAC (LAND_CONV holSyntaxLib.EVAL_typeof) >> REFL_TAC) >>
      fs[is_bool_interpretation_def,is_bool_sig_def] ) >>
    disch_then (CHANGED_TAC o SUBST1_TAC)
  end g

fun use_apply_abstract (g as (asl,w)) =
  let
    val sel = lhs o snd o dest_imp
    val tm = find_term(can(match_term(sel(concl(SPEC_ALL apply_abstract_matchable))))) w
  in
    mp_tac(Q.GEN`u`(PART_MATCH sel apply_abstract_matchable tm))
  end g

val one_one_thm = prove(
  ``is_set_theory ^mem ⇒
    good_select select ⇒
    wf_to_inner ind_to_inner ⇒
    wf_to_inner ina ⇒
    wf_to_inner inb ⇒
    tmaof (hol_model select ind_to_inner) (strlit "ONE_ONE") [range ina; range inb] =
    fun_to_inner (fun_to_inner ina inb) bool_to_inner ONE_ONE``,
  rw[] >>
  mp_tac hol_model_models >>
  simp[models_def] >> strip_tac >>
  first_x_assum(mp_tac o SPEC (term_to_deep (concl ONE_ONE_DEF))) >>
  impl_tac >- EVAL_TAC >>
  simp[equation_intro] >>
  simp[satisfies_def] >>
  Q.PAT_ABBREV_TAC`i = hol_model X Y` >>
  Q.PAT_ABBREV_TAC`tm = X === Y` >>
  qabbrev_tac`τ = λx. if x = strlit"A" then range ina else range inb` >>
  `is_type_valuation τ` by (
    simp[Abbr`τ`,is_type_valuation_def] >> rw[] >>
    metis_tac[inhabited_range] ) >>
  qspecl_then[`tysof hol_ctxt`,`tyaof i`,`τ`]mp_tac (UNDISCH term_valuation_exists) >>
  impl_tac >- fs[is_interpretation_def] >> strip_tac >>
  disch_then(qspec_then`τ,σ`mp_tac) >>
  impl_tac >- fs[] >>
  qunabbrev_tac`tm` >>
  use_termsem_equation >>
  simp[boolean_eq_true] >>
  simp[Once termsem_def] >>
  qspecl_then[`tmsof hol_ctxt`,`i`,`strlit"ONE_ONE"`]mp_tac identity_instance >>
  CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV EVAL))) >>
  simp[] >>
  EVAL_STRING_SORT >>
  disch_then kall_tac >>
  simp[listTheory.MAP_MAP_o,mlstringTheory.implode_def] >>
  `τ(strlit"A") = range ina ∧ τ(strlit"B") = range inb` by (
    simp[Abbr`τ`] ) >> simp[] >>
  disch_then kall_tac >>
  simp[Once termsem_def,Once fun_to_inner_def,range_fun_to_inner] >>
  `is_std_type_assignment (tyaof i)` by fs[is_std_interpretation_def] >>
  imp_res_tac typesem_Fun >> imp_res_tac typesem_Bool >>
  simp[] >> simp[Once typesem_def] >> simp[Once typesem_def] >>
  simp[range_fun_to_inner,range_bool_to_inner] >>
  match_mp_tac (UNDISCH abstract_eq) >> simp[] >>
  gen_tac >> strip_tac >>
  Q.PAT_ABBREV_TAC`v:'U valuation = X Y` >>
  `is_valuation (tysof hol_ctxt) (tyaof i) v` by (
    simp[Abbr`v`] >>
    match_mp_tac is_valuation_extend >>
    simp[typesem_def] ) >>
  simp[equation_def] >>
  assume_tac hol_is_bool_sig >>
  assume_tac hol_bool_interpretation >> rfs[] >>
  use_termsem_forall >>
  simp[boolean_in_boolset,bool_to_inner_def] >>
  AP_TERM_TAC >>
  simp[ONE_ONE_DEF] >>
  `tyvof v = τ` by simp[Abbr`v`] >>
  simp[typesem_def] >>
  qho_match_abbrev_tac`(∀x. P x ⇒ Q x) ⇔ (∀x. R x)` >>
  `∀x. P x ⇔ ∃y. x = ina y` by (
    simp[Abbr`P`] >>
    gen_tac >> EQ_TAC >- (
      metis_tac[wf_to_inner_finv_right] ) >>
    metis_tac[wf_to_inner_range_thm] ) >>
  `∀x. Q (ina x) ⇔ R x` suffices_by metis_tac[] >>
  simp[Abbr`P`,Abbr`Q`,Abbr`R`] >>
  gen_tac >>
  Q.PAT_ABBREV_TAC`vx:'U valuation = X Y` >>
  `is_valuation (tysof hol_ctxt) (tyaof i) vx` by (
    simp[Abbr`vx`] >>
    match_mp_tac is_valuation_extend >>
    simp[typesem_def] >> rw[] >>
    metis_tac[]) >>
  use_termsem_forall >>
  simp[boolean_eq_true] >>
  `tyvof vx = τ` by simp[Abbr`vx`] >>
  qho_match_abbrev_tac`(∀x. P x ⇒ Q x) ⇔ (∀x. R x)` >>
  `∀x. P x ⇔ ∃y. x = ina y` by (
    simp[Abbr`P`,typesem_def] >>
    gen_tac >> EQ_TAC >- (
      metis_tac[wf_to_inner_finv_right] ) >>
    metis_tac[wf_to_inner_range_thm] ) >>
  `∀x. Q (ina x) ⇔ R x` suffices_by metis_tac[] >>
  simp[Abbr`P`,Abbr`Q`,Abbr`R`] >>
  gen_tac >>
  Q.PAT_ABBREV_TAC`vxx:'U valuation = X Y` >>
  `is_valuation (tysof hol_ctxt) (tyaof i) vxx` by (
    simp[Abbr`vxx`] >>
    match_mp_tac is_valuation_extend >>
    simp[typesem_def] >> rw[] >>
    metis_tac[]) >>
  use_termsem_implies >>
  simp[boolean_eq_true] >>
  qmatch_abbrev_tac`A ⇒ B ⇔ A' ⇒ B'` >>
  `(A ⇔ A') ∧ (B ⇔ B')` suffices_by rw[] >>
  map_every qunabbrev_tac[`A`,`A'`,`B`,`B'`] >>
  conj_tac >- (
    simp[equation_intro] >>
    use_termsem_equation >>
    simp[boolean_eq_true] >>
    simp[termsem_def] >>
    simp[Abbr`vxx`,APPLY_UPDATE_THM] >>
    simp[Abbr`vx`,APPLY_UPDATE_THM] >>
    simp[Abbr`v`,APPLY_UPDATE_THM] >>
    ntac 6 (pop_assum kall_tac) >>
    qspecl_then[`x`,`range ina`,`range inb`]mp_tac(UNDISCH in_funspace_abstract) >>
    impl_tac >- simp[] >> strip_tac >>
    BasicProvers.VAR_EQ_TAC >>
    `∃g. Abstract (range ina) (range inb) f =
         Abstract (range ina) (range inb) (λx. inb (g (finv ina x)))` by (
      qexists_tac`finv inb o f o ina` >>
      match_mp_tac(UNDISCH abstract_eq) >>
      simp[] >>
      metis_tac[wf_to_inner_finv_left,wf_to_inner_finv_right,wf_to_inner_range_thm] ) >>
    pop_assum SUBST1_TAC >>
    qspecl_then[`ina`,`inb`]mp_tac(UNDISCH wf_to_inner_fun_to_inner) >>
    impl_tac >- simp[] >>
    disch_then(assume_tac o MATCH_MP (wf_to_inner_finv_left)) >>
    simp[GSYM fun_to_inner_def] >>
    simp[fun_to_inner_def] >>
    use_apply_abstract >> simp[] >>
    impl_tac >- metis_tac[wf_to_inner_range_thm] >>
    disch_then SUBST1_TAC >>
    use_apply_abstract >> simp[] >>
    impl_tac >- metis_tac[wf_to_inner_range_thm] >>
    disch_then SUBST1_TAC >>
    qspec_then`ina`mp_tac wf_to_inner_finv_left >>
    simp[] >> disch_then kall_tac >>
    reverse EQ_TAC >- rw[] >>
    metis_tac[wf_to_inner_finv_left] ) >>
  simp[equation_intro] >>
  use_termsem_equation >>
  simp[boolean_eq_true] >>
  simp[termsem_def] >>
  simp[Abbr`vxx`,APPLY_UPDATE_THM] >>
  simp[Abbr`vx`,APPLY_UPDATE_THM] >>
  metis_tac[wf_to_inner_finv_left] )

val onto_thm = prove(
  ``is_set_theory ^mem ⇒
    good_select select ⇒
    wf_to_inner ind_to_inner ⇒
    wf_to_inner ina ⇒
    wf_to_inner inb ⇒
    tmaof (hol_model select ind_to_inner) (strlit "ONTO") [range ina; range inb] =
    fun_to_inner (fun_to_inner ina inb) bool_to_inner ONTO``,
  rw[] >>
  mp_tac hol_model_models >>
  simp[models_def] >> strip_tac >>
  first_x_assum(mp_tac o SPEC (term_to_deep (concl ONTO_DEF))) >>
  impl_tac >- EVAL_TAC >>
  simp[equation_intro] >>
  simp[satisfies_def] >>
  Q.PAT_ABBREV_TAC`i = hol_model X Y` >>
  Q.PAT_ABBREV_TAC`tm = X === Y` >>
  qabbrev_tac`τ = λx. if x = strlit"A" then range ina else range inb` >>
  `is_type_valuation τ` by (
    simp[Abbr`τ`,is_type_valuation_def] >> rw[] >>
    metis_tac[inhabited_range] ) >>
  qspecl_then[`tysof hol_ctxt`,`tyaof i`,`τ`]mp_tac (UNDISCH term_valuation_exists) >>
  impl_tac >- fs[is_interpretation_def] >> strip_tac >>
  disch_then(qspec_then`τ,σ`mp_tac) >>
  impl_tac >- fs[] >>
  qunabbrev_tac`tm` >>
  use_termsem_equation >>
  simp[boolean_eq_true] >>
  simp[Once termsem_def] >>
  qspecl_then[`tmsof hol_ctxt`,`i`,`strlit"ONTO"`]mp_tac identity_instance >>
  CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV EVAL))) >>
  simp[] >>
  EVAL_STRING_SORT >>
  disch_then kall_tac >>
  simp[listTheory.MAP_MAP_o,mlstringTheory.implode_def] >>
  `τ(strlit"A") = range ina ∧ τ(strlit"B") = range inb` by (
    simp[Abbr`τ`] ) >> simp[] >>
  disch_then kall_tac >>
  simp[Once termsem_def,Once fun_to_inner_def,range_fun_to_inner] >>
  `is_std_type_assignment (tyaof i)` by fs[is_std_interpretation_def] >>
  imp_res_tac typesem_Fun >> imp_res_tac typesem_Bool >>
  simp[] >> simp[Once typesem_def] >> simp[Once typesem_def] >>
  simp[range_fun_to_inner,range_bool_to_inner] >>
  match_mp_tac (UNDISCH abstract_eq) >> simp[] >>
  gen_tac >> strip_tac >>
  Q.PAT_ABBREV_TAC`v:'U valuation = X Y` >>
  `is_valuation (tysof hol_ctxt) (tyaof i) v` by (
    simp[Abbr`v`] >>
    match_mp_tac is_valuation_extend >>
    simp[typesem_def] ) >>
  simp[equation_def] >>
  assume_tac hol_is_bool_sig >>
  assume_tac hol_bool_interpretation >> rfs[] >>
  use_termsem_forall >>
  simp[boolean_in_boolset,bool_to_inner_def] >>
  AP_TERM_TAC >>
  simp[ONTO_DEF] >>
  `tyvof v = τ` by simp[Abbr`v`] >>
  simp[typesem_def] >>
  qho_match_abbrev_tac`(∀x. P x ⇒ Q x) ⇔ (∀x. R x)` >>
  `∀x. P x ⇔ ∃y. x = inb y` by (
    simp[Abbr`P`] >>
    gen_tac >> EQ_TAC >- (
      metis_tac[wf_to_inner_finv_right] ) >>
    metis_tac[wf_to_inner_range_thm] ) >>
  `∀x. Q (inb x) ⇔ R x` suffices_by metis_tac[] >>
  simp[Abbr`P`,Abbr`Q`,Abbr`R`] >>
  gen_tac >>
  Q.PAT_ABBREV_TAC`vx:'U valuation = X Y` >>
  `is_valuation (tysof hol_ctxt) (tyaof i) vx` by (
    simp[Abbr`vx`] >>
    match_mp_tac is_valuation_extend >>
    simp[typesem_def] >> rw[] >>
    metis_tac[]) >>
  use_termsem_exists >>
  simp[boolean_eq_true] >>
  `tyvof vx = τ` by simp[Abbr`vx`] >>
  qho_match_abbrev_tac`(∃x. P x ∧ Q x) ⇔ (∃x. R x)` >>
  `∀x. P x ⇔ ∃y. x = ina y` by (
    simp[Abbr`P`,typesem_def] >>
    gen_tac >> EQ_TAC >- (
      metis_tac[wf_to_inner_finv_right] ) >>
    metis_tac[wf_to_inner_range_thm] ) >>
  `∀x. Q (ina x) ⇔ R x` suffices_by metis_tac[] >>
  simp[Abbr`P`,Abbr`Q`,Abbr`R`] >>
  gen_tac >>
  Q.PAT_ABBREV_TAC`vxx:'U valuation = X Y` >>
  `is_valuation (tysof hol_ctxt) (tyaof i) vxx` by (
    simp[Abbr`vxx`] >>
    match_mp_tac is_valuation_extend >>
    simp[typesem_def] >> rw[] >>
    metis_tac[wf_to_inner_range_thm]) >>
  simp[equation_intro] >>
  use_termsem_equation >>
  simp[boolean_eq_true] >>
  simp[termsem_def] >>
  simp[Abbr`vxx`,APPLY_UPDATE_THM] >>
  simp[Abbr`vx`,APPLY_UPDATE_THM] >>
  simp[Abbr`v`,APPLY_UPDATE_THM] >>
  ntac 6 (pop_assum kall_tac) >>
  qspecl_then[`x`,`range ina`,`range inb`]mp_tac(UNDISCH in_funspace_abstract) >>
  impl_tac >- simp[] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  `∃g. Abstract (range ina) (range inb) f =
       Abstract (range ina) (range inb) (λx. inb (g (finv ina x)))` by (
    qexists_tac`finv inb o f o ina` >>
    match_mp_tac(UNDISCH abstract_eq) >>
    simp[] >>
    metis_tac[wf_to_inner_finv_left,wf_to_inner_finv_right,wf_to_inner_range_thm] ) >>
  pop_assum SUBST1_TAC >>
  qspecl_then[`ina`,`inb`]mp_tac(UNDISCH wf_to_inner_fun_to_inner) >>
  impl_tac >- simp[] >>
  disch_then(assume_tac o MATCH_MP (wf_to_inner_finv_left)) >>
  simp[GSYM fun_to_inner_def] >>
  simp[fun_to_inner_def] >>
  use_apply_abstract >> simp[] >>
  impl_tac >- metis_tac[wf_to_inner_range_thm] >>
  disch_then SUBST1_TAC >>
  qspec_then`ina`mp_tac wf_to_inner_finv_left >>
  simp[] >> disch_then kall_tac >>
  reverse EQ_TAC >- rw[] >>
  metis_tac[wf_to_inner_finv_left] )

val _ = save_thms ["one_one_thm","onto_thm"]
 (map UNDISCH_ALL [ one_one_thm,  onto_thm ])

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

val NewTypes_ctxt_def = Define`
  NewTypes_ctxt =
    MAP (λ(name,arity,(cs:('U list # 'U) list)). NewType name arity)`;

val NewConsts_ctxt_def = Define`
  NewConsts_ctxt = MAP (λ(name,type,(cs:('U list # 'U) list)). NewConst name type)`;

val ax_ctxt_def = Define`
  ax_ctxt ctxt ths tys tms =
    MAP NewAxiom ths ++
    NewConsts_ctxt tms ++
    NewTypes_ctxt tys ++
    ctxt`;

(* assumptions on tys and tms: *)
val [ctxt,ths,tys,tms] =
  ax_ctxt_def |> INST_TYPE[alpha|->universe_ty,beta|->universe_ty]
  |> SPEC_ALL |> concl |> lhs |> strip_comb |> #2
val distinct_tys = ``ALL_DISTINCT (MAP FST (type_list (NewTypes_ctxt ^tys ++ ^ctxt)))``
val distinct_tms = ``ALL_DISTINCT (MAP FST (const_list (NewConsts_ctxt ^tms ++ ^ctxt)))``
val disjoint_tys = ``EVERY ((ALL_DISTINCT o MAP FST) o SND o SND) ^tys``
val disjoint_tms = ``EVERY ((ALL_DISTINCT o MAP FST) o SND o SND) ^tms``
val inhabited_tys = ``EVERY (EVERY (inhabited o SND) o SND o SND) ^tys``
val types_ok = ``EVERY (type_ok (tysof (NewTypes_ctxt ^tys ++ ^ctxt)) o FST o SND) ^tms``
val _ = overload_on("intype",``λδ ty (args,u).
        u <: typesem δ ((K boolset) =++ ZIP (mlstring_sort (tyvars ty),args)) ty``);
val props_ok = ``EVERY (λp. term_ok (sigof (NewConsts_ctxt ^tms ++ NewTypes_ctxt ^tys ++ ^ctxt)) p ∧ typeof p = Bool) ^ths``
(*  - ... constrained constant values in appropriate typesem ...  *)

val ALL_DISTINCT_MAP_FST_type_list_NewTypes_ctxt = Q.store_thm("ALL_DISTINCT_MAP_FST_type_list_NewTypes_ctxt",
  `ALL_DISTINCT (MAP FST (type_list (NewTypes_ctxt tys))) ⇔ ALL_DISTINCT (MAP FST tys)`,
  rw[NewTypes_ctxt_def,MAP_MAP_o,o_DEF,UNCURRY,FLAT_MAP_SING,ETA_AX]);

val ALL_DISTINCT_MAP_FST_const_list_NewConsts_ctxt = Q.store_thm("ALL_DISTINCT_MAP_FST_const_list_NewConsts_ctxt",
  `ALL_DISTINCT (MAP FST (const_list (NewConsts_ctxt tms))) ⇔ ALL_DISTINCT (MAP FST tms)`,
  rw[NewConsts_ctxt_def,MAP_MAP_o,o_DEF,UNCURRY,FLAT_MAP_SING,ETA_AX]);

val MEM_type_list_NewTypes_ctxt = Q.store_thm("MEM_type_list_NewTypes_ctxt",
  `MEM x (type_list (NewTypes_ctxt tys)) ⇔ MEM x (MAP (λ(name,arity,cs). (name,arity)) tys)`,
  rw[MEM_FLAT,MAP_MAP_o,NewTypes_ctxt_def,o_DEF,UNCURRY,MEM_MAP,EQ_IMP_THM] \\ fs[PULL_EXISTS]
  \\ metis_tac[]);

val MEM_const_list_NewConsts_ctxt = Q.store_thm("MEM_const_list_NewConsts_ctxt",
  `MEM x (const_list (NewConsts_ctxt tms)) ⇔ MEM x (MAP (λ(name,type,cs). (name,type)) tms)`,
  rw[MEM_FLAT,MAP_MAP_o,NewConsts_ctxt_def,o_DEF,UNCURRY,MEM_MAP,EQ_IMP_THM] \\ fs[PULL_EXISTS]
  \\ metis_tac[]);

val ALOOKUP_type_list_NewTypes_ctxt = Q.store_thm("ALOOKUP_type_list_NewTypes_ctxt",
  `ALOOKUP (type_list (NewTypes_ctxt tys)) k =
   OPTION_MAP FST (ALOOKUP tys k)`,
  rw[NewTypes_ctxt_def,MAP_MAP_o,o_DEF,UNCURRY,FLAT_MAP_SING]
  \\ rw[ALOOKUP_MAP_gen,Once LAMBDA_PROD,ETA_AX]);

val ALOOKUP_const_list_NewConsts_ctxt = Q.store_thm("ALOOKUP_const_list_NewConsts_ctxt",
  `ALOOKUP (const_list (NewConsts_ctxt tms)) k =
   OPTION_MAP FST (ALOOKUP tms k)`,
  rw[NewConsts_ctxt_def,MAP_MAP_o,o_DEF,UNCURRY,FLAT_MAP_SING]
  \\ rw[ALOOKUP_MAP_gen,Once LAMBDA_PROD,ETA_AX]);

val const_list_NewTypes_ctxt = Q.store_thm("const_list_NewTypes_ctxt[simp]",
  `const_list (NewTypes_ctxt tys) = []`,
  rw[NewTypes_ctxt_def,MAP_FLAT,MAP_MAP_o,o_DEF,UNCURRY,FLAT_EQ_NIL,EVERY_MAP]);

val type_list_NewConsts_ctxt = Q.store_thm("type_list_NewConsts_ctxt[simp]",
  `type_list (NewConsts_ctxt tys) = []`,
  rw[NewConsts_ctxt_def,MAP_FLAT,MAP_MAP_o,o_DEF,UNCURRY,FLAT_EQ_NIL,EVERY_MAP]);

val type_list_NewAxioms_ctxt = Q.store_thm("type_list_NewAxioms_ctxt[simp]",
  `type_list (MAP NewAxiom ths) = []`,
  rw[MAP_FLAT,MAP_MAP_o,o_DEF,UNCURRY,FLAT_EQ_NIL,EVERY_MAP]);

val NewTypes_ctxt_extends = Q.store_thm("NewTypes_ctxt_extends",
  `∀tys.
   ^distinct_tys
   ⇒
   NewTypes_ctxt tys ++ ctxt extends ctxt`,
  simp[NewTypes_ctxt_def]
  \\ Induct \\ simp[]
  >- metis_tac[RTC_REFL,extends_def]
  \\ fs[ALL_DISTINCT_APPEND] \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ simp[extends_def]
  \\ simp[Once RTC_CASES1]
  \\ simp[GSYM extends_def]
  \\ simp[Once updates_cases]);

val NewConsts_ctxt_extends = Q.store_thm("NewConsts_ctxt_extends",
  `∀tms.
   ALL_DISTINCT (MAP FST (const_list (NewConsts_ctxt ^tms ++ ctxt))) ∧
   EVERY (type_ok (tysof (NewTypes_ctxt ^tys ++ ctxt)) o FST o SND) tms
   ⇒
   NewConsts_ctxt tms ++ NewTypes_ctxt tys ++ ctxt extends NewTypes_ctxt tys ++ ctxt`,
  gen_tac
  \\ `const_list (NewConsts_ctxt tms ++ ctxt) =
      const_list (NewConsts_ctxt tms ++ NewTypes_ctxt tys ++ ctxt)` by (simp[])
  \\ pop_assum SUBST_ALL_TAC
  \\ REWRITE_TAC[GSYM APPEND_ASSOC]
  \\ qspec_tac(`NewTypes_ctxt tys ++ ctxt`,`ttxt`)
  \\ qx_gen_tac`ctxt`
  \\ simp[NewConsts_ctxt_def]
  \\ Induct_on`tms` \\ simp[]
  >- metis_tac[extends_def,RTC_REFL]
  \\ fs[ALL_DISTINCT_APPEND] \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ simp[extends_def]
  \\ simp[Once RTC_CASES1]
  \\ simp[GSYM extends_def]
  \\ rw[Once updates_cases]
  \\ match_mp_tac type_ok_extend
  \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
  \\ simp[]
  \\ match_mp_tac SUBMAP_FUNION
  \\ simp[IN_DISJOINT,MEM_FLAT,MEM_MAP,FORALL_PROD,PULL_EXISTS]);

val NewAxioms_ctxt_extends = Q.store_thm("NewAxioms_ctxt_extends",
  `∀ths. EVERY (λp. term_ok (sigof ctxt) p ∧ typeof p = Bool) ths ⇒
   MAP NewAxiom ths ++ ctxt extends ctxt`,
  Induct \\ simp[]
  >- metis_tac[RTC_REFL,extends_def]
  \\ fs[] \\ rw[]
  \\ simp[extends_def]
  \\ simp[Once RTC_CASES1]
  \\ simp[GSYM extends_def]
  \\ simp[Once updates_cases]
  \\ imp_res_tac term_ok_welltyped
  \\ conj_tac >- metis_tac[WELLTYPED]
  \\ match_mp_tac term_ok_extend
  \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
  \\ simp[]
  \\ match_mp_tac SUBMAP_FUNION
  \\ simp[IN_DISJOINT,MEM_FLAT,MEM_MAP,FORALL_PROD,PULL_EXISTS]);

val tysof_NewConsts_ctxt = Q.store_thm("tysof_NewConsts_ctxt[simp]",
  `tysof (NewConsts_ctxt tms ++ ctxt) = tysof ctxt`,
  rw[NewConsts_ctxt_def,MAP_MAP_o,o_DEF,UNCURRY,FLAT_MAP_NIL]);

val tysof_NewAxioms_ctxt = Q.store_thm("tysof_NewAxioms_ctxt[simp]",
  `tysof (MAP NewAxiom ths ++ ctxt) = tysof ctxt`,
  rw[MAP_MAP_o,o_DEF,UNCURRY,FLAT_MAP_NIL]);

val tmsof_NewAxioms_ctxt = Q.store_thm("tmsof_NewAxioms_ctxt[simp]",
  `tmsof (MAP NewAxiom ths ++ ctxt) = tmsof ctxt`,
  rw[MAP_MAP_o,o_DEF,UNCURRY,FLAT_MAP_NIL]);

val ax_ctxt_extends_ctxt = Q.store_thm("ax_ctxt_extends_ctxt",
  `^distinct_tys ∧
   ^distinct_tms ∧
   ^types_ok ∧
   ^props_ok
   ⇒
   ax_ctxt ctxt ths tys tms extends ctxt`,
  rw[ax_ctxt_def]
  \\ match_mp_tac extends_trans
  \\ qspec_then`tys`(part_match_exists_tac(last o strip_conj) o concl o UNDISCH)NewTypes_ctxt_extends
  \\ simp[NewTypes_ctxt_extends]
  \\ match_mp_tac extends_trans
  \\ qspec_then`tms`(part_match_exists_tac(last o strip_conj) o concl o UNDISCH)NewConsts_ctxt_extends
  \\ simp[NewConsts_ctxt_extends]
  \\ REWRITE_TAC[GSYM APPEND_ASSOC]
  \\ match_mp_tac NewAxioms_ctxt_extends
  \\ fs[]);

val ax_tyass_def = xDefine"ax_tyass"`
  ax_tyass0 ^mem δ tys name args =
    case ALOOKUP tys name of
    | NONE => δ name args
    | SOME (arity,cs) =>
      (case ALOOKUP cs args of
       | NONE => One
       | SOME u => u)`;
val _ = overload_on("ax_tyass",``ax_tyass0 ^mem``);

val is_type_assignment_ax_tyass = Q.store_thm("is_type_assignment_ax_tyass",
  `is_set_theory ^mem ∧
   is_type_assignment (tysof ctxt) δ ∧
   ^inhabited_tys
   ⇒
   is_type_assignment (tysof (NewTypes_ctxt tys ++ ctxt)) (ax_tyass δ tys)`,
  rw[is_type_assignment_def,FEVERY_ALL_FLOOKUP,ALOOKUP_APPEND,ALOOKUP_type_list_NewTypes_ctxt]
  \\ rw[ax_tyass_def]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ split_pair_case_tac \\ fs[]
  \\ BasicProvers.CASE_TAC
  >- metis_tac[mem_one]
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs[EVERY_MEM,FORALL_PROD]
  \\ metis_tac[]);

val ax_tyass_values = Q.store_thm("ax_tyass_values",
  `^distinct_tys ∧
   ^disjoint_tys
   ⇒
   EVERY
    (λ(name,arity,cs).
      EVERY
        (λ(args,v). ax_tyass δ tys name args = v)
        cs)
    tys`,
  rw[ax_tyass_def,EVERY_MEM]
  \\ pairarg_tac \\ fs[] \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ BasicProvers.CASE_TAC
  >- (
    imp_res_tac ALOOKUP_FAILS \\ fs[] )
  \\ split_pair_case_tac \\ fs[] \\ rw[]
  \\ fs[ALL_DISTINCT_APPEND,ALL_DISTINCT_MAP_FST_type_list_NewTypes_ctxt]
  \\ imp_res_tac ALOOKUP_ALL_DISTINCT_MEM \\ fs[] \\ rw[]
  \\ BasicProvers.CASE_TAC
  >- (
    imp_res_tac ALOOKUP_FAILS \\ fs[] )
  \\ res_tac \\ fs[]);

val ax_tmass_def = xDefine"ax_tmass"`
  ax_tmass0 ^mem i tms name args =
  case ALOOKUP tms name of
  | NONE => tmaof i name args
  | SOME (ty,cs) =>
    (case ALOOKUP cs args of
     | NONE =>
       @u.  u <: typesem (tyaof i)
                   ((K boolset) =++ ZIP(mlstring_sort (tyvars ty), args))
                   ty
     | SOME u => u)`;
val _ = overload_on("ax_tmass",``ax_tmass0 ^mem``);

val is_term_assignment_ax_tmass = Q.store_thm("is_term_assignment_ax_tmass",
  `is_set_theory ^mem ∧
   is_term_assignment (tmsof ctxt) (tyaof i) (tmaof i) ∧
   is_type_assignment (tysof ctxt) (tyaof i) ∧
   EVERY (type_ok (tysof ctxt) o FST o SND) tms ∧
   EVERY (λ(name,ty,cs). EVERY (intype (tyaof i) ty) cs) tms
   ⇒
   is_term_assignment (tmsof (NewConsts_ctxt tms ++ ctxt)) (tyaof i) (ax_tmass i tms)`,
  rw[is_term_assignment_def,FEVERY_ALL_FLOOKUP,ALOOKUP_APPEND,ALOOKUP_const_list_NewConsts_ctxt]
  \\ rw[ax_tmass_def]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ split_pair_case_tac \\ fs[]
  \\ BasicProvers.CASE_TAC
  >- (
    SELECT_ELIM_TAC
    \\ conj_tac
    >- (
      match_mp_tac (MP_CANON typesem_inhabited)
      \\ first_assum(part_match_exists_tac(el 3 o strip_conj) o concl)
      \\ simp[]
      \\ conj_tac
      >- (
        match_mp_tac (MP_CANON is_type_valuation_update_list)
        \\ simp[is_type_valuation_base]
        \\ simp[mlstring_sort_def]
        \\ simp[MAP_MAP_o,EVERY_MEM,MEM_ZIP,PULL_EXISTS,EL_MAP]
        \\ fs[is_type_valuation_def] )
      \\ imp_res_tac ALOOKUP_MEM
      \\ fs[EVERY_MAP,EVERY_MEM,FORALL_PROD]
      \\ first_x_assum match_mp_tac
      \\ first_assum(match_exists_tac o concl)
      \\ simp[] )
    \\ gen_tac
    \\ qmatch_abbrev_tac`_ <: m1 ⇒ _ <: m2`
    \\ `m2 = m1` suffices_by rw[]
    \\ unabbrev_all_tac
    \\ match_mp_tac typesem_tyvars
    \\ simp[APPLY_UPDATE_LIST_ALOOKUP]
    \\ rw[]
    \\ BasicProvers.CASE_TAC
    >- (
      imp_res_tac ALOOKUP_FAILS
      \\ fs[MEM_ZIP,mlstring_sort_def]
      \\ fs[GSYM mlstring_sort_def]
      \\ qmatch_assum_rename_tac`MEM z _`
      \\ `¬MEM z (mlstring_sort(tyvars ty))`
      by ( simp[MEM_EL] \\ fs[mlstring_sort_def] )
      \\ fs[mlstring_sort_def,MEM_MAP,PULL_EXISTS,mlstringTheory.implode_explode] )
    \\ imp_res_tac ALOOKUP_MEM
    \\ fs[MEM_ZIP,mlstring_sort_def]
    \\ fs[GSYM mlstring_sort_def]
    \\ rw[]
    \\ fs[mlstring_sort_def,EL_MAP] )
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs[EVERY_MEM,FORALL_PROD]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ qmatch_abbrev_tac`_ <: m1 ⇒ _ <: m2`
  \\ `m2 = m1` suffices_by rw[]
  \\ unabbrev_all_tac
  \\ match_mp_tac typesem_tyvars
  \\ simp[APPLY_UPDATE_LIST_ALOOKUP]
  \\ rw[]
  \\ BasicProvers.CASE_TAC
  >- (
      imp_res_tac ALOOKUP_FAILS
      \\ fs[MEM_ZIP,mlstring_sort_def]
      \\ fs[GSYM mlstring_sort_def]
      \\ qmatch_assum_rename_tac`MEM z _`
      \\ `¬MEM z (mlstring_sort(tyvars ty))`
      by ( simp[MEM_EL] \\ fs[mlstring_sort_def] )
      \\ fs[mlstring_sort_def,MEM_MAP,PULL_EXISTS,mlstringTheory.implode_explode] )
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs[MEM_ZIP,mlstring_sort_def]
  \\ fs[GSYM mlstring_sort_def]
  \\ rw[]
  \\ fs[mlstring_sort_def,EL_MAP] );

val ax_tmass_values = Q.store_thm("ax_tmass_values",
  `^distinct_tms ∧
   ^disjoint_tms
   ⇒
   EVERY
    (λ(name,ty,cs).
      EVERY
        (λ(args,v). ax_tmass i tms name args = v)
        cs)
    tms`,
  rw[ax_tmass_def,EVERY_MEM]
  \\ pairarg_tac \\ fs[] \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ BasicProvers.CASE_TAC
  >- (
    imp_res_tac ALOOKUP_FAILS \\ fs[] )
  \\ split_pair_case_tac \\ fs[] \\ rw[]
  \\ fs[ALL_DISTINCT_APPEND,ALL_DISTINCT_MAP_FST_const_list_NewConsts_ctxt]
  \\ imp_res_tac ALOOKUP_ALL_DISTINCT_MEM \\ fs[] \\ rw[]
  \\ BasicProvers.CASE_TAC
  >- (
    imp_res_tac ALOOKUP_FAILS \\ fs[] )
  \\ res_tac \\ fs[]);

val ax_int_def = xDefine"ax_int"`
  ax_int0 ^mem i tys tms =
    (ax_tyass (tyaof i) tys,
     ax_tmass (ax_tyass (tyaof i) tys,tmaof i) tms)`;
val _ = overload_on("ax_int",``ax_int0 ^mem``);

val is_interpretation_ax_int = Q.store_thm("is_interpretation_ax_int",
  `is_set_theory ^mem ∧
   theory_ok (thyof ctxt) ∧
   is_interpretation (sigof ctxt) i ∧
   ^distinct_tys ∧
   ^inhabited_tys ∧
   ^types_ok ∧
   EVERY (λ(name,ty,cs). EVERY (intype (ax_tyass (tyaof i) tys) ty) cs) tms
   ⇒ is_interpretation (sigof (ax_ctxt ctxt ths tys tms)) (ax_int i tys tms)`,
  strip_tac
  \\ qhdtm_x_assum`is_interpretation0`mp_tac
  \\ REWRITE_TAC[is_interpretation_def,ax_int_def,ax_ctxt_def]
  \\ strip_tac
  \\ REWRITE_TAC[tysof_NewAxioms_ctxt,tysof_NewConsts_ctxt,
                 tmsof_NewAxioms_ctxt,GSYM APPEND_ASSOC]
  \\ conj_asm1_tac
  >- ( match_mp_tac is_type_assignment_ax_tyass \\ rw[] )
  \\ qmatch_goalsub_abbrev_tac`(δ,γ):'U interpretation`
  \\ `δ = tyaof (δ,γ)` by simp[]
  \\ pop_assum(fn th => CONV_TAC(RATOR_CONV(ONCE_REWRITE_CONV[th])))
  \\ match_mp_tac is_term_assignment_ax_tmass
  \\ rw[] \\ fs[]
  \\ fs[is_term_assignment_def,FEVERY_ALL_FLOOKUP]
  \\ rw[]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ qmatch_abbrev_tac`_ <: t1 ⇒ _ <: t2`
  \\ `t1 = t2` suffices_by rw[]
  \\ unabbrev_all_tac
  \\ match_mp_tac typesem_sig
  \\ qexists_tac`tysof ctxt`
  \\ conj_asm1_tac
  >- (
    fs[theory_ok_def]
    \\ first_x_assum match_mp_tac
    \\ simp[IN_FRANGE_FLOOKUP]
    \\ metis_tac[] )
  \\ rw[ax_tyass_def,FUN_EQ_THM]
  \\ BasicProvers.CASE_TAC
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs[ALL_DISTINCT_APPEND,MEM_MAP,PULL_EXISTS,EXISTS_PROD,MEM_type_list_NewTypes_ctxt]
  \\ metis_tac[PAIR] );

val is_std_interpretation_ax_int = Q.store_thm("is_std_interpretation_ax_int",
  `is_set_theory ^mem ∧
   is_std_sig (sigof ctxt) ∧
   is_std_interpretation i ∧
   ^distinct_tys ∧
   ^distinct_tms
   ⇒
   is_std_interpretation (ax_int i tys tms)`,
  strip_tac
  \\ match_mp_tac (GEN_ALL is_std_interpretation_equal_on)
  \\ qexists_tac`sigof ctxt`
  \\ qexists_tac`i`
  \\ simp[equal_on_def,ax_int_def]
  \\ rw[ax_tyass_def,ax_tmass_def,FUN_EQ_THM]
  \\ BasicProvers.CASE_TAC
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs[ALL_DISTINCT_APPEND,MEM_type_list_NewTypes_ctxt,MEM_const_list_NewConsts_ctxt,
        MEM_MAP,PULL_EXISTS,EXISTS_PROD]
  \\ metis_tac[PAIR]);

val good_context_ax = Q.store_thm("good_context_ax",
  `is_set_theory ^mem ∧
   theory_ok (thyof ctxt) ∧
   is_interpretation (sigof ctxt) i ∧
   is_std_interpretation i ∧
   ^distinct_tys ∧
   ^distinct_tms ∧
   ^inhabited_tys ∧
   ^types_ok ∧
   EVERY (λ(name,ty,cs). EVERY (intype (ax_tyass (tyaof i) tys) ty) cs) tms ∧
   ^props_ok
   ⇒
   good_context ^mem (sigof (ax_ctxt ctxt ths tys tms)) (ax_int i tys tms)`,
  strip_tac
  \\ REWRITE_TAC[good_context_unpaired]
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ conj_tac
  >- metis_tac[ax_ctxt_extends_ctxt,is_std_sig_extends,theory_ok_sig,FST,SND]
  \\ conj_tac
  >- metis_tac[is_interpretation_ax_int]
  \\ metis_tac[is_std_interpretation_ax_int,theory_ok_sig,FST,SND]);

val MEM_axiom_list_ax_ctxt = Q.store_thm("MEM_axiom_list_ax_ctxt[simp]",
  `MEM p (axiom_list (ax_ctxt ctxt ths tys tms)) ⇔ MEM p ths ∨ MEM p (axiom_list ctxt)`,
  rw[ax_ctxt_def,NewConsts_ctxt_def,NewTypes_ctxt_def,
     MEM_MAP,MEM_FLAT,PULL_EXISTS,EXISTS_PROD,EQ_IMP_THM]
  \\ fs[axexts_of_upd_def,conexts_of_upd_def]
  \\ fsrw_tac[boolSimps.DNF_ss][]
  \\ metis_tac[]);

val ax_int_equal_on = Q.store_thm("ax_int_equal_on",
  `^distinct_tys ⇒
   ^distinct_tms ⇒
   equal_on (sigof ctxt) i (ax_int i tys tms)`,
  rw[equal_on_def]
  \\ rw[ax_int_def,ax_tyass_def,ax_tmass_def,FUN_EQ_THM]
  \\ BasicProvers.CASE_TAC
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs[ALL_DISTINCT_APPEND,
        MEM_type_list_NewTypes_ctxt,
        MEM_const_list_NewConsts_ctxt,
        MEM_MAP,PULL_EXISTS]
  \\ res_tac \\ fs[UNCURRY]
  \\ metis_tac[])

val ax_int_models = Q.store_thm("ax_int_models",
  `theory_ok (thyof ctxt) ⇒
   ^distinct_tys ⇒
   ^distinct_tms ⇒
   good_context ^mem (sigof (ax_ctxt ctxt ths tys tms)) (ax_int i tys tms) ⇒
   i models thyof ctxt ⇒
   EVERY (λp. ∀v. is_valuation (tysof (sigof (ax_ctxt ctxt ths tys tms))) (tyaof (ax_int i tys tms)) v ⇒
                  (termsem (tmsof (sigof (ax_ctxt ctxt ths tys tms))) (ax_int i tys tms) v p = True)) ths
   ⇒
   ax_int i tys tms models (thyof (ax_ctxt ctxt ths tys tms))`,
  rw[models_def,good_context_unpaired,satisfies_def,EVERY_MEM] \\ fs[]
  \\ first_x_assum drule
  \\ disch_then(qspec_then`v`mp_tac)
  \\ impl_tac
  >- (
    fs[is_valuation_def,is_term_valuation_def]
    \\ rw[]
    \\ `type_ok (tysof (ax_ctxt ctxt ths tys tms) ) ty`
    by (
      match_mp_tac type_ok_extend
      \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
      \\ simp[ax_ctxt_def]
      \\ match_mp_tac SUBMAP_FUNION
      \\ fs[IN_DISJOINT,ALL_DISTINCT_APPEND,MEM_FLAT,FORALL_PROD,MEM_MAP,PULL_EXISTS]
      \\ metis_tac[] )
    \\ `typesem (tyaof i) (tyvof v) ty =
        typesem (tyaof (ax_int i tys tms)) (tyvof v) ty`
    by (
      match_mp_tac typesem_sig
      \\ last_assum(part_match_exists_tac(hd o strip_conj) o concl)
      \\ simp[ax_int_def,ax_tyass_def,FUN_EQ_THM]
      \\ rw[]
      \\ BasicProvers.CASE_TAC
      \\ imp_res_tac ALOOKUP_MEM
      \\ fs[ALL_DISTINCT_APPEND,MEM_MAP,MEM_FLAT,EXISTS_PROD,PULL_EXISTS,NewTypes_ctxt_def]
      \\ metis_tac[PAIR] )
    \\ rw[] )
  \\ disch_then(SUBST_ALL_TAC o SYM)
  \\ `tmsof ctxt ⊑ tmsof (ax_ctxt ctxt ths tys tms)`
  by (
    simp[ax_ctxt_def]
    \\ match_mp_tac SUBMAP_FUNION
    \\ fs[IN_DISJOINT,ALL_DISTINCT_APPEND,MEM_FLAT,FORALL_PROD,MEM_MAP,PULL_EXISTS]
    \\ metis_tac[] )
  \\ `term_ok (sigof ctxt) p` by fs[theory_ok_def]
  \\ imp_res_tac termsem_extend \\ simp[]
  \\ match_mp_tac termsem_sig
  \\ qexists_tac`sigof ctxt`
  \\ fs[theory_ok_def]
  \\ simp[equal_on_def]
  \\ simp[ax_int_def,ax_tyass_def,ax_tmass_def,FUN_EQ_THM]
  \\ rw[]
  \\ BasicProvers.CASE_TAC
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs[ALL_DISTINCT_APPEND,MEM_MAP,MEM_FLAT,EXISTS_PROD,PULL_EXISTS,NewTypes_ctxt_def,NewConsts_ctxt_def]
  \\ metis_tac[PAIR]);

val std_equality = Q.store_thm("std_equality",
  `is_set_theory ^mem ⇒
   is_std_interpretation i ⇒
   wf_to_inner ina ⇒
   (tmaof i (strlit "=") [range ina] =
    fun_to_inner ina (fun_to_inner ina bool_to_inner) $=)`,
  rw[is_std_interpretation_def,interprets_def,fun_to_inner_def]
  \\ first_x_assum(qspec_then`((strlit"A")=+range ina)(K boolset)`mp_tac)
  \\ impl_tac
  >- (
    simp[is_type_valuation_def,APPLY_UPDATE_THM]
    \\ rw[]
    >- ( match_mp_tac inhabited_range \\ rw[] )
    \\ metis_tac[mem_boolset] )
  \\ rw[APPLY_UPDATE_THM,range_fun_to_inner,wf_to_inner_bool_to_inner,range_bool_to_inner]
  \\ match_mp_tac (UNDISCH abstract_eq)
  \\ rw[]
  \\ TRY (
    match_mp_tac (UNDISCH abstract_in_funspace)
    \\ rw[boolean_in_boolset,bool_to_inner_def] )
  \\ match_mp_tac (UNDISCH abstract_eq)
  \\ rw[boolean_in_boolset,bool_to_inner_def]
  \\ rw[boolean_def]
  \\ metis_tac[wf_to_inner_finv_right]);

val _ = export_theory()
