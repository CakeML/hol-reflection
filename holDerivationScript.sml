open preamble holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
val _ = new_theory"holDerivation"

val _ = temp_tight_equality()

(* TODO: move? *)
val FLOOKUP_tmsof_updates = store_thm("FLOOKUP_tmsof_updates",
  ``∀upd ctxt. upd updates ctxt ⇒
    FLOOKUP (tmsof (thyof ctxt)) name = SOME ty ⇒
    FLOOKUP (tmsof (thyof (upd::ctxt))) name = SOME ty``,
  rw[finite_mapTheory.FLOOKUP_FUNION] >>
  BasicProvers.CASE_TAC >> imp_res_tac updates_DISJOINT >>
  fs[pred_setTheory.IN_DISJOINT,listTheory.MEM_MAP,pairTheory.EXISTS_PROD] >>
  PROVE_TAC[alistTheory.ALOOKUP_MEM])

val FLOOKUP_tysof_updates = store_thm("FLOOKUP_tysof_updates",
  ``∀upd ctxt. upd updates ctxt ⇒
    FLOOKUP (tysof (thyof ctxt)) name = SOME a ⇒
    FLOOKUP (tysof (thyof (upd::ctxt))) name = SOME a``,
  rw[finite_mapTheory.FLOOKUP_FUNION] >>
  BasicProvers.CASE_TAC >> imp_res_tac updates_DISJOINT >>
  fs[pred_setTheory.IN_DISJOINT,listTheory.MEM_MAP,pairTheory.EXISTS_PROD] >>
  PROVE_TAC[alistTheory.ALOOKUP_MEM])

val term_ok_updates = store_thm("term_ok_updates",
  ``∀upd ctxt. upd updates ctxt ⇒
      term_ok (sigof (thyof ctxt)) tm ⇒
      term_ok (sigof (thyof (upd::ctxt))) tm``,
  rw[] >> match_mp_tac term_ok_extend >>
  map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
  simp[] >> conj_tac >> match_mp_tac finite_mapTheory.SUBMAP_FUNION >>
  metis_tac[updates_DISJOINT,finite_mapTheory.SUBMAP_REFL,pred_setTheory.DISJOINT_SYM])
(* -- *)

val term_ok_Abs = store_thm("term_ok_Abs",
  ``∀v. term_ok (sigof (thy:thy)) b ∧ type_ok (tysof thy) ty ⇒
      term_ok (sigof thy) (Abs (Var v ty) b)``,
  rw[term_ok_def])

val term_ok_Comb = store_thm("term_ok_Comb",
  ``term_ok (sigof (thy:thy)) x ∧ term_ok (sigof thy) f ∧
    welltyped (Comb f x) ⇒
    term_ok (sigof thy) (Comb f x)``,
  rw[term_ok_def])

val term_ok_Const = store_thm("term_ok_Const",
  ``(FLOOKUP (tmsof (thy:thy)) name = SOME ty0) ∧
    type_ok (tysof thy) ty ⇒
    is_instance ty0 ty ⇒
    term_ok (sigof thy) (Const name ty)``,
  rw[term_ok_def])

val term_ok_Var = store_thm("term_ok_Var",
  ``∀name. type_ok (tysof (thy:thy)) ty ⇒
    term_ok (sigof thy) (Var name ty)``,
  rw[term_ok_def])

val type_ok_Tyvar = store_thm("type_ok_Tyvar",
  ``∀(thy:thy) a. type_ok (tysof thy) (Tyvar a)``,
  rw[type_ok_def])

val type_ok_Tyapp = store_thm("type_ok_Tyapp",
  ``(FLOOKUP (tysof (thy:thy)) name = SOME a) ⇒
    EVERY (type_ok (tysof thy)) args ⇒
    (LENGTH args = a)
    ⇒ type_ok (tysof thy) (Tyapp name args)``,
  rw[type_ok_def] >>
  asm_simp_tac (std_ss++boolSimps.ETA_ss)[])

val is_instance_lemma = store_thm("is_instance_lemma",
  ``(TYPE_SUBST s ty1 = ty2) ⇒ is_instance ty1 ty2``,
  rw[] >> metis_tac[])

val lookup_type_ok = store_thm("lookup_type_ok",
  ``theory_ok thy ∧
    (FLOOKUP (tmsof thy) name = SOME ty0) ⇒
    type_ok (tysof thy) ty0``,
  rw[theory_ok_def,finite_mapTheory.IN_FRANGE_FLOOKUP,PULL_EXISTS] >>
  metis_tac[])

val absThm_equation = save_thm("absThm_equation",
  proves_rules |> CONJUNCTS |> el 1
  |> ONCE_REWRITE_RULE[CONJ_COMM]
  |> REWRITE_RULE[GSYM AND_IMP_INTRO,NOT_EXISTS])

val absThm = store_thm("absThm",
  ``∀h l r thy ty x ey.
    type_ok (tysof thy) ty ⇒
    (thy,h) |- Comb (Comb (Equal ey) l) r ⇒
    EVERY ($~ o VFREE_IN (Var x ty)) h ⇒
    (thy,h) |- Comb (Comb (Equal (Fun ty ey)) (Abs (Var x ty) l)) (Abs (Var x ty) r)``,
  rw[] >>
  imp_res_tac proves_term_ok >> fs[] >>
  imp_res_tac term_ok_welltyped >> fs[] >>
  `typeof (Abs (Var x ty) l) = Fun ty (typeof r)` by (simp[] >> rw[] ) >>
  pop_assum(SUBST1_TAC o SYM) >>
  REWRITE_TAC[GSYM equation_def] >>
  match_mp_tac (MP_CANON absThm_equation) >>
  simp[equation_def])

val appThm = store_thm("appThm",
  ``∀h1 h2 l1 l2 r1 r2 thy ty1 ty2.
    (thy,h1) |- Comb (Comb (Equal (Fun ty1 ty2)) l1) r1 ⇒
    (thy,h2) |- Comb (Comb (Equal ty1) l2) r2 ⇒
    welltyped (Comb l1 l2) ⇒
    (thy,term_union h1 h2) |- Comb (Comb (Equal ty2) (Comb l1 l2)) (Comb r1 r2)``,
  rw[] >>
  imp_res_tac proves_term_ok >> fs[] >>
  imp_res_tac term_ok_welltyped >> fs[] >>
  `typeof (Comb l1 l2) = ty2` by (simp[] >> metis_tac[codomain_def]) >>
  pop_assum(SUBST1_TAC o SYM) >>
  REWRITE_TAC[GSYM equation_def] >>
  match_mp_tac (MP_CANON appThm_equation) >>
  simp[equation_def])

val axiom = store_thm("axiom",
  ``∀c c' thy. theory_ok thy ⇒
      welltyped c' ⇒
      c ∈ axsof thy ∧ ACONV c c' ⇒
      (thy,[]) |- c'``,
  rw[] >>
  imp_res_tac(proves_rules |> CONJUNCTS |> el 11) >>
  match_mp_tac proves_ACONV >> simp[] >>
  metis_tac[])

val assume = store_thm("assume",
  ``∀p thy. theory_ok thy ⇒
    term_ok (sigof thy) p ⇒
    (typeof p = Bool) ⇒
    (thy,[p]) |- p``,
  rpt strip_tac >>
  metis_tac[proves_rules |> CONJUNCTS |> el 2,
            holSyntaxExtraTheory.term_ok_welltyped,
            holSyntaxExtraTheory.WELLTYPED])

val deductAntisym = store_thm("deductAntisym",
  ``∀c1 c2 h1 h2 thy.
    (thy,h1) |- c1 ∧ (thy,h2) |- c2 ⇒
    (typeof c1 = ty) ⇒
    (thy,term_union(term_remove c2 h1)(term_remove c1 h2)) |-
      Comb (Comb (Equal ty) c1) c2``,
  rw[] >> rw[GSYM equation_def] >>
  metis_tac[deductAntisym_equation])

val eqMp = store_thm("eqMp",
  ``∀h1 h2 p p' q thy ty.
    (thy,h1) |- Comb (Comb (Equal ty) p) q ⇒
    (thy,h2) |- p' ⇒
    ACONV p p' ⇒
    (thy,term_union h1 h2) |- q``,
  rw[] >>
  imp_res_tac proves_term_ok >> fs[] >>
  imp_res_tac term_ok_welltyped >> fs[] >>
  metis_tac[eqMp_equation,equation_def])

val refl = store_thm("refl",
  ``∀t thy. theory_ok thy ∧ term_ok (sigof thy) t ⇒ (typeof t = ty) ⇒
      (thy,[]) |- Comb (Comb (Equal ty) t) t``,
  rw[] >> rw[GSYM equation_def] >> metis_tac[refl_equation])

val inst_type = proves_rules |> CONJUNCTS |> el 7
val vsubst = proves_rules |> CONJUNCTS |> el 6
  |> ONCE_REWRITE_RULE[CONJ_COMM]
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]

val betaConvVar = (proves_rules |> CONJUNCTS |> el 3)

val betaConv = store_thm("betaConv",
  ``∀x ty ty1 t thy u.
    theory_ok thy ⇒
    term_ok (sigof thy) (Comb (Abs (Var x ty) t) u) ⇒
    (typeof t = ty1) ⇒
    (thy,[]) |- Comb
      (Comb (Equal ty1) (Comb (Abs (Var x ty) t) u))
      (VSUBST [(u,Var x ty)] t)``,
  rw[term_ok_def] >>
  qspecl_then[`t`,`thy`,`typeof u`,`x`]mp_tac betaConvVar >>
  simp[] >>
  disch_then(mp_tac o MATCH_MP vsubst) >>
  Q.PAT_ABBREV_TAC`ilist = [(u,X:term)]` >>
  disch_then(qspec_then`ilist`mp_tac) >>
  impl_tac >- (
    simp[Abbr`ilist`] >> fs[WELLTYPED] ) >>
  simp[Once term_image_def] >>
  simp[equation_def] >>
  simp[VSUBST_def,Abbr`ilist`,REV_ASSOCD])

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

val (inst_core_eval_def,inst_eval_def) =
  let
    val INST_CORE =``INST_CORE``
    val ty = type_of INST_CORE
    val inst_core_eval = mk_var("inst_core_eval",ty)
    val deftm =
      (INST_CORE_Abs_thm |> SPEC_ALL |> concl |> dest_imp |> snd
       |> replace_term (mk_var("_",``:type``)) ``u:type``)
      ::(INST_CORE_def |> CONJUNCTS |> map SPEC_ALL |> map concl |> List.rev |> tl)
      |> rev |> list_mk_conj
      |> replace_term INST_CORE inst_core_eval
    val INST = ``INST``
    val ty2 = type_of INST
    val inst_eval = mk_var("inst_eval",ty2)
    val th1 = tDefine"inst_core_eval"`^deftm`
     (WF_REL_TAC`measure (sizeof o SND o SND)` >> simp[SIZEOF_VSUBST])
    val deftm2 = INST_def
      |> SPEC_ALL |> concl
      |> replace_term INST inst_eval
      |> replace_term INST_CORE ``inst_core_eval``
  in
    (th1,Define`^deftm2`)
  end

val inst_core_eval_thm = prove(
  ``∀env tyin tm. welltyped tm ⇒
    (inst_core_eval env tyin tm = INST_CORE env tyin tm)``,
  ho_match_mp_tac (theorem"inst_core_eval_ind") >>
  rpt conj_tac >>
  TRY(rw[inst_core_eval_def,INST_CORE_def]>>
      unabbrev_all_tac >> fs[] >> NO_TAC) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  imp_res_tac INST_CORE_Abs_thm >>
  asm_simp_tac pure_ss [inst_core_eval_def] >>
  pop_assum kall_tac >>
  srw_tac[][] >> fs[] >>
  unabbrev_all_tac >> fs[] >>
  IF_CASES_TAC >> fs[] >>
  IF_CASES_TAC >> fs[] >>
  last_x_assum mp_tac >>
  impl_tac >- (
    match_mp_tac VSUBST_WELLTYPED >>
    simp[] >> simp[Once has_type_cases] ) >>
  strip_tac >> rfs[])

val inst_eval_thm = store_thm("inst_eval_thm",
  ``∀tyin tm. welltyped tm ⇒ (INST tyin tm = inst_eval tyin tm)``,
  rw[INST_def,inst_eval_def,inst_core_eval_thm])

val term_image_inst_eval_thm = prove(
  ``EVERY welltyped h ⇒ (term_image (INST tyin) h = term_image (inst_eval tyin) h)``,
  Induct_on`h` >> simp[] >> rpt strip_tac >> fs[] >>
  simp[Once term_image_def] >>
  simp[Once term_image_def,SimpRHS] >>
  simp[inst_eval_thm])

val subst_rule = store_thm("subst_rule",
  ``∀thy h c.
    (thy,h) |- c ⇒
    EVERY (λp. type_ok (tysof thy) (FST p)) tyin ⇒
    EVERY (λ(s',s). ∃x ty. (s = Var x ty) ∧ (typeof s' = ty) ∧ term_ok (sigof thy) s') subst ⇒
    (thy,term_image (VSUBST subst) (term_image (inst_eval tyin) h)) |-
      (VSUBST subst (inst_eval tyin c))``,
  rw[] >>
  qspecl_then[`c`,`h`,`thy`,`tyin`]mp_tac inst_type >>
  simp[EVERY_MAP] >>
  imp_res_tac proves_term_ok >> fs[] >>
  `welltyped c ∧ EVERY welltyped h` by (
    fs[EVERY_MEM] >> metis_tac[term_ok_welltyped] ) >>
  simp[inst_eval_thm,term_image_inst_eval_thm] >>
  disch_then(match_mp_tac o MATCH_MP vsubst) >>
  fs[EVERY_MEM] >> rw[] >> res_tac >> fs[] >>
  metis_tac[term_ok_welltyped,WELLTYPED])

val exists_var_lemma = store_thm("exists_var_lemma",
  ``(∃x ty. (Var x1 ty1 = Var x ty) ∧ (typeof s' = ty) ∧ term_ok (sigof (thy:thy)) s') ⇔
    ((typeof s' = ty1) ∧ term_ok (sigof thy) s')``,
  rw[EQ_IMP_THM])

val thm = store_thm("thm",
  ``∀thy c' h c.
      (thy,h) |- c ⇒
      welltyped c' ⇒ ACONV c c' ⇒
      EVERY (λx. term_ok (sigof thy) x ∧ (typeof x = Bool)) h' ⇒
      hypset_ok h' ⇒
      EVERY (λx. EXISTS (ACONV x) h') h ⇒
      (thy,h') |- c'``,
  rw[] >>
  match_mp_tac proves_ACONV >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  fs[EVERY_MEM,EXISTS_MEM] >>
  metis_tac[WELLTYPED,term_ok_welltyped])

open holBoolSyntaxTheory

val truth = store_thm("truth",
  ``theory_ok thy ∧
    (Const (strlit "T") Bool === ^(rhs(concl TrueDef_def))) ∈ axsof thy
    ⇒
    (thy,[]) |- True``,
  rw[] >>
  imp_res_tac (proves_rules |> CONJUNCTS |> el 11) >>
  pop_assum(strip_assume_tac o MATCH_MP sym_equation) >>
  pop_assum(mp_tac o MATCH_MP eqMp_equation) >>
  qspecl_then[`Abs(Var(strlit"p")Bool)(Var(strlit"p")Bool)`,`thy`]mp_tac refl_equation >>
  imp_res_tac theory_ok_sig >>
  simp[term_ok_clauses] >>
  disch_then(fn th => disch_then(mp_tac o C MATCH_MP th)) >>
  simp[])

val eqT_intro = store_thm("eqT_intro",
  ``∀thy h c. (thy,h) |- c ∧
    (Const (strlit "T") Bool === ^(rhs(concl TrueDef_def))) ∈ axsof thy
    ⇒
    (thy,h) |- c === True``,
  rw[] >>
  imp_res_tac proves_term_ok >>
  imp_res_tac proves_theory_ok >> fs[] >>
  imp_res_tac truth >>
  qspecl_then[`c`,`True`]mp_tac deductAntisym_equation >>
  simp[GSYM AND_IMP_INTRO] >>
  first_x_assum(fn th => disch_then(mp_tac o C MATCH_MP th)) >>
  first_x_assum(fn th => disch_then(mp_tac o C MATCH_MP th)) >>
  simp[term_union_thm] >>
  Cases_on`term_remove True h = h`>>simp[] >> strip_tac >>
  imp_res_tac term_remove_exists >>
  qspecl_then[`thy`,`term_remove True h`,`c === True`,`c'`]mp_tac addAssum >>
  simp[] >>
  impl_tac >- fs[EVERY_MEM] >>
  metis_tac[term_union_insert_remove])

val eqT_elim = store_thm("eqT_elim",
  ``∀thy h c. (thy,h) |- c === True ⇒
    (Const (strlit "T") Bool === ^(rhs(concl TrueDef_def))) ∈ axsof thy
    ⇒
    (thy,h) |- c``,
  rw[] >>
  imp_res_tac proves_term_ok >>
  imp_res_tac proves_theory_ok >> fs[] >>
  imp_res_tac truth >>
  imp_res_tac sym_equation >>
  imp_res_tac eqMp_equation >>
  fs[term_union_thm])

val gen = store_thm("gen",
  ``∀thy h t x ty.
     is_true_sig (tmsof thy) ∧
     (Const (strlit "T") Bool === ^(rhs(concl TrueDef_def))) ∈ axsof thy ∧
     (Const (strlit "!") (Fun (Fun (Tyvar(strlit"A")) Bool) Bool) ===
       ^(rhs(concl ForallDef_def))) ∈ axsof thy ⇒
    (thy,h) |- t ⇒
     type_ok (tysof (thy:thy)) ty ⇒
     EVERY ($~ o VFREE_IN (Var x ty)) h
    ⇒ (thy,h) |- (Forall x ty t)``,
  rw[] >>
  imp_res_tac proves_theory_ok >> fs[] >>
  ASSUM_LIST(fn ls => assume_tac (MATCH_MP (proves_rules |> CONJUNCTS |> el 11) (CONJ (el 1 ls) (el 5 ls)))) >>
  first_x_assum(mp_tac o MATCH_MP (GEN_ALL subst_rule)) >>
  disch_then(qspecl_then[`[(ty,Tyvar(strlit"A"))]`,`[]`]mp_tac) >>
  simp[] >>
  CONV_TAC(LAND_CONV(RAND_CONV EVAL)) >>
  dep_rewrite.DEP_REWRITE_TAC[equation_intro] >>
  conj_tac >- EVAL_TAC >>
  strip_tac >>
  qspecl_then[`Abs (Var x ty) t`,`thy`]mp_tac refl_equation >>
  simp[term_ok_def] >>
  impl_keep_tac >- ( imp_res_tac proves_term_ok >> fs[] ) >>
  strip_tac >>
  last_x_assum(mp_tac o MATCH_MP appThm_equation) >>
  disch_then(fn th => last_x_assum (mp_tac o MATCH_MP th)) >>
  `welltyped t ∧ (typeof t = Bool)` by (
    imp_res_tac proves_term_ok >> fs[] >>
    metis_tac[term_ok_welltyped,WELLTYPED_LEMMA] ) >>
  simp[] >> strip_tac >>
  qmatch_assum_abbrev_tac`(thy,[]) |- Forall x ty t === Comb (Abs (Var u uy) b) l` >>
  qspecl_then[`u`,`uy`,`typeof b`,`b`,`thy`,`l`]mp_tac betaConv >>
  imp_res_tac theory_ok_sig >>
  simp[term_ok_clauses,Abbr`uy`,Abbr`l`] >>
  simp[GSYM AND_IMP_INTRO] >>
  impl_keep_tac >- (
    simp[Abbr`b`,term_ok_clauses] >>
    fs[term_ok_def,is_true_sig_def,term_ok_clauses] ) >>
  impl_keep_tac >- metis_tac[term_ok_welltyped] >> rfs[] >>
  qunabbrev_tac`b` >> qunabbrev_tac`u` >>
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV EVAL))) >>
  dep_rewrite.DEP_REWRITE_TAC[equation_intro] >>
  conj_tac >- (EVAL_TAC >> PROVE_TAC[]) >> strip_tac >>
  first_x_assum(mp_tac o MATCH_MP trans_equation) >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  simp[] >>
  `(thy,[]) |- True` by metis_tac[truth] >>
  qspecl_then[`thy`,`h`,`t`]mp_tac eqT_intro >>
  simp[] >> strip_tac >>
  qspecl_then[`h`,`t`,`True`,`thy`,`ty`,`x`]mp_tac absThm_equation >>
  simp[] >> rw[] >>
  pop_assum(mp_tac o (MATCH_MP eqMp_equation) o MATCH_MP sym_equation) >>
  disch_then(fn th => pop_assum(mp_tac o MATCH_MP th)) >>
  simp[term_union_thm] >> disch_then match_mp_tac >>
  simp[equation_def,ACONV_def,RACONV] >>
  match_mp_tac RACONV_REFL >>
  simp[])

val idspec = store_thm("idspec",
  ``∀thy h t x ty.
     is_true_sig (tmsof thy) ∧
     (Const (strlit "T") Bool === ^(rhs(concl TrueDef_def))) ∈ axsof thy ∧
     (Const (strlit "!") (Fun (Fun (Tyvar(strlit"A")) Bool) Bool) ===
       ^(rhs(concl ForallDef_def))) ∈ axsof thy ⇒
    (thy,h) |- (Forall x ty t)
    ⇒ (thy,h) |- t``,
  rw[] >>
  imp_res_tac proves_theory_ok >> fs[] >>
  ASSUM_LIST(fn ls => assume_tac (MATCH_MP (proves_rules |> CONJUNCTS |> el 11) (CONJ (el 1 ls) (el 3 ls)))) >>
  first_x_assum(mp_tac o MATCH_MP (GEN_ALL subst_rule)) >>
  disch_then(qspecl_then[`[(ty,Tyvar(strlit"A"))]`,`[]`]mp_tac) >>
  simp[] >>
  CONV_TAC(LAND_CONV(RAND_CONV EVAL)) >>
  dep_rewrite.DEP_REWRITE_TAC[equation_intro] >>
  conj_tac >- EVAL_TAC >>
  impl_keep_tac >- ( imp_res_tac proves_term_ok >> fs[term_ok_def] ) >>
  qmatch_assum_abbrev_tac`(thy,h) |- Comb t1 t2` >>
  qspecl_then[`t2`,`thy`]mp_tac refl_equation >>
  simp[] >>
  impl_keep_tac >- ( imp_res_tac proves_term_ok >> fs[term_ok_def] ) >>
  strip_tac >>
  disch_then(mp_tac o MATCH_MP appThm_equation) >>
  pop_assum(fn th => disch_then(mp_tac o C MATCH_MP th)) >>
  impl_tac >- ( imp_res_tac proves_term_ok >>
                      full_simp_tac std_ss [EVERY_DEF] >>
                      metis_tac[term_ok_welltyped]) >>
  disch_then(mp_tac o MATCH_MP eqMp_equation) >>
  first_assum(fn th => disch_then(mp_tac o C MATCH_MP th)) >>
  impl_tac >- simp[] >>
  simp[term_union_thm] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`(thy,h) |- Comb (Abs (Var P Pty) b) t2` >>
  qspecl_then[`P`,`Pty`,`Bool`,`b`,`thy`,`t2`]mp_tac betaConv >>
  impl_tac >- rw[] >>
  impl_tac >- ( imp_res_tac proves_term_ok >> fs[] ) >>
  impl_keep_tac >- ( simp[Abbr`b`] >> EVAL_TAC ) >>
  dep_rewrite.DEP_REWRITE_TAC[equation_intro] >>
  conj_tac >- simp[] >>
  disch_then(mp_tac o MATCH_MP eqMp_equation) >>
  first_assum(fn th => disch_then(mp_tac o C MATCH_MP th)) >>
  impl_tac >- simp[] >>
  simp[term_union_thm] >>
  unabbrev_all_tac >>
  CONV_TAC(LAND_CONV(RAND_CONV EVAL)) >>
  dep_rewrite.DEP_REWRITE_TAC[equation_intro] >>
  conj_tac >- ( simp[] >> imp_res_tac proves_term_ok >> fs[term_ok_def] ) >>
  disch_then(mp_tac o MATCH_MP appThm_equation) >>
  qspecl_then[`Var x ty`,`thy`]mp_tac refl_equation >>
  impl_tac >- simp[term_ok_def] >>
  disch_then(fn th => disch_then(mp_tac o C MATCH_MP th)) >>
  impl_tac >- (imp_res_tac proves_term_ok >> fs[term_ok_def]) >>
  simp[term_union_thm] >>
  qspecl_then[`t`,`thy`,`ty`,`x`]mp_tac betaConvVar >>
  impl_tac >- (imp_res_tac proves_term_ok >> fs[term_ok_def]) >>
  qspecl_then[`strlit"x"`,`ty`,`Bool`,`True`,`thy`,`Var x ty`]mp_tac betaConv >>
  impl_tac >- simp[] >>
  impl_tac >- (
    imp_res_tac proves_term_ok >>
    rfs[term_ok_def,is_true_sig_def] >>
    fs[type_ok_def]) >>
  impl_tac >- simp[] >>
  CONV_TAC(LAND_CONV EVAL) >>
  dep_rewrite.DEP_REWRITE_TAC[equation_intro] >>
  conj_tac >- EVAL_TAC >>
  disch_then(mp_tac o MATCH_MP eqT_elim) >>
  impl_tac >- simp[] >>
  strip_tac >>
  strip_tac >>
  disch_then(mp_tac o MATCH_MP sym_equation) >>
  disch_then(mp_tac o MATCH_MP eqMp_equation) >>
  first_assum(fn th => disch_then(mp_tac o C MATCH_MP th) >> (impl_tac >- simp[])) >>
  simp[term_union_thm] >>
  pop_assum(mp_tac o MATCH_MP eqMp_equation) >>
  disch_then(fn th => disch_then(mp_tac o MATCH_MP th)) >>
  impl_tac >- simp[] >>
  simp[term_union_thm])

val _ = export_theory()
