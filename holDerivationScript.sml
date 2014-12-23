open HolKernel boolLib bossLib lcsymtacs listTheory miscLib holSyntaxTheory holSyntaxExtraTheory
val _ = new_theory"holDerivation"

val term_ok_Abs = store_thm("term_ok_Abs",
  ``term_ok (sigof thy) b ∧ type_ok (tysof thy) ty ⇒
      term_ok (sigof thy) (Abs (Var v ty) b)``,
  rw[term_ok_def])

val term_ok_Comb = store_thm("term_ok_Comb",
  ``term_ok (sigof thy) x ∧ term_ok (sigof thy) f ∧
    welltyped (Comb f x) ⇒
    term_ok (sigof thy) (Comb f x)``,
  rw[term_ok_def])

val term_ok_Const = store_thm("term_ok_Const",
  ``(FLOOKUP (tmsof thy) name = SOME ty0) ∧
    type_ok (tysof thy) ty ⇒
    is_instance ty0 ty ⇒
    term_ok (sigof thy) (Const name ty)``,
  rw[term_ok_def])

val term_ok_Var = store_thm("term_ok_Var",
  ``∀name. type_ok (tysof thy) ty ⇒
    term_ok (sigof thy) (Var name ty)``,
  rw[term_ok_def])

val type_ok_Tyapp = store_thm("type_ok_Tyapp",
  ``(FLOOKUP (tysof thy) name = SOME a) ⇒
    EVERY (type_ok (tysof thy)) args ⇒
    (LENGTH args = a)
    ⇒ type_ok (tysof thy) (Tyapp name args)``,
  rw[type_ok_def] >>
  asm_simp_tac (std_ss++boolSimps.ETA_ss)[])

val exists_rty_lemma = store_thm("exists_rty_lemma",
  ``(∃rty. Fun dty rty1 = Fun dty rty) = T``, rw[])

val absThm = save_thm("absThm",
  proves_rules |> CONJUNCTS |> el 1
  |> ONCE_REWRITE_RULE[CONJ_COMM]
  |> REWRITE_RULE[GSYM AND_IMP_INTRO,NOT_EXISTS])

val appThm = save_thm("appThm",
  proves_rules |> CONJUNCTS |> el 8
  |> REWRITE_RULE[GSYM AND_IMP_INTRO])

val axiom = save_thm("axiom",
  proves_rules |> CONJUNCTS |> el 11
  |> REWRITE_RULE[GSYM AND_IMP_INTRO])

val assume = store_thm("assume",
  ``∀p thy. theory_ok thy ⇒
    term_ok (sigof thy) p ⇒
    (typeof p = Bool) ⇒
    (thy,[p]) |- p``,
  rpt strip_tac >>
  metis_tac[proves_rules |> CONJUNCTS |> el 2,
            holSyntaxExtraTheory.term_ok_welltyped,
            holSyntaxExtraTheory.WELLTYPED])

val betaConv = store_thm("betaConv",
  ``∀x ty t thy.
    theory_ok thy ⇒
    term_ok (sigof thy) (Comb (Abs (Var x ty) t) (Var x ty)) ⇒
    (thy,[]) |- (Comb (Abs (Var x ty) t) (Var x ty) === t)``,
  strip_tac >>
  rw[term_ok_def] >>
  imp_res_tac(proves_rules |> CONJUNCTS |> el 3) >>
  fs[])

val deductAntisym = save_thm("deductAntisym",
  proves_rules |> CONJUNCTS |> el 4)

val eqMp = save_thm("eqMp",
  proves_rules |> CONJUNCTS |> el 5
  |> REWRITE_RULE[GSYM AND_IMP_INTRO])

val refl = save_thm("refl",
  proves_rules |> CONJUNCTS |> el 9)

val sym = store_thm("sym",
  ``∀thyh p q. thyh |- p === q ⇒ thyh |- q === p``,
  rpt strip_tac >>
  imp_res_tac proves_theory_ok >>
  imp_res_tac proves_term_ok >>
  imp_res_tac theory_ok_sig >>
  `(FST thyh,[]) |- p === p` by (
    match_mp_tac refl >> simp[] >>
    fs[term_ok_equation]) >>
  `(FST thyh,[]) |- Equal (typeof p) === Equal (typeof p)` by (
    match_mp_tac refl >> simp[holBoolSyntaxTheory.term_ok_clauses] >>
    fs[term_ok_equation] >>
    metis_tac[term_ok_type_ok] ) >>
  qspecl_then[`[]`,`SND thyh`,`Equal (typeof p)`,`p`]mp_tac appThm >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >> simp[] >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  simp[] >> discharge_hyps_keep
    >- fs[term_ok_equation,EQUATION_HAS_TYPE_BOOL] >>
  simp[term_union_thm] >>
  strip_tac >> mp_tac appThm >>
  Cases_on`thyh`>>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  full_simp_tac std_ss [] >>
  disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
  fs[term_ok_equation] >>
  simp[GSYM equation_def,term_union_thm] >>
  qpat_assum`typeof p = typeof q`(assume_tac o SYM) >>
  simp[GSYM equation_def] >>
  fs[EQUATION_HAS_TYPE_BOOL] >>
  metis_tac[eqMp,term_union_thm,ACONV_REFL])

val proveHyp = store_thm("proveHyp",
  ``∀thy h1 c1 h2 c2. (thy,h1) |- c1 ∧ (thy,h2) |- c2 ⇒
      (thy,term_union h2 (term_remove c2 h1)) |- c1``,
  rw[] >>
  imp_res_tac proves_term_ok >>
  imp_res_tac proves_theory_ok >> fs[] >>
  qspecl_then[`c2`,`c1`,`h2`,`h1`,`thy`]mp_tac deductAntisym >>
  simp[] >> strip_tac >>
  qmatch_assum_abbrev_tac`(thy,h3) |- c2 === c1` >>
  qspecl_then[`h3`,`h2`,`c2`,`c2`,`c1`,`thy`]mp_tac eqMp >>
  simp[] >>
  strip_tac >>
  match_mp_tac proves_ACONV >>
  first_assum(match_exists_tac o concl) >>
  simp[] >>
  conj_tac >- metis_tac[welltyped_def] >>
  unabbrev_all_tac >>
  simp[EVERY_MEM,EXISTS_MEM] >>
  conj_tac >> gen_tac >>
  disch_then(mp_tac o MATCH_MP MEM_term_union_imp) >>
  strip_tac >>
  TRY(pop_assum(mp_tac o MATCH_MP MEM_term_union_imp)) >>
  TRY strip_tac >>
  imp_res_tac MEM_term_remove_imp >>
  TRY(fs[EVERY_MEM]>>NO_TAC) >>
  metis_tac[MEM_term_union,hypset_ok_term_union,hypset_ok_term_remove,ACONV_REFL])

val _ = export_theory()
