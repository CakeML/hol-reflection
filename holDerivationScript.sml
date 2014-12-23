open HolKernel boolLib bossLib lcsymtacs listTheory miscLib holSyntaxTheory holSyntaxExtraTheory
val _ = new_theory"holDerivation"

(* TODO: move *)
val hypset_ok_ALL_DISTINCT = store_thm("hypset_ok_ALL_DISTINCT",
  ``∀h. hypset_ok h ⇒ ALL_DISTINCT h``,
  simp[hypset_ok_def] >> Induct >>
  simp[MATCH_MP sortingTheory.SORTED_EQ transitive_alpha_lt] >>
  rw[] >> strip_tac >> res_tac >> fs[alpha_lt_def] >>
  metis_tac[totoTheory.cpn_distinct,ACONV_REFL,ACONV_eq_orda])

val hypset_ok_eq = store_thm("hypset_ok_eq",
  ``∀h1 h2.  hypset_ok h1 ∧ hypset_ok h2 ⇒
            ((h1 = h2) ⇔ (set h1 = set h2))``,
  rw[EQ_IMP_THM] >>
  fs[pred_setTheory.EXTENSION] >>
  metis_tac[hypset_ok_ALL_DISTINCT,
            sortingTheory.PERM_ALL_DISTINCT,
            sortingTheory.SORTED_PERM_EQ,
            hypset_ok_def,
            transitive_alpha_lt,
            antisymmetric_alpha_lt])

val term_remove_nil = store_thm("term_remove_nil[simp]",
  ``term_remove a [] = []``,
  rw[Once term_remove_def])

val term_union_sing_lt = store_thm("term_union_sing_lt",
  ``∀ys x. EVERY (λy. alpha_lt x y) ys ⇒ (term_union [x] ys = x::ys)``,
  Induct >> simp[term_union_thm] >> rw[] >> fs[] >>
  fs[alpha_lt_def])

val MEM_term_union_first = store_thm("MEM_term_union_first",
  ``∀h1 h2 t. hypset_ok h1 ∧ hypset_ok h2 ∧ MEM t h1 ⇒ MEM t (term_union h1 h2)``,
  Induct >> simp[hypset_ok_cons] >>
  gen_tac >> Induct >> simp[term_union_thm] >>
  rw[hypset_ok_cons] >>
  BasicProvers.CASE_TAC >> rw[] >>
  disj2_tac >>
  first_x_assum match_mp_tac >>
  rw[hypset_ok_cons])
(* -- *)

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

(* TODO: add to term_ok_clauses? *)
val term_ok_Equal = prove(
  ``is_std_sig sig ⇒
    (term_ok sig (Equal ty) ⇔ type_ok (tysof sig) ty)``,
  rw[term_ok_def,type_ok_def] >>
  fs[is_std_sig_def] >> rw[EQ_IMP_THM] >>
  qexists_tac`[(ty,Tyvar(strlit"A"))]` >>
  EVAL_TAC)
(* -- *)

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
    match_mp_tac refl >> simp[term_ok_Equal] >>
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

val proves_concl_ACONV = store_thm("proves_concl_ACONV",
  ``∀thyh c c'. thyh |- c ∧ ACONV c c' ∧ welltyped c' ⇒ thyh |- c'``,
  rw[] >>
  qspecl_then[`c'`,`FST thyh`]mp_tac refl >>
  imp_res_tac proves_theory_ok >>
  imp_res_tac proves_term_ok >> fs[] >>
  imp_res_tac term_ok_aconv >> pop_assum kall_tac >> simp[] >>
  Cases_on`thyh`>>fs[]>>
  metis_tac[eqMp,term_union_thm,ACONV_SYM] )

val addAssum = store_thm("addAssum",
  ``∀thy h c a. (thy,h) |- c ∧ term_ok (sigof thy) a ∧ (typeof a = Bool) ⇒
      (thy,term_union [a] h) |- c``,
  rw[] >>
  ho_match_mp_tac (MP_CANON eqMp) >>
  map_every qexists_tac[`c`,`c`] >> simp[] >>
  qspecl_then[`a`,`thy`]mp_tac assume >>
  imp_res_tac proves_theory_ok >> fs[] >> strip_tac >>
  Cases_on`ACONV (c === c) a` >- (
    qspecl_then[`c === c`,`thy`]mp_tac refl >>
    imp_res_tac theory_ok_sig >>
    imp_res_tac proves_term_ok >>
    fs[term_ok_equation] >> strip_tac >>
    imp_res_tac eqMp >>
    fs[term_union_thm] ) >>
  qspecl_then[`c`,`thy`]mp_tac refl >>
  imp_res_tac proves_term_ok >> fs[] >> strip_tac >>
  qspecl_then[`a`,`c === c`,`[a]`,`[]`,`thy`]mp_tac deductAntisym >>
  simp[term_union_thm] >>
  `term_remove (c === c) [a] = [a]` by (
    simp[Once term_remove_def,GSYM ACONV_eq_orda] ) >>
  rw[] >>
  imp_res_tac eqMp >>
  metis_tac[ACONV_REFL,term_union_idem])

(*
val addAssums = store_thm("addAssums",
  ``∀thy as h c.
    (thy,h) |- c ∧ EVERY (λa. term_ok (sigof thy) a ∧ (typeof a = Bool)) as ∧ hypset_ok as ⇒
    (thy,term_union as h) |- c``,
  gen_tac >> Induct >> simp[term_union_thm] >> rw[] >> fs[hypset_ok_cons] >>
  imp_res_tac addAssum >>
*)

(*
val proves_ACONV = store_thm("proves_ACONV",
  ``∀thy h' c' h c.
      (thy,h) |- c ⇒
      hypset_ok h' ∧ welltyped c' ∧ ACONV c c' ∧
      EVERY (λx. EXISTS (ACONV x) h') h ∧
      EVERY (λx. term_ok (sigof thy) x ∧ x has_type Bool) h'
      ⇒ (thy,h') |- c'``,
  gen_tac >> Induct >> rw[hypset_ok_cons] >>
  imp_res_tac proves_theory_ok >>
  imp_res_tac proves_term_ok >> fs[] >-
    metis_tac[proves_concl_ACONV] >>
  Cases_on`ACONV c h` >- (
    qsuff_tac`(thy,h::h') |- h`>-
      metis_tac[proves_concl_ACONV,ACONV_SYM,ACONV_TRANS] >>
    qspecl_then[`h`,`thy`]mp_tac assume >>
    imp_res_tac WELLTYPED_LEMMA >> simp[] >>
    addAssum

  qspecl_then[`c`,`h`,`h''`,`[h]`,`thy`]mp_tac deductAntisym >>
  discharge_hyps >- (
    metis_tac[WELLTYPED_LEMMA,assume] ) >>
  addAssum

  rpt gen_tac >> strip_tac
    deductAntisym
              print_find"term_ok_A"

val proves_hypset_ACONV = store_thm("proves_hypset_ACONV",
  ``∀thy h1 h2 c. (thy,h1) |- c ∧ LIST_REL ACONV h1 h2 ⇒ (thy,h2) |- c``,
  gen_tac >> Induct >> rw[] >>
  imp_res_tac proves_term_ok >> fs[hypset_ok_cons] >>
  qmatch_assum_rename_tac`LIST_REL ACONV h1 h2`[] >>
  qmatch_assum_rename_tac`ACONV a1 a2`[] >>
  qspecl_then[`a1`,`a2`,`a1::h1`,`[a1]`,`thy`]mp_tac deductAntisym
  qspecl_then[`[]`,`
  `(thy,[]) |- 
  `(thy,h::h1) |- y
  deductAntisym
  eqMp

val proves_ACONV = store_thm("proves_ACONV",
  ``∀thyh c. thyh |- c ⇒
      ∀h' c'.
        EVERY (λp. EXISTS (ACONV p) (SND thyh)) h' ∧
        ACONV c c' ⇒
        (FST thyh,h') |- c'``,
  ho_match_mp_tac proves_ind >> simp[] >>
    or: prove ADD_ASSUM and aconv transformers as derived rules
        to do this all in one go *)

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
  qsuff_tac`term_union h3 h2 = term_union h2 (term_remove c2 h1)` >- rw[] >>
  qmatch_abbrev_tac`l1 = l2` >>
  `hypset_ok l1 ∧ hypset_ok l2` by metis_tac[hypset_ok_term_union,hypset_ok_term_remove] >>
  simp[hypset_ok_eq,Abbr`l1`,Abbr`l2`]
*)

val _ = export_theory()
