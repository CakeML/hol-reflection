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
  ``theory_ok thy ⇒
    term_ok (sigof thy) p ⇒
    (typeof p = Bool) ⇒
    (thy,[p]) |- p``,
  rpt strip_tac >>
  metis_tac[proves_rules |> CONJUNCTS |> el 2,
            holSyntaxExtraTheory.term_ok_welltyped,
            holSyntaxExtraTheory.WELLTYPED])

val betaConv = store_thm("betaConv",
  ``theory_ok thy ⇒
    term_ok (sigof thy) (Comb (Abs (Var x ty) t) (Var x ty)) ⇒
    (thy,[]) |- (Comb (Abs (Var x ty) t) (Var x ty) === t)``,
  strip_tac >>
  rw[term_ok_def] >>
  imp_res_tac(proves_rules |> CONJUNCTS |> el 3) >>
  fs[])

val deductAntisym = save_thm("deductAntisym",
  proves_rules |> CONJUNCTS |> el 4
  |> REWRITE_RULE[combinTheory.o_DEF])

val eqMp = save_thm("eqMp",
  proves_rules |> CONJUNCTS |> el 5
  |> REWRITE_RULE[GSYM AND_IMP_INTRO])

val refl = save_thm("refl",
  proves_rules |> CONJUNCTS |> el 9)

val _ = export_theory()
