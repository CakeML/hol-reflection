open HolKernel boolLib bossLib lcsymtacs
open pred_setTheory cardinalTheory
open setSpecTheory miscLib
val _ = new_theory"lca"

val strong_limit_cardinal_def = Define`
  strong_limit_cardinal X ⇔
    ∀x. x ⊆ X ∧ ¬(cardleq X x) ⇒
          ¬(cardleq X (POW x))`

val bijection_exists_def = Define`
  bijection_exists X =
    ∃f. BIJ f X { x | x ⊆ X ∧ ¬(cardleq X x)}`

(* probably not true :( *)
val strong_limit_cardinal_bijection_exists = store_thm("strong_limit_cardinal_bijection_exists",
  ``∀X. strong_limit_cardinal X ⇒ bijection_exists X``,
  rw[strong_limit_cardinal_def] >>
  rw[BIJ_IFF_INV]>>
  cheat)

(*
≺
*)

(* not true in general; make it just about UNIV:'U set
val lemma = prove(
  ``∀A X f. A ≺ X ∧ (∀a. a ∈ A ⇒ f a ≺ X) ⇒
           BIGUNION (IMAGE f A) ≺ X``,
  cheat)
*)

val bijection_implies_set_theory = store_thm("bijection_implies_set_theory",
  ``strong_limit_cardinal (UNIV:'U set) ⇒
    ∃(mem:'U reln). is_set_theory mem``,
  strip_tac >>
  imp_res_tac strong_limit_cardinal_bijection_exists >>
  fs[bijection_exists_def] >>
  qexists_tac`λx y. f y x` >>
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
    qmatch_abbrev_tac`f (g z) x = R` >>
    `f (g z) = z` suffices_by rw[Abbr`R`] >>
    first_x_assum match_mp_tac >>
    rw[Abbr`z`] >>
    match_mp_tac (INST_TYPE[beta|->``:'U``]cardleq_lt_trans) >>
    qexists_tac`f y` >> simp[] >>
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
    cheat) >>
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

val _ = export_theory()
