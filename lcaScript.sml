open HolKernel boolLib bossLib lcsymtacs
open pred_setTheory cardinalTheory
open ordinalTheory wellorderTheory
open setSpecTheory miscLib
val _ = new_theory"lca"

val strong_limit_cardinal_def = Define`
  strong_limit_cardinal X ⇔
    ∀x. x ⊆ X ∧ x ≺ X ⇒ POW x ≺ X`

val limitation_of_size_def = Define`
  limitation_of_size X ⇔
    ∃f. BIJ f X { x | x ⊆ X ∧ x ≺ X}`

val regular_cardinal_def = Define`
  regular_cardinal X ⇔
    ∀x f.
      x ⊆ X ∧ x ≺ X ∧ (∀a. a ∈ x ⇒ f a ⊆ X ∧ f a ≺ X) ⇒
        BIGUNION (IMAGE f x) ≺ X`

(*
val cardinal_def = Define`
  cardinal (X:α set) = oleast (k:α ordinal). preds k ≈ X`

val cardbij_def = new_specification("cardbij_def",["cardbij"],
  prove(``∃f. BIJ f (preds (cardinal X)) X``,
    rw[cardinal_def] >>
    rw[cardeq_def] >>
    qho_match_abbrev_tac`∃f. BIJ f (preds ($oleast P)) X` >>
    qho_match_abbrev_tac`Q ($oleast P)` >>
    match_mp_tac oleast_intro >>
    simp[Abbr`P`,Abbr`Q`] >>
    qspec_then`X`strip_assume_tac allsets_wellorderable >> rw[] >>
type_of``mkOrdinal``

(λ(x,y). (f x, f y) WIN wo)
val minWO_exists = prove(
  ``∀s. ∃wo. elsOf wo = s ∧
             (∀x. x ∈ s ⇒ iseg wo x ≺ s)``,
  gen_tac >>
  qspec_then`s`strip_assume_tac allsets_wellorderable >>
  qho_match_abbrev_tac`∃wo. P wo ∧ Q wo` >>
  Cases_on`Q wo` >- metis_tac[] >>
  qunabbrev_tac`Q` >> pop_assum mp_tac >>
  simp[] >>
  strip_tac >>
  `s ≈ iseg wo x` by (
    match_mp_tac cardleq_ANTISYM >> simp[] >>
    simp[cardleq_def] >>
    qexists_tac`I` >>
    simp[INJ_DEF] >>
    simp[iseg_def] >>
    metis_tac[WIN_elsOf] ) >>
  `∃f. BIJ f (iseg wo x) s` by metis_tac[cardeq_def,BIJ_LINV_BIJ] >>
  qabbrev_tac`wo2 = rrestrict (IMAGE (f ## f) (strict (destWO wo)))  s`>>
  qexists_tac`mkWO wo2` >>
  `wellorder wo2` by (
    simp[Abbr`wo2`] >>
    qspec_then`wo`strip_assume_tac wellorder_cases >>
    simp[destWO_mkWO] >>
  simp[Abbr`P`] >>
  conj_tac >- (
    simp[elsOf_def]
    m``destWO(mkWO x)``
    destWO_mkWO
  simp[elsOf_wobound] >>

  elsOf_def
  f"wrange"
  overload_info_for"wrange"


type_of``mkOrdinal``
m``oleast x. x ≈ X``
f"oleast"
  fs[Abbr`P`,Abbr`Q`] >>
  qspec_then`
  qexists_tac
  f"elsOf"
  Cases_on

val aWO_def = new_specification

val has_supremum_def = Define`
  has_supremum x X ⇔
  ∃y. 

val regular_cardinal_supremums = prove(
  ``∀X. regular_cardinal X ⇒
      ∀x. x ⊆ X ∧ x ≺ X ⇒
*)

val strong_regular_limitation = store_thm("strong_regular_limitation",
  ``strong_limit_cardinal X ∧ regular_cardinal X ⇒
    limitation_of_size X``,
  rw[strong_limit_cardinal_def,regular_cardinal_def,limitation_of_size_def] >>
  simp[GSYM cardeq_def] >>
  match_mp_tac cardleq_ANTISYM >>
  conj_tac >- (
    simp[cardleq_def] >>
    qexists_tac`λa. {a}` >>
    simp[INJ_DEF] >> rw[] >>
    spose_not_then strip_assume_tac >>
    Cases_on`∃b. b ∈ X ∧ a ≠ b` >> fs[] >- metis_tac[] >>
    `X = {a}` by (
      simp[EXTENSION] >>
      metis_tac[] ) >>
    fs[] >>
    last_x_assum(qspec_then`{}`mp_tac) >>
    simp[CARDLEQ_CARD,POW_DEF] ) >>
  (* SET_SQUARED_CARDEQ_SET *)
  simp[Once cardleq_def] >>
  last_assum mp_tac >>
  CONV_TAC(LAND_CONV(QUANT_CONV(RAND_CONV(RAND_CONV(REWR_CONV cardleq_def))))) >>
  cheat)

val implies_set_theory = store_thm("implies_set_theory",
  ``strong_limit_cardinal (UNIV:'U set) ∧
    regular_cardinal (UNIV:'U set) ∧
    limitation_of_size (UNIV:'U set)
    ⇒
    ∃(mem:'U reln). is_set_theory mem``,
  strip_tac >>
  fs[limitation_of_size_def] >>
  qexists_tac`combin$C f` >>
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
    qmatch_abbrev_tac`f (g z) a = R` >>
    `f (g z) = z` suffices_by rw[Abbr`R`] >>
    first_x_assum match_mp_tac >>
    rw[Abbr`z`] >>
    match_mp_tac (INST_TYPE[beta|->``:'U``]cardleq_lt_trans) >>
    qexists_tac`f x` >> simp[] >>
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
    qexists_tac`λx. g (BIGUNION (IMAGE f (f x)))` >>
    simp[] >>
    rpt gen_tac >>
    qmatch_abbrev_tac`f (g z) c ⇔ R` >>
    `f (g z) = z` suffices_by (
      rw[Abbr`z`,PULL_EXISTS,IN_DEF] ) >>
    first_x_assum match_mp_tac >>
    rw[Abbr`z`] >>
    fs[regular_cardinal_def]) >>
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
