open HolKernel boolLib bossLib lcsymtacs listTheory combinTheory
open holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
open holConsistencyTheory
open holExtensionTheory holConstrainedExtensionTheory
open reflectionTheory reflectionLib

val _ = new_theory"reflectionDemo"
val () = Globals.max_print_depth := 13

(* example 1: defining products on top of hol_ctxt *)
val ctxt = ``hol_ctxt``
val pred_tm = ``λp. ∃x y. p = λa b. (a=x) ∧ (b=y)``
val pred_inner = term_to_deep pred_tm
val inner_upd = ``TypeDefn (strlit"prod") ^pred_inner (strlit"ABS_prod") (strlit"REP_prod")``
val updates_thm = prove(
  ``^inner_upd updates ^ctxt``,
  match_mp_tac (updates_rules |> CONJUNCTS |> el 5) >>
  exists_tac(term_to_deep``λa b. (a=x) ∧ (b=y)``) >>
  conj_tac >- ( cheat ) >>
  conj_tac >- ( EVAL_TAC >> rw[] >> metis_tac[] ) >>
  EVAL_TAC)
val sound_update_thm = prove(
  ``is_set_theory ^mem ⇒
    sound_update ^ctxt ^inner_upd``,
  strip_tac >>
  ho_match_mp_tac (UNDISCH new_type_definition_correct) >>
  (updates_thm |> SIMP_RULE (srw_ss()) [updates_cases] |> strip_assume_tac) >>
  simp[] >> PROVE_TAC[]) |> UNDISCH
val constrainable_thm = prove(
  ``constrainable_update ^inner_upd``,
  REWRITE_TAC[constrainable_update_def] >>
  qexists_tac`set(tvars(HD(axioms_of_upd ^inner_upd)))` >>
  conj_tac >- (EVAL_TAC >> rw[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- ( EVAL_TAC >> rw[] ) >>
  REWRITE_TAC[mlstring_sort_SET_TO_LIST_set_tvars] >>
  EVAL_TAC >> rw[] >> fs[] >> rw[] >>
  rpt(fs[subtype_Tyvar,subtype_Tyapp] >> rw[]))
val extends_init_thm = hol_extends_init
val upd:update = {
  sound_update_thm  = sound_update_thm,
  constrainable_thm = constrainable_thm,
  updates_thm = updates_thm,
  extends_init_thm = extends_init_thm,
  tys = [``:('a,'b)prod``],
  consts = [``ABS_prod``,``REP_prod``],
  axs = map SPEC_ALL (CONJUNCTS pairTheory.ABS_REP_prod) }
val tys = [``:'c#bool``]
val substs = [[alpha|->bool,beta|->alpha],[alpha|->gamma,beta|->(bool-->bool)]]
val consts =  map (C inst ``ABS_prod``) substs
val example1 = save_thm("example1",build_interpretation [upd] tys consts)

(* example 2: defining K on top of hol_ctxt *)
val ctxt = ``hol_ctxt``
val tm = term_to_deep(rhs(concl K_DEF))
val inner_upd = ``ConstDef (strlit"K") ^tm``
val updates_thm = prove(
  ``^inner_upd updates hol_ctxt``,
  ho_match_mp_tac ConstDef_updates >>
  conj_tac >- (
    rw[hol_ctxt_def,fhol_ctxt_def,hol_theory_ok] ) >>
  conj_tac >- ( EVAL_TAC >> rw[] >> EVAL_TAC ) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- ( EVAL_TAC >> rw[] >> PROVE_TAC[] ) >>
  EVAL_TAC >> rw[])
val sound_update_thm = prove(
  ``is_set_theory ^mem ⇒
    sound_update ^ctxt ^inner_upd``,
  strip_tac >>
  ho_match_mp_tac (UNDISCH new_specification_correct) >>
  conj_asm1_tac >- (
    rw[hol_ctxt_def,fhol_ctxt_def,hol_theory_ok] ) >>
  conj_tac >- (
    simp_tac (srw_ss()) [] >>
    match_mp_tac (el 2 (CONJUNCTS proves_rules)) >>
    conj_tac >- rw[] >>
    conj_tac >- (
      simp_tac std_ss [EQUATION_HAS_TYPE_BOOL] >>
      simp_tac (srw_ss())[] ) >>
    imp_res_tac theory_ok_sig >>
    simp[term_ok_equation] >>
    simp[term_ok_def,type_ok_def] >>
    EVAL_TAC ) >>
  (updates_thm |> SIMP_RULE (srw_ss()) [updates_cases] |> strip_assume_tac) >>
  simp_tac (srw_ss())[] >>
  rpt conj_tac >>
  first_assum ACCEPT_TAC) |> UNDISCH
val constrainable_thm = prove(
  ``constrainable_update ^inner_upd``,
  rw[constrainable_update_def] >> rw[] >>
  rw[conexts_of_upd_def] >>
  rw[listTheory.EVERY_MAP] >>
  unabbrev_all_tac >> rw[] >>
  TRY(pop_assum mp_tac) >>
  EVAL_TAC)
val upd:update = {
  sound_update_thm  = sound_update_thm,
  constrainable_thm = constrainable_thm,
  updates_thm = updates_thm,
  extends_init_thm = hol_extends_init,
  tys = [],
  consts = [``K``],
  axs = [combinTheory.K_DEF] }
val substs = [[alpha|->bool,beta|->alpha],[alpha|->gamma,beta|->(bool-->bool)]]
val consts =  map (C inst ``K``) substs
val tys:hol_type list = []
val ctxt:update list = []
val example2 = save_thm("example2",build_interpretation (upd::ctxt) tys consts)

val _ = export_theory()
