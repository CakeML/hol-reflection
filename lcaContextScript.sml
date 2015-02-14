open HolKernel boolLib bossLib lcsymtacs
open pred_setTheory cardinalTheory reflectionTheory
open lcaTheory reflectionLib holDerivationLib
val _ = new_theory"lcaContext"

val _ = Globals.max_print_depth := 15

val uneta = prove(
  ``(∀x. f x = g x) ⇔ f = \x. g x``,
  rw[FUN_EQ_THM])
fun preprocess def =
  SIMP_RULE (std_ss++boolSimps.ETA_ss) [uneta] def

fun mk_eqs tm =
  let
    fun mk tm =
      pairSyntax.mk_pair(fst(holSyntaxSyntax.dest_Var(rand(rand(rator tm)))),rand tm)
    val (ls,ty) = listSyntax.dest_list tm
  in
    listSyntax.mk_list(map mk ls,
      pairSyntax.mk_prod(mlstringSyntax.mlstring_ty,ty))
  end

fun MAP_EVERY_CONV conv tm =
  (if listSyntax.is_nil tm then ALL_CONV
   else LAND_CONV conv THENC RAND_CONV (MAP_EVERY_CONV conv))
  tm

val Equal_cong = prove(
  ``(ty1 = ty2) ⇒ (Equal ty1 = Equal ty2)``,
  rw[])

fun EVAL_Equal_typeof tm =
  let
    val th = EVAL_typeof (rand(rator(rand(rand tm))))
  in
    MATCH_MP Equal_cong th
  end

val unmk_eq_conv =
  LAND_CONV(RAND_CONV EVAL_typeof) THENC
  REWR_CONV holSyntaxTheory.equation_def THENC
  LAND_CONV(LAND_CONV(EVAL_Equal_typeof))

open holSyntaxTheory holSyntaxExtraTheory holExtensionTheory holConstrainedExtensionTheory

val mem = reflectionLib.mem

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

(* SUC_REP *)
val SUC_REP_witness =
  let
    val istr = TextIO.openIn("opentheory/suc-rep.art")
  in
    istr |> readArticle hol_ctxt_reader
    |> Net.listItems |> hd
    before TextIO.closeIn istr
  end
val inner_th = SUC_REP_witness
val eqs = inner_th |> concl |> rator |> rand |> rand |> mk_eqs
val prop = inner_th |> concl |> rand
val inner_upd = ``ConstSpec ^eqs ^prop``
val ctxt = ``hol_ctxt``
val extends_init_thm = hol_extends_init
val cs = listLib.list_compset()
val () = pairLib.add_pair_compset cs
val updates_thm = prove(
  ``^inner_upd updates ^ctxt``,
  match_mp_tac (updates_rules |> CONJUNCTS |> el 3) >>
  conj_tac >- (
    CONV_TAC(LAND_CONV(RAND_CONV(computeLib.CBV_CONV cs))) >>
    CONV_TAC(LAND_CONV(RAND_CONV(MAP_EVERY_CONV unmk_eq_conv))) >>
    ACCEPT_TAC SUC_REP_witness ) >>
  conj_tac >- ( EVAL_TAC >> rw[] >> PROVE_TAC[] ) >>
  conj_tac >- ( EVAL_TAC >> rw[] ) >>
  conj_tac >- ( EVAL_TAC >> rw[] ) >>
  EVAL_TAC)
val theory_ok = prove(
  ``theory_ok (thyof ^ctxt)``,
    match_mp_tac(MATCH_MP extends_theory_ok extends_init_thm) >>
    rw[init_theory_ok] )
val sound_update_thm = prove(
  ``is_set_theory ^mem ⇒
    sound_update ^ctxt ^inner_upd``,
  strip_tac >>
  ho_match_mp_tac (UNDISCH new_specification_correct) >>
  conj_asm1_tac >- ACCEPT_TAC theory_ok >>
  (updates_thm |> SIMP_RULE bool_ss [updates_cases,update_distinct,update_11] |> strip_assume_tac) >>
  rpt conj_tac >>
  first_assum ACCEPT_TAC) |> UNDISCH
val constrainable_thm = prove(
  ``constrainable_update ^inner_upd``,
  rw[constrainable_update_def] >> rw[] >>
  rw[conexts_of_upd_def] >>
  rw[listTheory.EVERY_MAP] >>
  unabbrev_all_tac >> rw[] >>
  TRY(pop_assum mp_tac) >>
  EVAL_TAC >> rw[])

val (upd:update) = {
  sound_update_thm = sound_update_thm,
  constrainable_thm = constrainable_thm,
  updates_thm = updates_thm,
  extends_init_thm = extends_init_thm,
  consts = [``SUC_REP``],
  tys = [],
  axs = [numTheory.SUC_REP_DEF]}

val extends_init_thm =
  MATCH_MP updates_extends_trans
    (CONJ updates_thm extends_init_thm)

val ctxt = rand(rator(concl extends_init_thm))

val SUC_REP_name = ``strlit"SUC_REP"``
val FLOOKUP_SUC_REP =
  ``FLOOKUP (tmsof (thyof ^ctxt)) ^SUC_REP_name`` |> EVAL

val FLOOKUP_tmsof = MATCH_MP FLOOKUP_tmsof_updates updates_thm
val FLOOKUP_tysof = MATCH_MP FLOOKUP_tysof_updates updates_thm
val proves = MATCH_MP updates_proves updates_thm

val term_ok_reduce = prove(
  ``∀tm.
    term_ok (sigof (thyof ^ctxt)) tm ⇒
    ($~ o (VFREE_IN (Const ^SUC_REP_name ^(rand(rhs(concl FLOOKUP_SUC_REP)))))) tm ⇒
    term_ok (sigof (thyof ^(rand ctxt))) tm``,
  ho_match_mp_tac term_induction >> rw[term_ok_def] >>
  rfs[finite_mapTheory.FLOOKUP_UPDATE] >>
  BasicProvers.EVERY_CASE_TAC >> rw[] >> fs[] >>
  PROVE_TAC[])

fun reduce_term_ok th =
  let
    val th1 = MATCH_MP term_ok_reduce th
    val th2 = EVAL_not_VFREE_IN (fst(dest_imp(concl th1)))
  in
    MP th1 th2
  end

val (reader:reader) = {
  theory_ok =
    MATCH_MP (MATCH_MP extends_theory_ok extends_init_thm)
    init_theory_ok,
  const = (fn name =>
    if name = SUC_REP_name then FLOOKUP_SUC_REP
    else MATCH_MP FLOOKUP_tmsof (#const hol_ctxt_reader name)),
  typeOp = (fn name =>
    MATCH_MP FLOOKUP_tysof (#typeOp hol_ctxt_reader name)),
  axiom = (fn term_oks =>
    MATCH_MP proves (#axiom hol_ctxt_reader (List.map reduce_term_ok term_oks)))
  }

(* IN *)
val def = IN_DEF
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
(* INJ *)
val def = preprocess INJ_DEF
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
(* cardleq *)
val def = preprocess cardleq_def
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
(* UNIV *)
val def = UNIV_DEF
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
(* SUBSET *)
val def = preprocess SUBSET_DEF
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
(* POW *)
val POW_alt = METIS_PROVE[EXTENSION,IN_DEF,IN_POW]``∀s x. POW s x ⇔ x ⊆ s``
val def = preprocess POW_alt
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
(* plan for building context:

LCA_def: ConstSpec LCA_exists
Proof: LCA_exists (from num_Axiom)
ConstDef: strongly_inaccessible_alt
ConstDef: countable_def
ConstDef: strong_limit_cardinal_def
ConstDef: my_regular_cardinal_alt
(* countable *)
ConstDef: countable_def
(* POW *)
ConstDef: POW_alt
(* ⊆ *)
ConstDef: SUBSET_DEF
(* UNIV *)
ConstDef: UNIV_DEF
(* ≺ ( overload for ≼ ) *)
ConstDef: cardleq_def
ConstDef: INJ_DEF
ConstDef: IN_DEF
(* recursive defn *)
Proof: somehow get something like num_Axiom from the below
(* 0, SUC *)
ConstDef: SUC_DEF
ConstDef: ZERO_DEF
(* :num *)
Proof: TypeDefn EXISTS_NUM_REP
Const_Def: IS_NUM_REP
Proof: ZERO_REP: ConstSpec ZERO_REP_EXISTS
Proof: SUC_REP: ConstSpec infinity_ax
hol_ctxt
*)

(* dependencies:
  stuff in HOL model (T, ∃, ∧, etc.)
  ≺, countable -- (expands to INJ, or further)
  ∈, ⊆, UNIV, POW -- (expands if necessary)
  0, SUC
  machinery for making recursive definitions...?

  strongly_inaccessible_alt
  my_regular_cardinal_alt
  strong_limit_cardinal_def
  countable_def
*)

val _ = export_theory()
