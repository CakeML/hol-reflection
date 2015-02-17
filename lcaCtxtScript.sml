open HolKernel boolLib bossLib lcsymtacs miscLib
open pred_setTheory cardinalTheory
open lcaTheory reflectionTheory reflectionLib
open holSyntaxTheory holSyntaxExtraTheory holSyntaxLib holSyntaxSyntax
open holExtensionTheory holConstrainedExtensionTheory
open holDerivationTheory holDerivationLib

val _ = new_theory"lcaCtxt"

val _ = Globals.max_print_depth := 15

(* stolen from holDerivationScript.sml - TODO: move? *)
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
(* -- *)

val uneta = prove(
  ``(∀x. f x = g x) ⇔ f = \x. g x``,
  rw[FUN_EQ_THM])
fun preprocess def =
  SIMP_RULE (pure_ss++boolSimps.ETA_ss) [uneta] def

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

val mem = reflectionLib.mem

val IMP_TRANS1 = METIS_PROVE[]``(P ==> Q) ==> (Q ==> R) ==> (P ==> R)``
val IMP_TRANS2 = METIS_PROVE[]``(∀h c. P h c ==> Q h c) ==> (∀h c. Q h c ==> R h c) ==> (∀h c. P h c ==> R h c)``

val ctxt:update list = []

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
val inner_ctxt = ``hol_ctxt``
val extends_init_thm = hol_extends_init
val cs = listLib.list_compset()
val () = pairLib.add_pair_compset cs
val updates_thm = prove(
  ``^inner_upd updates ^inner_ctxt``,
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
  ``theory_ok (thyof ^inner_ctxt)``,
    match_mp_tac(MATCH_MP extends_theory_ok extends_init_thm) >>
    rw[init_theory_ok] )
val sound_update_thm = prove(
  ``is_set_theory ^mem ⇒
    sound_update ^inner_ctxt ^inner_upd``,
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
val ctxt = upd::ctxt
val inner_ctxt = rand(rator(concl extends_init_thm))

(* reader for ZERO_REP *)

val SUC_REP_name = ``strlit"SUC_REP"``
val FLOOKUP_SUC_REP =
  ``FLOOKUP (tmsof (thyof ^inner_ctxt)) ^SUC_REP_name`` |> EVAL

val FLOOKUP_tmsof = MATCH_MP FLOOKUP_tmsof_updates updates_thm
val FLOOKUP_tysof = MATCH_MP FLOOKUP_tysof_updates updates_thm
val proves = MATCH_MP updates_proves updates_thm

val SUC_REP_ty = rand(rhs(concl FLOOKUP_SUC_REP))

val term_ok_reduce = prove(
  ``∀tm.
    term_ok (sigof (thyof ^inner_ctxt)) tm ⇒
    ($~ o (VFREE_IN (Const ^SUC_REP_name ^SUC_REP_ty))) tm ⇒
    term_ok (sigof (thyof ^(rand inner_ctxt))) tm``,
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

val SUC_REP_ax =
  replace_term
    (mk_Var(SUC_REP_name,SUC_REP_ty))
    (mk_Const(SUC_REP_name,SUC_REP_ty))
  prop

val theory_ok =
  MATCH_MP (MATCH_MP extends_theory_ok extends_init_thm)
  init_theory_ok

val SUC_REP_axiom = prove(
  ``(thyof ^inner_ctxt,[]) |- ^SUC_REP_ax``,
  match_mp_tac (last (CONJUNCTS proves_rules)) >>
  conj_tac >- ACCEPT_TAC theory_ok >>
  EVAL_TAC)

val (zero_rep_reader:reader) = {
  theory_ok = theory_ok,
  const = (fn name =>
    if name = SUC_REP_name then FLOOKUP_SUC_REP
    else MATCH_MP FLOOKUP_tmsof (#const hol_ctxt_reader name)),
  typeOp = (fn name =>
    MATCH_MP FLOOKUP_tysof (#typeOp hol_ctxt_reader name)),
  axiom = (fn term_oks =>
    if aconv (rand(concl SUC_REP_axiom)) (rand(concl(hd term_oks)))
    then SUC_REP_axiom
    else MATCH_MP proves (#axiom hol_ctxt_reader (List.map reduce_term_ok term_oks)))
  }

(* ZERO_REP *)
val ZERO_REP_witness =
  let
    val istr = TextIO.openIn("opentheory/zero-rep.art")
  in
    istr |> readArticle zero_rep_reader
    |> Net.listItems |> hd
    before TextIO.closeIn istr
  end
val inner_th = ZERO_REP_witness
val eqs = inner_th |> concl |> rator |> rand |> rand |> mk_eqs
val prop = inner_th |> concl |> rand
val inner_upd = ``ConstSpec ^eqs ^prop``
val updates_thm = prove(
  ``^inner_upd updates ^inner_ctxt``,
  match_mp_tac (updates_rules |> CONJUNCTS |> el 3) >>
  conj_tac >- (
    CONV_TAC(LAND_CONV(RAND_CONV(computeLib.CBV_CONV cs))) >>
    CONV_TAC(LAND_CONV(RAND_CONV(MAP_EVERY_CONV unmk_eq_conv))) >>
    ACCEPT_TAC ZERO_REP_witness ) >>
  conj_tac >- ( EVAL_TAC >> rw[] >> PROVE_TAC[] ) >>
  conj_tac >- ( EVAL_TAC >> rw[] ) >>
  conj_tac >- ( EVAL_TAC >> rw[] ) >>
  EVAL_TAC)
val theory_ok = prove(
  ``theory_ok (thyof ^inner_ctxt)``,
    match_mp_tac(MATCH_MP extends_theory_ok extends_init_thm) >>
    rw[init_theory_ok] )
val sound_update_thm = prove(
  ``is_set_theory ^mem ⇒
    sound_update ^inner_ctxt ^inner_upd``,
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
  consts = [``ZERO_REP``],
  tys = [],
  axs = [numTheory.ZERO_REP_DEF]}
val extends_init_thm =
  MATCH_MP updates_extends_trans
    (CONJ updates_thm extends_init_thm)
val ctxt = upd::ctxt
val inner_ctxt = rand(rator(concl extends_init_thm))

(* IS_NUM_REP *)
val def = preprocess numTheory.IS_NUM_REP
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
val ctxt = upd::ctxt
val inner_ctxt = rand(rator(concl extends_init_thm))

(* reader for :num *)

val ZERO_REP_name = ``strlit"ZERO_REP"``
val FLOOKUP_ZERO_REP =
  ``FLOOKUP (tmsof (thyof ^inner_ctxt)) ^ZERO_REP_name`` |> EVAL
val ZERO_REP_ty = rand(rhs(concl FLOOKUP_ZERO_REP))

val IS_NUM_REP_name = ``strlit"IS_NUM_REP"``
val FLOOKUP_IS_NUM_REP =
  ``FLOOKUP (tmsof (thyof ^inner_ctxt)) ^IS_NUM_REP_name`` |> EVAL
val IS_NUM_REP_ty = rand(rhs(concl FLOOKUP_IS_NUM_REP))

val FLOOKUP_tmsof = MATCH_MP
  (MATCH_MP IMP_TRANS1 (MATCH_MP FLOOKUP_tmsof_updates updates_thm))
  (MATCH_MP FLOOKUP_tmsof_updates (#updates_thm upd))
val FLOOKUP_tysof = MATCH_MP
  (MATCH_MP IMP_TRANS1 (MATCH_MP FLOOKUP_tysof_updates updates_thm))
  (MATCH_MP FLOOKUP_tysof_updates (#updates_thm upd))

val proves = HO_MATCH_MP
  (HO_MATCH_MP IMP_TRANS2 (MATCH_MP updates_proves updates_thm))
  (MATCH_MP updates_proves (#updates_thm upd))

val term_ok_reduce = prove(
  ``∀tm.
    term_ok (sigof (thyof ^inner_ctxt)) tm ⇒
    ($~ o (VFREE_IN (Const ^ZERO_REP_name ^ZERO_REP_ty))) tm ⇒
    ($~ o (VFREE_IN (Const ^IS_NUM_REP_name ^IS_NUM_REP_ty))) tm ⇒
    term_ok (sigof (thyof ^(rand (rand inner_ctxt)))) tm``,
  ho_match_mp_tac term_induction >> rw[term_ok_def] >>
  rfs[finite_mapTheory.FLOOKUP_UPDATE] >>
  BasicProvers.EVERY_CASE_TAC >> rw[] >> fs[] >>
  PROVE_TAC[])

fun reduce_term_ok th =
  let
    val th1 = MATCH_MP term_ok_reduce th
    val th2 = EVAL_not_VFREE_IN (fst(dest_imp(concl th1)))
    val th3 = MP th1 th2
    val th4 = EVAL_not_VFREE_IN (fst(dest_imp(concl th3)))
  in
    MP th3 th4
  end

val ZERO_REP_ax =
  replace_term
    (mk_Var(ZERO_REP_name,ZERO_REP_ty))
    (mk_Const(ZERO_REP_name,ZERO_REP_ty))
  prop

val theory_ok =
  MATCH_MP (MATCH_MP extends_theory_ok extends_init_thm)
  init_theory_ok

val ZERO_REP_axiom = prove(
  ``(thyof ^inner_ctxt,[]) |- ^ZERO_REP_ax``,
  match_mp_tac (last (CONJUNCTS proves_rules)) >>
  conj_tac >- ACCEPT_TAC theory_ok >>
  EVAL_TAC)

val IS_NUM_REP_ax =
  term_to_deep(concl(def))

val IS_NUM_REP_axiom = prove(
  ``(thyof ^inner_ctxt,[]) |- ^IS_NUM_REP_ax``,
  match_mp_tac (last (CONJUNCTS proves_rules)) >>
  conj_tac >- ACCEPT_TAC theory_ok >>
  EVAL_TAC)

val (num_reader:reader) = {
  theory_ok = theory_ok,
  const = (fn name =>
    if name = ZERO_REP_name then FLOOKUP_ZERO_REP
    else if name = IS_NUM_REP_name then FLOOKUP_IS_NUM_REP
    else MATCH_MP FLOOKUP_tmsof (#const zero_rep_reader name)),
  typeOp = (fn name =>
    MATCH_MP FLOOKUP_tysof (#typeOp zero_rep_reader name)),
  axiom = (fn term_oks =>
    if aconv (rand(concl ZERO_REP_axiom)) (rand(concl(hd term_oks)))
    then ZERO_REP_axiom
    else if aconv (rand(concl IS_NUM_REP_axiom)) (rand(concl(hd term_oks)))
    then IS_NUM_REP_axiom
    else MATCH_MP proves (#axiom zero_rep_reader (List.map reduce_term_ok term_oks)))
  }

(* :num *)
val NUM_REP_witness =
  let
    val istr = TextIO.openIn("opentheory/num-rep.art")
  in
    istr |> readArticle num_reader
    |> Net.listItems |> hd
    before TextIO.closeIn istr
  end
val inner_upd = ``TypeDefn (strlit"num") ^(mk_Const(IS_NUM_REP_name,IS_NUM_REP_ty))
                    (strlit"ABS_num") (strlit"REP_num")``
val updates_thm = prove(
  ``^inner_upd updates ^inner_ctxt``,
  match_mp_tac (updates_rules |> CONJUNCTS |> el 5) >>
  exists_tac(mk_Const(ZERO_REP_name,ZERO_REP_ty)) >>
  conj_tac >- ACCEPT_TAC NUM_REP_witness >>
  conj_tac >- (EVAL_TAC >> rw[]) >>
  EVAL_TAC)
val sound_update_thm = prove(
  ``is_set_theory ^mem ⇒
      sound_update ^inner_ctxt ^inner_upd``,
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
val (upd:update) = {
  sound_update_thm  = sound_update_thm,
  constrainable_thm = constrainable_thm,
  updates_thm = updates_thm,
  extends_init_thm = extends_init_thm,
  tys = [``:num``],
  consts = [``ABS_num``,``REP_num``],
  axs = map SPEC_ALL (CONJUNCTS numTheory.num_ISO_DEF) }
val extends_init_thm =
  MATCH_MP updates_extends_trans
    (CONJ updates_thm extends_init_thm)
val ctxt = upd::ctxt
val inner_ctxt = rand(rator(concl extends_init_thm))

(* ZERO *)
val def = numTheory.ZERO_DEF
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
val ctxt = upd::ctxt

(* SUC *)
val def = preprocess numTheory.SUC_DEF
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
val ctxt = upd::ctxt

(* LESS *)
val def = preprocess prim_recTheory.LESS_DEF
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
val ctxt = upd::ctxt

(* IN *)
val def = IN_DEF
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
val ctxt = upd::ctxt
(* INJ *)
val def = preprocess INJ_DEF
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
val ctxt = upd::ctxt
(* cardleq *)
val def = preprocess cardleq_def
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
val ctxt = upd::ctxt
(* UNIV *)
val def = UNIV_DEF
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
val ctxt = upd::ctxt
(* SUBSET *)
val def = preprocess SUBSET_DEF
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
val ctxt = upd::ctxt
(* POW *)
val POW_alt = METIS_PROVE[EXTENSION,IN_DEF,IN_POW]``∀s x. POW s x ⇔ x ⊆ s``
val def = preprocess POW_alt
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
val ctxt = upd::ctxt
(* my_regular_cardinal *)
val def = preprocess (Q.GEN`X`my_regular_cardinal_alt)
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
val ctxt = upd::ctxt
(* strong_limit_cardinal *)
val def = preprocess strong_limit_cardinal_def
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
val ctxt = upd::ctxt
(* countable *)
val def = preprocess countable_def
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
val ctxt = upd::ctxt
(* strongly_inaccessible *)
val def = preprocess(Q.GEN`X`strongly_inaccessible_alt)
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
val ctxt = upd::ctxt
(* LCA *)
val def = preprocess LCA_alt
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
val ctxt = upd::ctxt

val _ = Feedback.set_trace "TheoryPP.include_docs" 0
val _ = save_thm("lca_ctxt_thm", pack_ctxt ctxt)
val _ = save_thm("lca_extends_init", extends_init_thm)
val _ = export_theory()
