open HolKernel lcsymtacs
open miscLib reflectionLib holSyntaxSyntax 
open holSyntaxExtraTheory holBoolSyntaxTheory holBoolTheory
     holAxiomsSyntaxTheory holAxiomsTheory
     reflectionTheory

structure Map = Redblackmap

type context_state = {
  theory_ok_thm : thm,
  is_infinity_sig_thm : thm,
  models_thm : thm,
  signature_lookups : thm list,
  interpretation_lookups : thm list
  }

val theory_ok_hol_ctxt = prove(
  ``theory_ok (thyof hol_ctxt)``,
  match_mp_tac (MP_CANON extends_theory_ok) >>
  match_exists_tac (concl hol_extends_bool) >>
  simp[hol_extends_bool,bool_theory_ok])

val is_infinity_sig_hol_ctxt = prove(
  ``is_infinity_sig (sigof hol_ctxt)``,
  simp[hol_ctxt_def] >>
  match_mp_tac infinity_has_infinity_sig >>
  match_mp_tac select_has_select_sig >>
  match_mp_tac (MP_CANON is_bool_sig_extends) >>
  qexists_tac`mk_bool_ctxt init_ctxt` >>
  conj_asm2_tac >- (
    match_mp_tac eta_extends >>
    fs[is_bool_sig_def] ) >>
  match_mp_tac bool_has_bool_sig >>
  ACCEPT_TAC (MATCH_MP theory_ok_sig init_theory_ok |> SIMP_RULE std_ss[]))

val initial_context_state = {
  theory_ok_thm = theory_ok_hol_ctxt,
  is_infinity_sig_thm = is_infinity_sig_hol_ctxt,
  models_thm = CONJ (CONJUNCT1 hol_model_models)
                    (Q.ISPECL[`hol_ctxt`,`hol_model select in_ind`]subinterpretation_refl),
  signature_lookups =

  [],
  interpretation_lookups = []}

FLOOKUP (tmsof (sigof current_ctxt)) "blah" = SOME xxx
tmaof current_interpretation "name" = ...
print_find"select_model"
select_bool_interpretation
bool_interpretations
show_assums := true


val the_context_state = ref initial_context_state

want a database with:
  theory_ok (thyof current_ctxt)
  is_std_sig (sigof current_ctxt)
  current_interpretation models (thyof current_ctxt)
  for each constant in current_ctxt:
    lookup constant (sigof current_ctxt) = ...
    lookup constant current_interpretation = ... (connect to outer) ...
  the current_interpretation will include select_fun as a variable

val exists_equal_thm = prove(
  ``$? ($= x) ⇔ T``,
  `$= x = λz. x = z` by ( simp[FUN_EQ_THM] ) >>
  pop_assum SUBST1_TAC >> simp[])
val exists_REV_ASSOCD_thm = prove(
  ``∃i. ty = REV_ASSOCD (Tyvar a) i (Tyvar a)``,
  qexists_tac`[ty,Tyvar a]` >>
  EVAL_TAC )

val cs = list_compset()
val () = pairLib.add_pair_compset cs
val () = stringLib.add_string_compset cs
val () = optionLib.OPTION_rws cs
val () = computeLib.add_thms[
   CONJUNCT1 ALOOKUP_EQ_FLOOKUP,
   ALOOKUP_def] cs
val () = computeLib.add_thms
  [term_ok_def,type_ok_def,
   WELLTYPED_CLAUSES,typeof_def,
   CLOSED_def,VFREE_IN_def,
   codomain_def,
   consts_of_upd_def, types_of_upd_def, equation_def,
   hol_ctxt_def,mk_infinity_ctxt_def,mk_select_ctxt_def,
   mk_eta_ctxt_def,mk_bool_ctxt_def,init_ctxt_def] cs
val () = computeLib.add_datatype_info cs (valOf(TypeBase.fetch``:type``))
val () = computeLib.add_datatype_info cs (valOf(TypeBase.fetch``:term``))

val IND_SUC_def = definition"IND_SUC_def"
val name = "IND_SUC"
val tm = term_to_deep(rhs(concl IND_SUC_def))
val theory_ok_th = theory_ok_hol_ctxt

val tm_def = IND_SUC_def

(term_to_cert``ARB``)
hol_ctxt_def
show_assums := true

fun mk_ConstDef_th theory_ok_th tm_def =
  let
    val name = tm_def |> concl |> lhs |> dest_const |> fst
    val tm = tm_def |> concl |> rhs |> term_to_deep
    val ctxt = theory_ok_th |> concl |> funpow 5 rand
    val updates_th = ConstDef_updates
      |> SPECL [fromMLstring name,tm,ctxt]
    val goal:goal = ([],fst(dest_imp(concl updates_th)))
    val goal_th = TAC_PROOF(goal,
      conj_tac >- ACCEPT_TAC theory_ok_th >>
      conj_tac >- (
        CONV_TAC (computeLib.CBV_CONV cs) >>
        simp[exists_equal_thm,exists_REV_ASSOCD_thm] ) >>
      conj_tac >- EVAL_TAC >>
      conj_tac >- (
        CONV_TAC (computeLib.CBV_CONV cs) >>
        simp[] >> rw[] >>
        rpt(
          Q.PAT_ABBREV_TAC`eq = ((A:string) = B)` >>
          Cases_on`eq`>>fs[markerTheory.Abbrev_def]>>
          rw[]) ) >>
      EVAL_TAC >> simp[])
    val updates_th = MP updates_th goal_th

  in
  end

mk_ConstDef_th theory_ok_hol_ctxt IND_SUC_def

mk_ConstDef_th theory_ok_hol_ctxt "IND_SUC" (term_to_deep(rhs(concl IND_SUC_def)))
IND_SUC_def
!the_record

print_find"ConstDef"

val witness_thm =
  ``(thyof (mk_select_ctxt (mk_bool_ctxt init_ctxt)),[]) |-
    Comb

fun mk_TypeDefn_th witness_thm name abs rep =
  let
    val (pred,witness) = dest_Comb(rand(concl witness_thm))

    val ctxt =
``TypeDefn name 
``(thyof ctxt,[]) |- Comb pred witness``
``(TypeDefn name pred abs rep) updates ctxt``
fun mk_TypeDefn 
el 5 (CONJUNCTS updates_rules)

