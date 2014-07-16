open HolKernel boolLib bossLib lcsymtacs
open reflectionLib
val _ = new_theory"reflectionDemo"

val () = show_assums := true

val p = ``0 = 1``
val res1 = prop_to_loeb_hyp p
val p = ``∀y. (λx. F) z``
val res2 = prop_to_loeb_hyp p
val p = ``(∀y. (λx. F) z) ⇔ ¬z``
val res3 = prop_to_loeb_hyp p

open basicReflectionLib miscTheory listSimps stringSimps
open setSpecTheory holSemanticsTheory reflectionTheory pairSyntax listSyntax stringSyntax
open holBoolTheory holBoolSyntaxTheory holSyntaxExtraTheory

val base_tyval_tm = ``base_tyval``

val (update_list_tm,mk_update_list,dest_update_list,is_update_list)
  = syntax_fns "misc" 3 dest_triop mk_triop "UPDATE_LIST"

val is_type_valuation_tm = ``is_type_valuation``
val is_set_theory_mem = ``is_set_theory ^mem``

val mk_is_in = mk_monop``is_in``

val tyval_asms = filter (can (match_term ``^tyval x = range y``)) o hyp

fun mk_tyval th =
  let
    val asms = tyval_asms th
    fun mk_kv eq =
      let
        val (l,r) = dest_eq eq
      in
        mk_pair(rand l,r)
      end
    val pairs = map mk_kv asms
    val pairs = mk_list(pairs,mk_prod(string_ty,U))
    val tyval = list_mk_icomb(update_list_tm,[base_tyval_tm,pairs])
    val is_ins = map (mk_is_in o rand o rand) asms
    val goal = (is_set_theory_mem::is_ins,mk_comb(is_type_valuation_tm,tyval))
    val th = TAC_PROOF(goal,
      match_mp_tac is_type_valuation_update_list >>
      conj_tac >- ACCEPT_TAC base_tyval_def >>
      SIMP_TAC (std_ss ++ LIST_ss) [] >>
      rpt conj_tac >>
      match_mp_tac inhabited_range >>
      first_assum ACCEPT_TAC)
  in
    SIMP_RULE std_ss [UPDATE_LIST_THM] th
  end

val tyval_th = mk_tyval res2
val r3 = res2 |> INST[tyval|->(rand(concl tyval_th))]
val simpths = mapfilter (QCHANGED_CONV (SIMP_CONV (std_ss++LIST_ss++STRING_ss) [combinTheory.APPLY_UPDATE_THM])) (hyp r3)
val phyps = map EQT_ELIM simpths
val r4 = foldl (uncurry PROVE_HYP) r3 phyps
val r5 = Q.INST[`ctxt`|->`mk_bool_ctxt init_ctxt`] r4
val bool_insts =
  bool_sig_instances
  |> Q.GEN`sig`
  |> Q.SPEC`sigof(mk_bool_ctxt init_ctxt)`
  |> SIMP_RULE std_ss []
val is_bool_sig_goal:goal = ([],fst(dest_imp(concl bool_insts)))
val is_bool_sig_th = TAC_PROOF(is_bool_sig_goal,
  match_mp_tac bool_has_bool_sig >>
  ACCEPT_TAC (MATCH_MP theory_ok_sig init_theory_ok |> SIMP_RULE std_ss []))
val is_std_sig_goal:goal = ([],first (can (match_term ``is_std_sig x``)) (hyp r5))
val is_std_sig_th = TAC_PROOF(is_std_sig_goal,
  match_mp_tac is_bool_sig_std >>
  ACCEPT_TAC is_bool_sig_th)
val r6 = PROVE_HYP is_std_sig_th r5
val bool_insts = MATCH_MP bool_insts is_bool_sig_th
val bool_sig = is_bool_sig_def
  |> Q.SPEC`sigof(mk_bool_ctxt init_ctxt)`
  |> SIMP_RULE std_ss [is_bool_sig_th,is_std_sig_th]
val simpths = mapfilter (QCHANGED_CONV (SIMP_CONV (std_ss++LIST_ss++STRING_ss)
  [combinTheory.APPLY_UPDATE_THM,bool_insts,bool_sig,is_instance_refl])) (hyp r6)
val r7 = foldl (uncurry (C simplify_assum)) r6 simpths |> PROVE_HYP TRUTH
val simpths = mapfilter (QCHANGED_CONV (SIMP_CONV (std_ss) [is_valuation_def,tyval_th])) (hyp r7)
val r8 = foldl (uncurry (C simplify_assum)) r7 simpths

val _ = save_thm("example",r8)

val _ = export_theory()
