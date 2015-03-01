open HolKernel boolLib bossLib lcsymtacs
     relationTheory
     holSyntaxTheory holSyntaxLibTheory holSyntaxLib holSyntaxExtraTheory
     reflectionTheory reflectionLib
     lcaCtxtTheory lcaProofTheory lcaLib

val _ = new_theory"lcaDemo"

val _ = Globals.max_print_depth := 15

val (EVAL_type_ok0,EVAL_term_ok0) =
  EVAL_type_ok_term_ok
    EVAL (MATCH_MP theory_ok_sig theory_ok_lca |> SIMP_RULE std_ss[])
val th = prove(``tysof lca_ctxt = tysof(sigof lca_ctxt)``,rw[])
val EVAL_type_ok =
  (RATOR_CONV(RAND_CONV(REWR_CONV th))) THENC EVAL_type_ok0
val EVAL_term_ok =
  EVAL_term_ok0 THENC
  SIMP_CONV (srw_ss()) [
    tyvar_inst_exists,
    tyvar_inst_exists2,
    tyvar_inst_exists2_diff]

val lca_ctxt = unpack_ctxt lca_ctxt_thm
val ctxt = rhs(concl lca_ctxt_def)
val extends_lca_thm = ``^ctxt extends lca_ctxt``
  |> SIMP_CONV std_ss [extends_def,RTC_REFL,GSYM lca_ctxt_def]
  |> EQT_ELIM
val phi = ``λl n. SUC n = l``
val term_ok_phi =
  ``term_ok (sigof ^ctxt) ^(term_to_deep phi)``
  |> ((REWRITE_CONV[GSYM lca_ctxt_def]) THENC EVAL_term_ok)
  |> EQT_ELIM
val typeof_phi =
  ``typeof ^(term_to_deep phi)`` |> EVAL_typeof

val example1 = save_thm("example1",
  build_master_theorem lca_ctxt extends_lca_thm term_ok_phi typeof_phi phi)

val _ = export_theory()
