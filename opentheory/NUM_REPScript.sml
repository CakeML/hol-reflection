open HolKernel boolLib bossLib numTheory Parse OpenTheoryMap
val _ = new_theory"NUM_REP"

val _ = OpenTheory_const_name{const={Name="ZERO_REP",Thy="num"},name=(["HOL4"],"ZERO_REP")}
val _ = OpenTheory_const_name{const={Name="SUC_REP",Thy="num"},name=(["HOL4"],"SUC_REP")}
val _ = OpenTheory_const_name{const={Name="IS_NUM_REP",Thy="num"},name=(["HOL4"],"IS_NUM_REP")}

val uneta = prove(
  ``(∀x. f x = g x) ⇔ (f = \x. g x)``,
  SIMP_TAC std_ss [FUN_EQ_THM])
fun preprocess def =
  SIMP_RULE (std_ss++boolSimps.ETA_ss) [uneta] def

val IS_NUM_REP_DEF =
  preprocess IS_NUM_REP

val () = delete_proof IS_NUM_REP_DEF

val NUM_REP_ZERO = store_thm("NUM_REP_ZERO",
  ``IS_NUM_REP ZERO_REP``,
  CONV_TAC(RATOR_CONV(REWR_CONV(IS_NUM_REP_DEF)) THENC BETA_CONV) THEN
  GEN_TAC THEN STRIP_TAC)

val _ = export_theory()
