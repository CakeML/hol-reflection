open HolKernel boolLib bossLib numTheory Parse OpenTheoryMap
val _ = new_theory"NUM_REP"

val _ = OpenTheory_const_name{const={Name="ZERO_REP",Thy="num"},name=(["HOL4"],"ZERO_REP")}
val _ = OpenTheory_const_name{const={Name="SUC_REP",Thy="num"},name=(["HOL4"],"SUC_REP")}
val _ = OpenTheory_const_name{const={Name="IS_NUM_REP",Thy="num"},name=(["HOL4"],"IS_NUM_REP")}

val NUM_REP_ZERO = store_thm("NUM_REP_ZERO",
  ``IS_NUM_REP ZERO_REP``,
  CONV_TAC(REWR_CONV(IS_NUM_REP)) THEN
  GEN_TAC THEN STRIP_TAC)

val _ = export_theory()
