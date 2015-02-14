open HolKernel boolLib bossLib numTheory Parse OpenTheoryMap
val _ = new_theory"ZERO_REP"

val _ = OpenTheory_const_name{const={Name="SUC_REP",Thy="num"},name=(["HOL4"],"SUC_REP")}

val ZERO_REP = mk_var("ZERO_REP",ind)
val tm = ``!y. ~(^ZERO_REP = SUC_REP y)``
val goal = ([mk_eq(ZERO_REP,mk_select(ZERO_REP,tm))],tm)
val ZERO_REP_EXISTS = save_thm("ZERO_REP_EXISTS",
  TAC_PROOF(goal,
    POP_ASSUM SUBST1_TAC THEN
    SELECT_ELIM_TAC THEN
    CONJ_TAC THEN1 (
      SUC_REP_DEF |> CONJUNCT2
      |> CONV_RULE (
        RAND_CONV(
          RATOR_CONV(REWR_CONV ONTO_DEF) THENC
          BETA_CONV) THENC
        NOT_FORALL_CONV THENC
        QUANT_CONV NOT_EXISTS_CONV)
      |> ACCEPT_TAC) THEN
    GEN_TAC THEN DISCH_THEN ACCEPT_TAC));

val _ = export_theory()
