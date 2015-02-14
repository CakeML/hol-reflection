open HolKernel boolLib bossLib numTheory Parse OpenTheoryMap
val _ = new_theory"ZERO_REP"

val _ = OpenTheory_const_name{const={Name="SUC_REP",Thy="num"},name=(["HOL4"],"SUC_REP")}
val _ = OpenTheory_const_name{const={Name="ZERO_REP",Thy="num"},name=(["HOL4"],"ZERO_REP")}

val ZERO_REP_EXISTS = store_thm("ZERO_REP_EXISTS",
  Term`?z. !y. ~(z = SUC_REP y)`,
  Q.X_CHOOSE_THEN `zrep` ASSUME_TAC ((CONV_RULE NOT_FORALL_CONV o
                                      REWRITE_RULE [ONTO_THM] o
                                      CONJUNCT2) SUC_REP_DEF) THEN
  POP_ASSUM (ASSUME_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
  Q.EXISTS_TAC `zrep` THEN POP_ASSUM ACCEPT_TAC);

val _ = export_theory()
