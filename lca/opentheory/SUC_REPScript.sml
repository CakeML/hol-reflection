open HolKernel boolLib bossLib lcsymtacs
val _ = new_theory"SUC_REP"

val SUC_REP = mk_var("SUC_REP",ind-->ind)
val (x,t) = boolSyntax.dest_exists(concl INFINITY_AX)
val SUC_REP_th = TAC_PROOF(([``^SUC_REP = @f. ^t``],
    subst [x|->SUC_REP] t),
    pop_assum SUBST1_TAC >>
    SELECT_ELIM_TAC >>
    conj_tac >- ACCEPT_TAC INFINITY_AX >>
    gen_tac >> strip_tac >>
    conj_tac >> first_assum ACCEPT_TAC)
val _ = save_thm("SUC_REP_th",SUC_REP_th)

val _ = export_theory()
