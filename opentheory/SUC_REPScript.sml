open HolKernel boolLib bossLib lcsymtacs
val _ = new_theory"SUC_REP"

val SUC_REP = mk_var("SUC_REP",ind-->ind)
val (x,t) = boolSyntax.dest_exists(concl INFINITY_AX)
val SUC_REP_th = TAC_PROOF(([``^SUC_REP = @f. ^t``],
    subst [x|->SUC_REP] t), metis_tac[INFINITY_AX])
val _ = save_thm("SUC_REP_th",SUC_REP_th)

val _ = export_theory()
