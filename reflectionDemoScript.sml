open HolKernel boolLib bossLib lcsymtacs
open reflectionLib
val _ = new_theory"reflectionDemo"

val _ = save_thm("example",prop_to_loeb_hyp``0 = 1``)

val _ = export_theory()
