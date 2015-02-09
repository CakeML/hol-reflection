open HolKernel boolLib bossLib lcsymtacs
open lcaTheory reflectionLib
val _ = new_theory"lcaProof"

(*
``LCA (UNIV:'U set) (SUC n) ⇒
  ∃mem. is_set_theory mem ∧ (∃inf. is_infinite mem inf) ∧
        termsem ... "?m. LCA m ^(quote n)" = True``

for ..., want:
type valuation to map "U" to the Q from the definition of LCA
otherwise, what build_interpretation builds
*)

val _ = export_theory()
