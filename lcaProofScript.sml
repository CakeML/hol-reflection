open HolKernel boolLib bossLib lcsymtacs
open lcaTheory reflectionLib
val _ = new_theory"lcaProof"

(*
intermediate theorem:

``LCA (SUC l) UNIV ⇒
  ∃mem. is_set_theory mem ∧ (∃inf. is_infinite mem inf) ∧
        termsem (sigof LCA_ctxt) (LCA_int) someval
          [LCA ^(quote l) UNIV] = True``

for someval, want:
  type valuation to map "U" to the Q from the definition of LCA
  term valuation to map "l" to the l from the master theorem
  otherwise, whatever
for LCA_int, want:
  what build_interpretation builds for LCA_ctxt and this term


master theorem...

``∀n. (^thy,[]) |- [∀l. LCA l UNIV ⇒ ^^phi ^(quote n) l] ⇒
    ∀l. LCA (SUC l) UNIV ⇒ ^phi n l``

where thy extends (thyof LCA_ctxt)

to prove master theorem:
1. assume Provable(LCA l ==> phi l)
2. assume LCA (SUC l)
3. get termsem (LCA l) = True from 2 and intermediate
4. get termsem (LCA l ==> phi l) = True from 1 and soundness
5. combine 3 and 4 to get termsem (phi l) = True
6. termsem_cert (phi l) to get termsem (phi l) = True <=> phi l
7. combine 5 and 6

*)

val _ = export_theory()
