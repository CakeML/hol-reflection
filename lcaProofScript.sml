open HolKernel boolLib bossLib lcsymtacs miscLib
open lcaTheory reflectionLib
open lcaCtxtTheory

val _ = new_theory"lcaProof"

val _ = Globals.max_print_depth := 15

val lca_ctxt = unpack_ctxt lca_ctxt_thm
val lca_inner_ctxt = lca_extends_init |> concl |> rator |> rand
val _ = overload_on("lca_ctxt",lca_inner_ctxt)

(*
val test = termsem_cert lca_ctxt ``T``
*)


val _ = overload_on("Num", ``Tyapp(strlit"num")[]``)
val quote_def = Define`
  (quote 0 = Const (strlit"0") Num) ∧
  (quote (SUC n) = Comb (Const(strlit"SUC")(Fun Num Num))
                        (quote n))`

val LCA_l_UNIV = term_to_deep ``LCA l (UNIV:'U set)``

open holSemanticsTheory

val axslca = EVAL ``axsof lca_ctxt``
axslca |> concl |> rhs |> rand |> listSyntax.dest_list |> fst |> hd

val termsem_comb2 = prove(
  ``i models thyof ctxt ∧
    f
    (Const f ty) === (Abs x (Abs y (t x y))) ∈ axsof ctxt
    ⇒
    termsem (tmsof ctxt) i v (Comb (Comb (Const f ty) a) b) =
    termsem (tmsof ctxt) i v (t a b)``,
  rw[termsem_def]

``LCA (SUC l) (UNIV:'U set) ⇒
  ∃(mem:'U reln).
    is_set_theory mem ∧ (∃inf. is_infinite mem inf) ∧
    (i models (thyof lca_ctxt) ⇒
       ∃v.
         (tmvof v (strlit"l",Num) = to_inner Num l) ∧
         (termsem (tmsof lca_ctxt) i v ^LCA_l_UNIV = True))``,
  CONV_TAC(LAND_CONV(REWR_CONV LCA_alt)) >> strip_tac >>
  first_assum(qspec_then`l`mp_tac) >>
  discharge_hyps >- simp[] >>
  first_assum(SUBST1_TAC) >> strip_tac >>
  imp_res_tac strongly_inaccessible_imp >>
  qexists_tac`mem` >>
  conj_tac >- simp[] >>
  conj_tac >- PROVE_TAC[] >>
  strip_tac >>
  first_assum(qspec_then`f l`mp_tac) >>
  discharge_hyps >- simp[] >>
  disch_then(qx_choose_then`fl`strip_assume_tac) >>
  qexists_tac`(K fl, K (to_inner Num l))` >>
  conj_tac >- simp[] >>
  ONCE_REWRITE_TAC[termsem_def] >>

  use the definition of LCA in the lca_ctxt, which means
  we have to provide an f and show it satisfies certain
  properties. for that f, use:
    Abstract
      (range ((to_inner Num):num->'U))
      (Funspace fl boolset)
      (λm. Abstract fl boolset
             (bool_to_inner o (f (finv (to_inner Num) m))))


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
