open HolKernel boolLib bossLib lcsymtacs miscLib
open lcaTheory reflectionTheory reflectionLib
open holSyntaxTheory holSyntaxExtraTheory
open holSemanticsTheory holSemanticsExtraTheory
open lcaCtxtTheory

val _ = new_theory"lcaProof"

val _ = Globals.max_print_depth := 15

val lca_ctxt = unpack_ctxt lca_ctxt_thm
val lca_inner_ctxt = lca_extends_init |> concl |> rator |> rand
val lca_ctxt_def = Define`
  lca_ctxt = ^lca_inner_ctxt`

val theory_ok_lca = store_thm("theory_ok_lca",
  ``theory_ok (thyof lca_ctxt)``,
  metis_tac[lca_extends_init |> REWRITE_RULE[GSYM lca_ctxt_def],
            init_theory_ok,extends_theory_ok])

val FLOOKUP_LCA = save_thm("FLOOKUP_LCA",
  ``ALOOKUP (const_list lca_ctxt) (strlit"LCA")``
  |> (PURE_ONCE_REWRITE_CONV[lca_ctxt_def] THENC EVAL))

val FLOOKUP_UNIV = save_thm("FLOOKUP_UNIV",
  ``ALOOKUP (const_list lca_ctxt) (strlit"UNIV")``
  |> (PURE_ONCE_REWRITE_CONV[lca_ctxt_def] THENC EVAL))

(*
val test = termsem_cert lca_ctxt ``T``
*)

val _ = overload_on("Num", ``Tyapp(strlit"num")[]``)
val quote_def = Define`
  (quote 0 = Const (strlit"0") Num) ∧
  (quote (SUC n) = Comb (Const(strlit"SUC")(Fun Num Num))
                        (quote n))`

val type_ok_Num = store_thm("type_ok_Num",
  ``type_ok (tysof lca_ctxt) Num``,
  rw[type_ok_def] >>
  ONCE_REWRITE_TAC[lca_ctxt_def] >>
  EVAL_TAC)

val LCA_l_UNIV = term_to_deep ``LCA l (UNIV:'U set)``

val (EVAL_type_ok,EVAL_term_ok) =
  holSyntaxLib.EVAL_type_ok_term_ok
    EVAL (MATCH_MP theory_ok_sig theory_ok_lca |> SIMP_RULE std_ss[])

open holBoolTheory HolKernel

val bool_interpretation_defs =
  [is_true_interpretation_def,
   is_and_interpretation_def,
   is_implies_interpretation_def,
   is_forall_interpretation_def,
   is_exists_interpretation_def,
   is_or_interpretation_def,
   is_false_interpretation_def,
   is_not_interpretation_def]

val extends_axioms = store_thm("extends_axioms",
  ``∀ctxt2 ctxt1. ctxt2 extends ctxt1 ⇒ axsof ctxt1 ⊆ axsof ctxt2``,
  simp[extends_def] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >>
  simp[PULL_EXISTS] >>
  metis_tac[pred_setTheory.SUBSET_UNION,pred_setTheory.SUBSET_TRANS])

(*
val extends_is_bool_interpretation = store_thm("extends_is_bool_interpretation",
  ``ctxt2 extends (mk_bool_ctxt ctxt) ∧
    theory_ok (thyof (mk_bool_ctxt ctxt)) ∧
    i models (thyof ctxt2) ⇒
    is_bool_interpretation i``,
  strip_tac >>
  `i models thyof (mk_bool_ctxt ctxt)` by (
    fs[models_def] >>
    f"is_inter"
    is_valuation_reduce
    f"assignment"
    f"extends"
    f"reduce"
    f"valua"
  `theory_ok (thyof ctxt2)`
  bool_has_bool_interpretation
  f"models"
  simp[is_bool_interpretation_def] >>
  fs[models_def] >>
  simp bool_interpretation_defs >>
  imp_res_tac extends_axioms >>
  fs[pred_setTheory.SUBSET_DEF] >>
  pop_assum mp_tac >>
  CONV_TAC(LAND_CONV(QUANT_CONV(LAND_CONV EVAL)))
  `MEM p (axiom_list (mk_bool_ctxt ctxt)) ⇒ MEM p (axiom_list ctxt2)` by (
  f"extends"

  is_true_interpretation_def
  f"is_bool"

val lca_is_bool_interpretation = 

val termsem_exists = store_thm("termsem_exists",
  ``is_bool_interpretation i ⇒
    termsem s i v (Exists f y b) =
    Boolean (∃
  ``,
  type_of``is_bool_interpretation``
  f"is_bool_int"
  f"bool_int"
  hyp extends_bool_interpretation
*)

val intermediate_thm = store_thm("intermediate_thm",
  ``LCA (SUC l) (UNIV:'U set) ⇒
    ∃(mem:'U reln).
      is_set_theory mem ∧ (∃inf. is_infinite mem inf) ∧
      (i models (thyof lca_ctxt) ∧
       to_inner Num l <: tyaof i (strlit "num") [] ⇒
         ∃v.
           is_valuation (tysof lca_ctxt) (tyaof i) v ∧
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
  `is_type_valuation (K fl)` by (
    simp[is_type_valuation_def] >>
    `(UNIV:ind set) ≼ f l` by (
      `∀k. k < SUC l ⇒ f k ≺ f (SUC k)` by metis_tac[] >>
      pop_assum mp_tac >>
      qid_spec_tac`l` >>
      last_x_assum mp_tac >>
      rpt(pop_assum kall_tac) >>
      strip_tac >>
      Induct >> simp[] >>
      strip_tac >>
      qpat_assum`X ⇒ Y`mp_tac >>
      discharge_hyps >- (
        rw[] >>
        `k < SUC(SUC l)` by simp[] >>
        res_tac ) >>
      rw[] >>
      first_x_assum(qspec_then`l`mp_tac) >> simp[] >>
      metis_tac[cardinalTheory.cardleq_lt_trans,cardinalTheory.cardlt_lenoteq] ) >>
    spose_not_then strip_assume_tac >> fs[] >>
    rfs[cardinalTheory.cardleq_empty] ) >>
  qspecl_then[`tysof lca_ctxt`,`tyaof i`,`K fl`]mp_tac(UNDISCH constrained_term_valuation_exists) >>
  simp[] >>
  discharge_hyps >- fs[models_def,is_interpretation_def] >>
  disch_then(qspec_then`[((strlit"l",Num),to_inner Num l)]`mp_tac) >>
  discharge_hyps >- (
    simp[type_ok_Num] >>
    simp[typesem_def] ) >>
  simp[] >> strip_tac >>
  qexists_tac`(K fl,σ)` >>
  conj_asm1_tac >- simp[is_valuation_def] >>
  conj_tac >- simp[] >>
  qmatch_abbrev_tac`termsem (tmsof ctxt) i v (Comb (Comb (Const g ty) a) b) = True` >>
  qspecl_then[`ctxt`,`i`,`v`,`g`,`ty`,`a`,`b`]mp_tac(UNDISCH termsem_comb2_ax) >>
  simp[Abbr`ctxt`,theory_ok_lca,Abbr`g`,FLOOKUP_LCA,Abbr`a`,Abbr`b`] >>
  simp[Once has_type_cases] >>
  simp[Once has_type_cases] >>
  CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(LAND_CONV EVAL_term_ok)))) >> simp[] >>
  CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(LAND_CONV EVAL_term_ok)))) >> simp[] >>
  simp[holSyntaxLibTheory.tyvar_inst_exists] >>
  CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(EVAL)))) >>
  simp_tac bool_ss [Abbr`ty`] >> disch_then kall_tac >>
  qmatch_abbrev_tac`termsem tmsig i vv (Exists ff fy pp) = True`
  f"termsem_exists"
  (*
  use:
    Abstract
      (range ((to_inner Num):num->'U))
      (Funspace fl boolset)
      (λm. Abstract fl boolset
             (bool_to_inner o (f (finv (to_inner Num) m))))

   *) cheat)

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
