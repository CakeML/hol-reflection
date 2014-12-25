open HolKernel boolLib boolSimps bossLib lcsymtacs listTheory alistTheory pred_setTheory pairTheory
open miscLib holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
val _ = new_theory"holDerivation"

(* TODO: move? *)
val type1_size_append = prove(
  ``∀l1 l2. type1_size (l1 ++ l2) = type1_size l1 + type1_size l2``,
  Induct >> simp[type_size_def])

val tymatch_def = tDefine"tymatch"`
  (tymatch [] [] sids = SOME sids) ∧
  (tymatch [] _ _ = NONE) ∧
  (tymatch _ [] _ = NONE) ∧
  (tymatch (Tyvar name::ps) (ty::obs) sids =
   let (s,ids) = sids in
   let v = REV_ASSOCD (Tyvar name) s (Tyvar name) in
   case if v = Tyvar name then
          if MEM name ids then SOME v else NONE
        else SOME v
   of NONE => if v=ty then tymatch ps obs (s,name::ids) else tymatch ps obs ((ty,v)::s,ids)
    | SOME ty1 => if ty1=ty then tymatch ps obs sids else NONE) ∧
  (tymatch (Tyapp c1 a1::ps) (Tyapp c2 a2::obs) sids =
   if c1=c2 then tymatch (a1++ps) (a2++obs) sids else NONE) ∧
  (tymatch _ _ _ = NONE)`
  (WF_REL_TAC`measure (λx. type1_size (FST x) + type1_size (FST(SND x)))` >>
   simp[type1_size_append])
val tymatch_ind = fetch "-" "tymatch_ind"

val arities_match_def = tDefine"arities_match"`
  (arities_match [] [] = T) ∧
  (arities_match [] _ = F) ∧
  (arities_match _ [] = F) ∧
  (arities_match (Tyapp c1 a1::xs) (Tyapp c2 a2::ys) =
   ((c1 = c2) ⇒ arities_match a1 a2) ∧ arities_match xs ys) ∧
  (arities_match (_::xs) (_::ys) = arities_match xs ys)`
  (WF_REL_TAC`measure (λx. type1_size (FST x) + type1_size (SND x))`)
val arities_match_ind = fetch "-" "arities_match_ind"

val arities_match_length = store_thm("arities_match_length",
  ``∀l1 l2. arities_match l1 l2 ⇒ (LENGTH l1 = LENGTH l2)``,
  ho_match_mp_tac arities_match_ind >> simp[arities_match_def])

val arities_match_nil = store_thm("arities_match_nil[simp]",
  ``(arities_match [] ls = (ls = [])) ∧
    (arities_match ls [] = (ls = []))``,
  Cases_on`ls`>> simp[arities_match_def])

val arities_match_Tyvar = store_thm("arities_match_Tyvar[simp]",
  ``arities_match (Tyvar v::ps) (ty::obs) = arities_match ps obs``,
  Cases_on`ty`>>simp[arities_match_def])

val arities_match_append = store_thm("arities_match_append",
  ``∀l1 l2 l3 l4.
    arities_match l1 l2 ∧ arities_match l3 l4 ⇒
    arities_match (l1++l3) (l2++l4)``,
  ho_match_mp_tac arities_match_ind >>
  simp[arities_match_def])

val tymatch_SOME = store_thm("tymatch_SOME",
  ``∀ps obs sids s' ids'.
     arities_match ps obs ∧
      DISJOINT (set (MAP SND (FST sids))) (set (MAP Tyvar (SND sids))) ∧
      (∀name. ¬MEM (Tyvar name,Tyvar name) (FST sids)) ∧
      ALL_DISTINCT (MAP SND (FST sids)) ∧
      (tymatch ps obs sids = SOME (s',ids')) ⇒
       ∃s1 ids1.
         (s' = s1++(FST sids)) ∧ (ids' = ids1++(SND sids)) ∧
         DISJOINT (set (MAP SND s')) (set (MAP Tyvar ids')) ∧
         (∀name. ¬MEM (Tyvar name,Tyvar name) s') ∧
         ALL_DISTINCT (MAP SND s') ∧
         (MAP (TYPE_SUBST s') ps = obs)``,
  ho_match_mp_tac tymatch_ind >>
  simp[tymatch_def,arities_match_def] >>
  conj_tac >- (
    rpt gen_tac >>
    `∃s ids. sids = (s,ids)` by metis_tac[pairTheory.pair_CASES] >>
    simp[] >> strip_tac >>
    rpt gen_tac >>
    reverse IF_CASES_TAC >> fs[] >- (
      strip_tac >> fs[arities_match_def] >> rfs[] >>
      fs[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND,ALL_DISTINCT_APPEND] >>
      BasicProvers.CASE_TAC >> fs[] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[IN_DISJOINT,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
      metis_tac[] ) >>
    IF_CASES_TAC >> fs[] >- (
      strip_tac >> fs[] >> rfs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND,ALL_DISTINCT_APPEND] >>
      BasicProvers.CASE_TAC >> fs[] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[IN_DISJOINT,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
      metis_tac[] ) >>
    IF_CASES_TAC >> fs[] >- (
      strip_tac >> fs[] >> rfs[] >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
      `¬MEM (Tyvar name) (MAP SND s)` by (
        fs[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND] >>
        BasicProvers.EVERY_CASE_TAC >- (
          imp_res_tac ALOOKUP_FAILS >> fs[MEM_MAP,EXISTS_PROD] ) >>
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        metis_tac[] ) >>
      fs[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND] >>
      BasicProvers.CASE_TAC >> fs[] >>
      reverse BasicProvers.EVERY_CASE_TAC >> fs[] >- (
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        metis_tac[] ) >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[ALL_DISTINCT_APPEND] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[IN_DISJOINT,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
      metis_tac[] ) >>
    strip_tac >> fs[] >> rfs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    `¬MEM (Tyvar name) (MAP SND s)` by (
      fs[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND] >>
      BasicProvers.EVERY_CASE_TAC >- (
        imp_res_tac ALOOKUP_FAILS >> fs[MEM_MAP,EXISTS_PROD] ) >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    `¬MEM (Tyvar name) (MAP Tyvar ids)` by fs[MEM_MAP] >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    simp[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND] >>
    BasicProvers.CASE_TAC >>
    fs[ALL_DISTINCT_APPEND] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
    metis_tac[] ) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> fs[] >>
  `arities_match (a1++ps) (a2++obs)` by
    (imp_res_tac arities_match_append) >>
  fs[] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp_tac (std_ss++ETA_ss) [] >>
  imp_res_tac arities_match_length >>
  fs[APPEND_EQ_APPEND] >>
  rfs[] >>
  `LENGTH l = 0` by DECIDE_TAC >>
  fs[LENGTH_NIL])

val match_type_def = Define`
  match_type ty1 ty2 = OPTION_MAP FST (tymatch [ty1] [ty2] ([],[]))`

val type_ok_arities_match = store_thm("type_ok_arities_match",
  ``∀tys ty1 ty2.
    type_ok tys ty1 ∧ type_ok tys ty2 ⇒ arities_match [ty1] [ty2]``,
  gen_tac >> ho_match_mp_tac type_ind >> simp[] >>
  gen_tac >> strip_tac >>
  gen_tac >> Cases >> simp[arities_match_def] >>
  rw[type_ok_def] >> fs[] >>
  fs[EVERY_MEM] >>
  `∀ty1 ty2. MEM ty1 l ∧ MEM ty2 l' ⇒ arities_match [ty1] [ty2]` by metis_tac[] >>
  pop_assum mp_tac >>
  qpat_assum`LENGTH X = Y`mp_tac >>
  rpt (pop_assum kall_tac) >>
  map_every qid_spec_tac[`l'`,`l`] >>
  Induct >> simp[LENGTH_NIL] >>
  gen_tac >> Cases >> rw[] >>
  `arities_match l t` by metis_tac[] >>
  `arities_match [h] [h']` by metis_tac[] >>
  metis_tac[arities_match_append,APPEND])

val match_type_SOME = store_thm("match_type_SOME",
  ``∀ty1 ty2 s. arities_match [ty1] [ty2] ⇒
    (match_type ty1 ty2 = SOME s) ⇒
    (TYPE_SUBST s ty1 = ty2)``,
  rw[match_type_def] >>
  qspecl_then[`[ty1]`,`[ty2]`,`[],[]`]mp_tac tymatch_SOME >>
  simp[] >>
  Cases_on`z`>>simp[])
(* -- *)

val term_ok_Abs = store_thm("term_ok_Abs",
  ``term_ok (sigof thy) b ∧ type_ok (tysof thy) ty ⇒
      term_ok (sigof thy) (Abs (Var v ty) b)``,
  rw[term_ok_def])

val term_ok_Comb = store_thm("term_ok_Comb",
  ``term_ok (sigof thy) x ∧ term_ok (sigof thy) f ∧
    welltyped (Comb f x) ⇒
    term_ok (sigof thy) (Comb f x)``,
  rw[term_ok_def])

val term_ok_Const = store_thm("term_ok_Const",
  ``(FLOOKUP (tmsof thy) name = SOME ty0) ∧
    type_ok (tysof thy) ty ⇒
    is_instance ty0 ty ⇒
    term_ok (sigof thy) (Const name ty)``,
  rw[term_ok_def])

val term_ok_Var = store_thm("term_ok_Var",
  ``∀name. type_ok (tysof thy) ty ⇒
    term_ok (sigof thy) (Var name ty)``,
  rw[term_ok_def])

val type_ok_Tyapp = store_thm("type_ok_Tyapp",
  ``(FLOOKUP (tysof thy) name = SOME a) ⇒
    EVERY (type_ok (tysof thy)) args ⇒
    (LENGTH args = a)
    ⇒ type_ok (tysof thy) (Tyapp name args)``,
  rw[type_ok_def] >>
  asm_simp_tac (std_ss++boolSimps.ETA_ss)[])

val exists_rty_lemma = store_thm("exists_rty_lemma",
  ``(∃rty. Fun dty rty1 = Fun dty rty) = T``, rw[])

val is_instance_lemma = store_thm("is_instance_lemma",
  ``(TYPE_SUBST s ty1 = ty2) ⇒ is_instance ty1 ty2``,
  rw[] >> metis_tac[])

val lookup_type_ok = store_thm("lookup_type_ok",
  ``theory_ok thy ∧
    (FLOOKUP (tmsof thy) name = SOME ty0) ⇒
    type_ok (tysof thy) ty0``,
  rw[theory_ok_def,finite_mapTheory.IN_FRANGE_FLOOKUP,PULL_EXISTS] >>
  metis_tac[])

val absThm = save_thm("absThm",
  proves_rules |> CONJUNCTS |> el 1
  |> ONCE_REWRITE_RULE[CONJ_COMM]
  |> REWRITE_RULE[GSYM AND_IMP_INTRO,NOT_EXISTS])

val appThm = save_thm("appThm",
  proves_rules |> CONJUNCTS |> el 8
  |> REWRITE_RULE[GSYM AND_IMP_INTRO])

val axiom = save_thm("axiom",
  proves_rules |> CONJUNCTS |> el 11
  |> REWRITE_RULE[GSYM AND_IMP_INTRO])

val assume = store_thm("assume",
  ``∀p thy. theory_ok thy ⇒
    term_ok (sigof thy) p ⇒
    (typeof p = Bool) ⇒
    (thy,[p]) |- p``,
  rpt strip_tac >>
  metis_tac[proves_rules |> CONJUNCTS |> el 2,
            holSyntaxExtraTheory.term_ok_welltyped,
            holSyntaxExtraTheory.WELLTYPED])

val betaConv = store_thm("betaConv",
  ``∀x ty t thy.
    theory_ok thy ⇒
    term_ok (sigof thy) (Comb (Abs (Var x ty) t) (Var x ty)) ⇒
    (thy,[]) |- (Comb (Abs (Var x ty) t) (Var x ty) === t)``,
  strip_tac >>
  rw[term_ok_def] >>
  imp_res_tac(proves_rules |> CONJUNCTS |> el 3) >>
  fs[])

val deductAntisym = save_thm("deductAntisym",
  proves_rules |> CONJUNCTS |> el 4)

val eqMp = save_thm("eqMp",
  proves_rules |> CONJUNCTS |> el 5
  |> REWRITE_RULE[GSYM AND_IMP_INTRO])

val refl = save_thm("refl",
  proves_rules |> CONJUNCTS |> el 9)

val sym = store_thm("sym",
  ``∀thyh p q. thyh |- p === q ⇒ thyh |- q === p``,
  rpt strip_tac >>
  imp_res_tac proves_theory_ok >>
  imp_res_tac proves_term_ok >>
  imp_res_tac theory_ok_sig >>
  `(FST thyh,[]) |- p === p` by (
    match_mp_tac refl >> simp[] >>
    fs[term_ok_equation]) >>
  `(FST thyh,[]) |- Equal (typeof p) === Equal (typeof p)` by (
    match_mp_tac refl >> simp[holBoolSyntaxTheory.term_ok_clauses] >>
    fs[term_ok_equation] >>
    metis_tac[term_ok_type_ok] ) >>
  qspecl_then[`[]`,`SND thyh`,`Equal (typeof p)`,`p`]mp_tac appThm >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >> simp[] >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  simp[] >> discharge_hyps_keep
    >- fs[term_ok_equation,EQUATION_HAS_TYPE_BOOL] >>
  simp[term_union_thm] >>
  strip_tac >> mp_tac appThm >>
  Cases_on`thyh`>>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  full_simp_tac std_ss [] >>
  disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
  fs[term_ok_equation] >>
  simp[GSYM equation_def,term_union_thm] >>
  qpat_assum`typeof p = typeof q`(assume_tac o SYM) >>
  simp[GSYM equation_def] >>
  fs[EQUATION_HAS_TYPE_BOOL] >>
  metis_tac[eqMp,term_union_thm,ACONV_REFL])

val trans = store_thm("trans",
  ``∀thy h1 h2 t1 t2a t2b t3.
      (thy,h2) |- t2b === t3 ⇒
      (thy,h1) |- t1 === t2a ⇒
      ACONV t2a t2b ⇒
      (thy,term_union h1 h2) |- t1 === t3``,
  rw[] >>
  imp_res_tac proves_theory_ok >> fs[] >>
  imp_res_tac theory_ok_sig >>
  imp_res_tac proves_term_ok >>
  rfs[term_ok_equation] >>
  qspecl_then[`Comb (Equal (typeof t3)) t3`,`thy`]mp_tac refl >>
  simp[holBoolSyntaxTheory.term_ok_clauses] >>
  discharge_hyps >- metis_tac[term_ok_type_ok,term_ok_welltyped] >>
  disch_then(mp_tac o MATCH_MP appThm) >>
  disch_then(qspecl_then[`h1`,`t2a`,`t1`]mp_tac) >>
  discharge_hyps >- metis_tac[sym] >>
  fs[EQUATION_HAS_TYPE_BOOL] >>
  imp_res_tac ACONV_TYPE >> rfs[] >>
  qpat_assum`typeof t3 = X`(assume_tac o SYM) >>
  simp[GSYM equation_def] >>
  disch_then(mp_tac o MATCH_MP eqMp) >>
  disch_then(qspecl_then[`h2`,`t3 === t2b`]mp_tac) >>
  simp[term_union_thm] >>
  discharge_hyps >- metis_tac[sym] >>
  discharge_hyps >- (
    simp[ACONV_def,RACONV,equation_def] >>
    simp[GSYM ACONV_def] ) >>
  metis_tac[sym])

val proveHyp = store_thm("proveHyp",
  ``∀thy h1 c1 h2 c2. (thy,h1) |- c1 ∧ (thy,h2) |- c2 ⇒
      (thy,term_union h2 (term_remove c2 h1)) |- c1``,
  rw[] >>
  imp_res_tac proves_term_ok >>
  imp_res_tac proves_theory_ok >> fs[] >>
  qspecl_then[`c2`,`c1`,`h2`,`h1`,`thy`]mp_tac deductAntisym >>
  simp[] >> strip_tac >>
  qmatch_assum_abbrev_tac`(thy,h3) |- c2 === c1` >>
  qspecl_then[`h3`,`h2`,`c2`,`c2`,`c1`,`thy`]mp_tac eqMp >>
  simp[] >>
  strip_tac >>
  match_mp_tac proves_ACONV >>
  first_assum(match_exists_tac o concl) >>
  simp[] >>
  conj_tac >- metis_tac[welltyped_def] >>
  unabbrev_all_tac >>
  simp[EVERY_MEM,EXISTS_MEM] >>
  conj_tac >> gen_tac >>
  disch_then(mp_tac o MATCH_MP MEM_term_union_imp) >>
  strip_tac >>
  TRY(pop_assum(mp_tac o MATCH_MP MEM_term_union_imp)) >>
  TRY strip_tac >>
  imp_res_tac MEM_term_remove_imp >>
  TRY(fs[EVERY_MEM]>>NO_TAC) >>
  metis_tac[MEM_term_union,hypset_ok_term_union,hypset_ok_term_remove,ACONV_REFL])

val inst_type = proves_rules |> CONJUNCTS |> el 7
val vsubst = proves_rules |> CONJUNCTS |> el 6
  |> ONCE_REWRITE_RULE[CONJ_COMM]
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]

fun replace_term from to =
  let
    fun f tm =
      if tm = from then to else
        case dest_term tm of
          COMB(t1,t2) => mk_comb(f t1, f t2)
        | LAMB(t1,t2) => mk_abs(f t1, f t2)
        | _ => tm
  in
    f
  end

val (inst_core_eval_def,inst_eval_def) =
  let
    val INST_CORE =``INST_CORE``
    val ty = type_of INST_CORE
    val inst_core_eval = mk_var("inst_core_eval",ty)
    val deftm =
      (INST_CORE_Abs_thm |> SPEC_ALL |> concl |> dest_imp |> snd
       |> replace_term (mk_var("_",``:type``)) ``u:type``)
      ::(INST_CORE_def |> CONJUNCTS |> map SPEC_ALL |> map concl |> List.rev |> tl)
      |> rev |> list_mk_conj
      |> replace_term INST_CORE inst_core_eval
    val INST = ``INST``
    val ty2 = type_of INST
    val inst_eval = mk_var("inst_eval",ty2)
    val th1 = tDefine"inst_core_eval"`^deftm`
     (WF_REL_TAC`measure (sizeof o SND o SND)` >> simp[SIZEOF_VSUBST])
    val deftm2 = INST_def
      |> SPEC_ALL |> concl
      |> replace_term INST inst_eval
      |> replace_term INST_CORE ``inst_core_eval``
  in
    (th1,Define`^deftm2`)
  end

val inst_core_eval_thm = prove(
  ``∀env tyin tm. welltyped tm ⇒
    (inst_core_eval env tyin tm = INST_CORE env tyin tm)``,
  ho_match_mp_tac (theorem"inst_core_eval_ind") >>
  rpt conj_tac >>
  TRY(rw[inst_core_eval_def,INST_CORE_def]>>
      unabbrev_all_tac >> fs[] >> NO_TAC) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  imp_res_tac INST_CORE_Abs_thm >>
  asm_simp_tac pure_ss [inst_core_eval_def] >>
  pop_assum kall_tac >>
  rw[] >> fs[] >>
  unabbrev_all_tac >> fs[] >>
  IF_CASES_TAC >> fs[] >>
  IF_CASES_TAC >> fs[] >>
  last_x_assum mp_tac >>
  discharge_hyps >- (
    match_mp_tac VSUBST_WELLTYPED >>
    simp[] >> simp[Once has_type_cases] ) >>
  strip_tac >> rfs[])

val inst_eval_thm = store_thm("inst_eval_thm",
  ``∀tyin tm. welltyped tm ⇒ (INST tyin tm = inst_eval tyin tm)``,
  rw[INST_def,inst_eval_def,inst_core_eval_thm])

val term_image_inst_eval_thm = prove(
  ``EVERY welltyped h ⇒ (term_image (INST tyin) h = term_image (inst_eval tyin) h)``,
  Induct_on`h` >> simp[] >> rpt strip_tac >> fs[] >>
  simp[Once term_image_def] >>
  simp[Once term_image_def,SimpRHS] >>
  simp[inst_eval_thm])

val subst_rule = store_thm("subst_rule",
  ``∀thy h c tyin subst.
    (thy,h) |- c ⇒
    EVERY (λp. type_ok (tysof thy) (FST p)) tyin ⇒
    EVERY (λ(s',s). ∃x ty. (s = Var x ty) ∧ (typeof s' = ty) ∧ term_ok (sigof thy) s') subst ⇒
    (thy,term_image (VSUBST subst) (term_image (inst_eval tyin) h)) |-
      (VSUBST subst (inst_eval tyin c))``,
  rw[] >>
  qspecl_then[`c`,`h`,`thy`,`tyin`]mp_tac inst_type >>
  simp[EVERY_MAP] >>
  imp_res_tac proves_term_ok >> fs[] >>
  `welltyped c ∧ EVERY welltyped h` by (
    fs[EVERY_MEM] >> metis_tac[term_ok_welltyped] ) >>
  simp[inst_eval_thm,term_image_inst_eval_thm] >>
  disch_then(match_mp_tac o MATCH_MP vsubst) >>
  fs[EVERY_MEM] >> rw[] >> res_tac >> fs[] >>
  metis_tac[term_ok_welltyped,WELLTYPED])

val exists_var_lemma = store_thm("exists_var_lemma",
  ``(∃x ty. (Var x1 ty1 = Var x ty) ∧ (typeof s' = ty) ∧ term_ok (sigof thy) s') ⇔
    ((typeof s' = ty1) ∧ term_ok (sigof thy) s')``,
  rw[EQ_IMP_THM])

val thm = store_thm("thm",
  ``∀thy c' h c.
      (thy,h) |- c ⇒
      welltyped c' ⇒ ACONV c c' ⇒
      EVERY (λx. term_ok (sigof thy) x ∧ (typeof x = Bool)) h' ⇒
      hypset_ok h' ⇒
      EVERY (λx. EXISTS (ACONV x) h') h ⇒
      (thy,h') |- c'``,
  rw[] >>
  match_mp_tac proves_ACONV >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  fs[EVERY_MEM,EXISTS_MEM] >>
  metis_tac[WELLTYPED,term_ok_welltyped])

val _ = export_theory()
