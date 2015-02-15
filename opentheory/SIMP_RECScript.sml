open HolKernel boolLib bossLib numTheory prim_recTheory NUM_REPTheory Parse OpenTheoryMap
val _ = new_theory"SIMP_REC"

val _ = OpenTheory_const_name{const={Name="SIMP_REC",Thy="prim_rec"},name=(["HOL4"],"SIMP_REC")}
val _ = OpenTheory_const_name{const={Name="ABS_num",Thy="num"},name=(["HOL4"],"ABS_num")}
val _ = OpenTheory_const_name{const={Name="REP_num",Thy="num"},name=(["HOL4"],"REP_num")}

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

val uneta = prove(
  ``(∀x. f x = g x) ⇔ (f = \x. g x)``,
  SIMP_TAC bool_ss [FUN_EQ_THM])
fun preprocess def =
  SIMP_RULE (std_ss++boolSimps.ETA_ss) [uneta] def

val IS_NUM_REP_DEF = preprocess IS_NUM_REP
val () = delete_proof IS_NUM_REP_DEF
val IS_NUM_REP = prove(concl(IS_NUM_REP),
  GEN_TAC THEN
  CONV_TAC(LAND_CONV(RATOR_CONV(REWR_CONV IS_NUM_REP_DEF) THENC BETA_CONV)) THEN
  REFL_TAC)
val IS_NUM_REP_ZERO = NUM_REP_ZERO
val ISO1 = SPEC_ALL(CONJUNCT1 num_ISO_DEF)
val ISO2 = SPEC_ALL(CONJUNCT2 num_ISO_DEF)
val SUC = preprocess SUC_DEF
val () = delete_proof ISO1
val () = delete_proof ISO2
val () = delete_proof SUC
val SUC_DEF =
  AP_THM SUC ``m:num``
  |> CONV_RULE(RAND_CONV BETA_CONV)

val RAR = prove(
  ``IS_NUM_REP (REP_num n)``,
    CONV_TAC(REWR_CONV ISO2) THEN
    CONV_TAC(LAND_CONV(RAND_CONV(REWR_CONV ISO1))) THEN
    REFL_TAC);

val ind_lemma1 =
    TAC_PROOF
    (([], --`!P. P ZERO_REP /\ (!i. P i ==> P(SUC_REP i))
                 ==>
	      !i. IS_NUM_REP i ==> P i`--),
     NTAC 3 STRIP_TAC THEN
     CONV_TAC(LAND_CONV(REWR_CONV IS_NUM_REP)) THEN
     STRIP_TAC THEN RES_TAC);

val lemma =
    TAC_PROOF(([], --`(A ==> (A /\ B)) = (A ==> B)`--),
               ASM_CASES_TAC (--`A:bool`--) THEN ASM_REWRITE_TAC []);

val IS_NUM_SUC_REP =
    TAC_PROOF
    (([], --`!i. IS_NUM_REP i ==> IS_NUM_REP (SUC_REP i)`--),
     STRIP_TAC THEN
     CONV_TAC(LAND_CONV(REWR_CONV IS_NUM_REP)) THEN STRIP_TAC THEN
     CONV_TAC(REWR_CONV IS_NUM_REP) THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC);

val IS_NUM_REP_SUC_REP =
    TAC_PROOF
    (([], --`!n. IS_NUM_REP(SUC_REP(REP_num n))`--),
      GEN_TAC THEN MATCH_MP_TAC IS_NUM_SUC_REP THEN
      ACCEPT_TAC RAR);

val ind_lemma2 = TAC_PROOF(([],
  --`!P. P ZERO_REP /\ (!i. IS_NUM_REP i /\ P i ==> P(SUC_REP i))
           ==>
         !i. IS_NUM_REP i ==> P i`--),
     GEN_TAC THEN STRIP_TAC THEN
     MP_TAC (SPEC (--`\i. IS_NUM_REP i /\ P i`--) ind_lemma1) THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     CONV_TAC(DEPTH_CONV(REWR_CONV lemma)) THEN
     DISCH_THEN MATCH_MP_TAC THEN
     CONJ_TAC THEN1 (
       CONJ_TAC THEN1 ACCEPT_TAC IS_NUM_REP_ZERO THEN
       FIRST_ASSUM ACCEPT_TAC ) THEN
     REPEAT STRIP_TAC THEN1
     IMP_RES_TAC IS_NUM_SUC_REP THEN
     RES_TAC);

val lemma1 =
    TAC_PROOF
    (([], --`(!i. IS_NUM_REP i ==> P(ABS_num i)) = (!n. P n)`--),
     EQ_TAC THEN REPEAT STRIP_TAC THENL
     [CONV_TAC(RAND_CONV(REWR_CONV(SYM ISO1))) THEN
      POP_ASSUM MATCH_MP_TAC THEN ACCEPT_TAC RAR,
      FIRST_ASSUM MATCH_ACCEPT_TAC]);

val INDUCTION = store_thm("INDUCTION",
    --`!P. P 0 /\ (!n. P n ==> P(SUC n)) ==> !n. P n`--,
     GEN_TAC THEN STRIP_TAC THEN
     MP_TAC (SPEC (--`\i. ((P(ABS_num i)):bool)`--) ind_lemma2) THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC [SYM ZERO_DEF,lemma1] THEN
     DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC,
      GEN_TAC THEN
      CONV_TAC(LAND_CONV(LAND_CONV(REWR_CONV ISO2))) THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
      CONV_TAC(RAND_CONV(REWR_CONV(SYM SUC_DEF))) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      CONV_TAC(RAND_CONV(REWR_CONV(SYM ISO1))) THEN
      FIRST_ASSUM ACCEPT_TAC]);

(*
val ax = num_Axiom_old
  |> CONV_RULE(QUANT_CONV(QUANT_CONV(
       RATOR_CONV(REWR_CONV EXISTS_UNIQUE_DEF) THENC
       BETA_CONV) THENC HO_REWR_CONV FORALL_AND_THM)
       THENC HO_REWR_CONV FORALL_AND_THM)
  |> CONJUNCT1
  |> Q.SPECL[`z`,`\x y. f x`]
  |> CONV_RULE(QUANT_CONV(RAND_CONV(QUANT_CONV(RAND_CONV(RATOR_CONV BETA_CONV THENC BETA_CONV)))))

val GSKOLEM = GSYM SKOLEM_THM

val SIMP_REC = mk_var("SIMP_REC",type_of``SIMP_REC``)
val tm = replace_term ``SIMP_REC`` SIMP_REC (concl SIMP_REC_THM)
val goal = ([mk_eq(SIMP_REC,mk_select(SIMP_REC,tm))],tm)
val SIMP_REC_EXISTS = save_thm("SIMP_REC_EXISTS",
  TAC_PROOF(goal,
    POP_ASSUM SUBST1_TAC THEN
    SELECT_ELIM_TAC THEN
    CONJ_TAC THEN1 (
      CONV_TAC(
        HO_REWR_CONV GSKOLEM THENC
        QUANT_CONV (HO_REWR_CONV GSKOLEM)) THEN
      MAP_EVERY Q.X_GEN_TAC[`z`,`f`] THEN
      ACCEPT_TAC ax) THEN
    GEN_TAC THEN DISCH_THEN ACCEPT_TAC));
*)

val _ = export_theory()
