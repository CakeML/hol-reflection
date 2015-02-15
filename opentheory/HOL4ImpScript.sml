open HolKernel boolLib bossLib
val _ = new_theory"HOL4Imp"

fun FALSITY_CONV tm = DISCH F (SPEC tm (EQ_MP F_DEF (ASSUME F)))

val tb = mk_var("t",bool)
val FALSITY = save_thm("FALSITY", GEN tb (FALSITY_CONV tb))

fun UNFOLD_OR_CONV tm =
  let val (disj1,disj2) = dest_disj tm in
  RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM OR_DEF disj1)) disj2)
  end;

fun CUT_EQUAL P x y t thm =
  let val e = mk_eq(y,t) in
  DISCH e (SUBST [(x|->SYM (ASSUME e))] P thm)
  end;

fun BOOL_CASE P x t pt pf =
  let val th0 = SPEC t BOOL_CASES_AX
      val th1 = EQ_MP (UNFOLD_OR_CONV (concl th0)) th0
      val th2 = SPEC (subst[(x|->t)] P) th1 in
  MP (MP th2 (CUT_EQUAL P x t T pt)) (CUT_EQUAL P x t F pf)
  end;

val t1b = mk_var("t1",bool)
val t2b = mk_var("t2",bool)
infixr ==>
val op==> = mk_imp
infix ==
val op== = mk_eq
val IMP_ANTISYM_AX = save_thm(
  "IMP_ANTISYM_AX",
  let fun dsch t1 t2 th = DISCH (t2 ==> t1) (DISCH (t1 ==> t2) th)
      fun sch t1 t2 = (t1==>t2) ==> (t2==>t1) ==> (t1 == t2)
      val abs = MP (FALSITY_CONV (F == T)) (MP (ASSUME (T ==> F)) TRUTH)
      val tht = BOOL_CASE (sch T t2b) t2b t2b
                          (dsch T T (REFL T)) (dsch F T (SYM abs))
      val thf = BOOL_CASE (sch F t2b) t2b t2b
                          (dsch T F abs) (dsch F F (REFL F))
  in
    GEN t1b (GEN t2b (BOOL_CASE (sch t1b t2b) t1b t1b tht thf))
  end);

val _ = export_theory()
