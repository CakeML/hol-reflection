open HolKernel boolLib bossLib
val _ = new_theory"HOL4Bool"

(* from boolScript.sml *)
fun FALSITY_CONV tm = DISCH F (SPEC tm (EQ_MP F_DEF (ASSUME F)))

val tb = mk_var("t",bool)
val _ = save_thm("FALSITY", GEN tb (FALSITY_CONV tb))

val ths = CONJUNCTS (SPEC tb boolTheory.IMP_CLAUSES)
val ths = map (GEN tb) ths
val () = app delete_proof ths
val _ = save_thm("IMP_CLAUSES", GEN tb (LIST_CONJ (map (SPEC tb) ths)))

val ths = CONJUNCTS (SPEC tb boolTheory.AND_CLAUSES)
val ths = map (GEN tb) ths
val () = app delete_proof ths
val _ = save_thm("AND_CLAUSES", GEN tb (LIST_CONJ (map (SPEC tb) ths)))

val ths = CONJUNCTS (SPEC tb boolTheory.EQ_CLAUSES)
val ths = map (GEN tb) ths
val () = app delete_proof ths
val _ = save_thm("EQ_CLAUSES", GEN tb (LIST_CONJ (map (SPEC tb) ths)))

val th = boolTheory.MONO_AND |> Q.GENL[`w`,`z`,`y`,`x`]
val () = delete_proof th
val _ = save_thm("MONO_AND", SPEC_ALL th)

val th = boolTheory.MONO_OR |> Q.GENL[`w`,`z`,`y`,`x`]
val () = delete_proof th
val _ = save_thm("MONO_OR", SPEC_ALL th)

val th = boolTheory.MONO_EXISTS |> Q.GENL[`Q`,`P`]
val () = delete_proof th
val _ = save_thm("MONO_EXISTS", SPEC_ALL th)

val RIGHT_OR_OVER_AND =
   let val t1 = ``A:bool``
       and t2 = ``B:bool``
       and t3 = ``C:bool``
       val th1 = ASSUME (mk_disj(mk_conj(t2,t3),t1))
       val th2 = CONJ (DISJ2 t2 (ASSUME t1)) (DISJ2 t3 (ASSUME t1))
       val (th3,th4) = CONJ_PAIR (ASSUME(mk_conj(t2,t3)))
       val th5 = CONJ (DISJ1 th3 t1) (DISJ1 th4 t1)
       val imp1 = DISCH (concl th1) (DISJ_CASES th1 th5 th2)
       val (th1,th2) = CONJ_PAIR (ASSUME (rand(concl imp1)))
       val th3 = DISJ2 (mk_conj(t2,t3)) (ASSUME t1)
       val (th4,th5) = CONJ_PAIR (ASSUME (mk_conj(t2,t3)))
       val th4 = DISJ1 (CONJ (ASSUME t2) (ASSUME t3)) t1
       val th5 = DISJ_CASES th2 (DISJ_CASES th1 th4 th3) th3
       val imp2 = DISCH (rand(concl imp1)) th5
   in
     GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE imp1 imp2)))
   end;
val _ = save_thm("RIGHT_OR_OVER_AND", RIGHT_OR_OVER_AND);

val SELECT_ELIM_THM = let
  val P = mk_var("P", alpha --> bool)
  val Q = mk_var("Q", alpha --> bool)
  val x = mk_var("x", alpha)
  val Px = mk_comb(P, x)
  val Qx = mk_comb(Q, x)
  val PimpQ = mk_imp(Px, Qx)
  val allPimpQ = mk_forall(x, PimpQ)
  val exPx = mk_exists (x, Px)
  val selP = mk_comb(prim_mk_const{Thy = "min", Name = "@"}, P)
  val asm_t = mk_conj(exPx, allPimpQ)
  val asm = ASSUME asm_t
  val (ex_th, forall_th) = CONJ_PAIR asm
  val imp_th = SPEC selP forall_th
  val Px_th = ASSUME Px
  val PselP_th0 = UNDISCH (SPEC_ALL SELECT_AX)
  val PselP_th = CHOOSE(x, ex_th) PselP_th0
in
  save_thm("SELECT_ELIM_THM", GENL [P, Q] (DISCH_ALL (MP imp_th PselP_th)))
end

val ONTO_THM = save_thm(
  "ONTO_THM",
  let val f = mk_var("f", Type.alpha --> Type.beta)
  in
      GEN f (RIGHT_BETA (AP_THM ONTO_DEF f))
  end);

val _ = export_theory()
