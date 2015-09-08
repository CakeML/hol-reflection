structure holSyntaxLib :> holSyntaxLib = struct

open HolKernel boolLib bossLib lcsymtacs
open holSyntaxSyntax holSyntaxTheory holSyntaxExtraTheory
open holDerivationTheory

fun MEM_CONV eval =
  (REWR_CONV(CONJUNCT1 listTheory.MEM)) ORELSEC
  (REWR_CONV(CONJUNCT2 listTheory.MEM) THENC eval)

fun fix_list_compset c =
  let
    val () = computeLib.scrub_const c ``set``
    val () = computeLib.scrub_thms [listTheory.MEM] c
    val () = computeLib.add_conv(``$IN``,2,
      MEM_CONV (computeLib.CBV_CONV c)) c
  in () end

val typeof_rws = [typeof_def,codomain_def]

local
  val c = computeLib.new_compset typeof_rws
in
  val EVAL_typeof = computeLib.CBV_CONV c
end

local
  val [var0,const0,comb0,abs0] =
    WELLTYPED_CLAUSES
    |> CONJUNCTS
  val var = var0 |> SPEC_ALL |> EQT_INTRO |> GEN_ALL
  val const = const0 |> SPEC_ALL |> EQT_INTRO |> GEN_ALL
  val comb = comb0
  val abs = abs0 |> SIMP_RULE bool_ss [LEFT_EXISTS_AND_THM]
  val exists_var_lemma = prove(``(∃n ty. Var x y = Var n ty) = T``,rw[])
  val exists_rty_lemma = prove(
    ``(∃rty. Fun dty rty1 = Fun dty rty) = T``, rw[])
in
  fun EVAL_welltyped tm =
    if is_Var (rand tm) then PART_MATCH lhs var tm
    else if is_Const (rand tm) then PART_MATCH lhs const tm
    else if is_Comb (rand tm) then
      tm |> (
      REWR_CONV comb THENC
      FORK_CONV(EVAL_welltyped,
        FORK_CONV(EVAL_welltyped,
          QUANT_CONV(FORK_CONV(EVAL_typeof,
                               RAND_CONV(RATOR_CONV(RAND_CONV EVAL_typeof)))) THENC
          TRY_CONV(REWR_CONV exists_rty_lemma)) THENC
        TRY_CONV reduceLib.AND_CONV) THENC
      TRY_CONV reduceLib.AND_CONV)
    else if is_Abs (rand tm) then
      tm |> (
      REWR_CONV abs THENC
      FORK_CONV(REWR_CONV exists_var_lemma,
        EVAL_welltyped) THENC
      reduceLib.AND_CONV)
    else raise UNCHANGED
end

val term_info = valOf(TypeBase.fetch term_ty)
val type_info = valOf(TypeBase.fetch type_ty)
val mlstring_info = valOf(TypeBase.fetch ``:mlstring``)
val cpn_info = valOf(TypeBase.fetch``:cpn``)

fun add_type_info c =
  let
    val () = computeLib.add_datatype_info c term_info
    val () = computeLib.add_datatype_info c type_info
    val () = computeLib.add_datatype_info c mlstring_info
    val () = computeLib.add_datatype_info c cpn_info
    val () = stringLib.add_string_compset c
  in () end

local
  val c = listLib.list_compset()
  val () = computeLib.add_thms [VFREE_IN_def] c
  val () = add_type_info c
in
  val EVAL_VFREE_IN = computeLib.CBV_CONV c
end

val NOT_F = NOT_CLAUSES |> CONJUNCTS |> last

val EVAL_not_VFREE_IN =
  EQT_ELIM o
    (REWR_CONV combinTheory.o_THM THENC
     RAND_CONV EVAL_VFREE_IN THENC
     REWR_CONV NOT_F)

val ACONV_rws =
  [ACONV_def,
   RACONV,
   holSyntaxLibTheory.ALPHAVARS_def]
  @ typeof_rws

local
  val c = listLib.list_compset()
  val () = pairLib.add_pair_compset c
  val () = computeLib.add_thms ACONV_rws c
  val () = add_type_info c
in
  val EVAL_ACONV = computeLib.CBV_CONV c
end

val mlstring_cmp_thm =
  ``mlstring_cmp (strlit x) (strlit y)``
  |> REWRITE_CONV[mlstringTheory.mlstring_cmp_def,
                  totoTheory.TO_of_LinearOrder,
                  mlstringTheory.mlstring_lt_def,
                  mlstringTheory.mlstring_11]

val orda_rws = [
  orda_def,
  ordav_def,
  term_cmp_thm,
  type_cmp_thm,
  comparisonTheory.pair_cmp_def,
  comparisonTheory.list_cmp_def,
  mlstring_cmp_thm ]
  @ typeof_rws

local
  val c = listLib.list_compset()
  val () = pairLib.add_pair_compset c
  val () = computeLib.add_thms orda_rws c
  val () = add_type_info c
in
  val EVAL_orda = computeLib.CBV_CONV c
end

val type_subst_rws = [
  TYPE_SUBST_def |> REWRITE_RULE[ETA_AX],
  holSyntaxLibTheory.REV_ASSOCD]

local
  val c = listLib.list_compset()
  val () = pairLib.add_pair_compset c
  val () = computeLib.add_thms type_subst_rws c
  val () = add_type_info c
in
  val EVAL_TYPE_SUBST = computeLib.CBV_CONV c
end

val strcat_thm = prove(
  ``strcat (strlit s1) (strlit s2) = strlit (s1 ++ s2)``,
  rw[mlstringTheory.strcat_def,mlstringTheory.implode_def])

val vsubst_inst_rws = [
  VSUBST_thm,
  VFREE_IN_def,
  inst_eval_def,
  inst_core_eval_def,
  frees_def,union_def,subtract_def,itlist_def,
  vfree_in_def,
  variant_def,
  strcat_thm,
  dest_var_def,
  holSyntaxLibTheory.RESULT_def,
  holSyntaxLibTheory.IS_RESULT_def,
  holSyntaxLibTheory.IS_CLASH_def]
  @ type_subst_rws

local
  val c = listLib.list_compset()
  val () = pairLib.add_pair_compset c
  val () = add_type_info c
  val () = computeLib.add_datatype_info c (valOf(TypeBase.fetch``:'a result``))
  val () = computeLib.add_thms vsubst_inst_rws c
  val () = computeLib.add_thms (term_union_def::term_remove_def::term_image_def::orda_rws) c
in
  val EVAL_subst = computeLib.CBV_CONV c
end

local
  val c = listLib.list_compset()
  val () = pairLib.add_pair_compset c
  val () = computeLib.add_thms (term_union_def::term_remove_def::term_image_def::orda_rws) c
  val () = add_type_info c
in
  val EVAL_hypset = computeLib.CBV_CONV c
end

val match_type_rws = [
  match_type_def,
  tymatch_def,
  holSyntaxLibTheory.REV_ASSOCD]

local
  val c = listLib.list_compset()
  (* TODO: list_compset is arguably broken because of this *)
  val () = fix_list_compset c
  val () = optionLib.OPTION_rws c
  val () = pairLib.add_pair_compset c
  val () = computeLib.add_thms match_type_rws c
  val () = add_type_info c
in
  val EVAL_match_type = computeLib.CBV_CONV c
end

local
  val c = listLib.list_compset()
  val () = computeLib.add_thms [alpha_lt_def,sortingTheory.SORTED_DEF] c
  val () = computeLib.add_conv(``orda``,3,EVAL_orda) c
  val () = computeLib.add_datatype_info c (valOf(TypeBase.fetch``:cpn``))
in
  val EVAL_SORTED_alpha_lt = computeLib.CBV_CONV c
end

local
  val refl_thm = PROVE[]``(a = a) = T``
in
  val EQ_CONV = REWR_CONV refl_thm
end

val EVERY_NIL = CONJUNCT1 listTheory.EVERY_DEF
val EVERY_CONS = CONJUNCT2 listTheory.EVERY_DEF
fun every_conv conv tm = tm |> (
  (REWR_CONV EVERY_NIL) ORELSEC
  (REWR_CONV EVERY_CONS THENC
   FORK_CONV(conv,every_conv conv)))

fun EVAL_type_ok_term_ok lookup_conv is_std_sig =
  let
    val clauses = is_std_sig
      |> MATCH_MP term_ok_clauses
    val (term_ok_Var  ,clauses) = CONJ_PAIR clauses
    val (type_ok_Tyvar,clauses) = CONJ_PAIR clauses
    val (type_ok_Bool ,clauses) = CONJ_PAIR clauses
    val (type_ok_Fun  ,clauses) = CONJ_PAIR clauses
    val (term_ok_Comb ,clauses) = CONJ_PAIR clauses
    val (term_ok_Equal,clauses) = CONJ_PAIR clauses
    val (term_ok_eqn  ,clauses) = CONJ_PAIR clauses
    val  term_ok_Abs            =           clauses
    val sg = rand(concl is_std_sig)
    val term_ok_Const =
      term_ok_def |> CONJUNCTS |> el 2 |> SPEC sg
    val type_ok_Tyapp =
      type_ok_def |> CONJUNCTS |> el 2
      |> SIMP_RULE (pure_ss++boolSimps.ETA_ss)[]
      |> SPEC ``tysof ^sg``
    val db = ref Net.empty
    fun memo f x =
      let
        val ls = Net.index x (!db)
      in
        if List.null ls orelse
           not (aconv x (lhs(concl(List.hd ls)))) then
          let
            val th = f x
            val () = db := Net.insert(x,th) (!db)
          in
            th
          end
        else List.hd ls
      end
    fun tyconv tm = tm |> (memo ((
      (REWR_CONV type_ok_Tyvar)    ORELSEC
      (REWR_CONV type_ok_Bool)     ORELSEC
      (REWR_CONV type_ok_Fun THENC
       FORK_CONV (tyconv,tyconv))  ORELSEC
      (REWR_CONV type_ok_Tyapp THENC
       FORK_CONV (lookup_conv,
         every_conv tyconv))       ORELSEC
      (ALL_CONV o (assert (is_var o rand))))
      THENC DEPTH_CONV reduceLib.AND_CONV))
    fun tmconv tm = tm |> (memo ((
      (REWR_CONV term_ok_Var THENC tyconv)   ORELSEC
      (REWR_CONV term_ok_Equal THENC tyconv) ORELSEC
      (REWR_CONV term_ok_eqn THENC
       FORK_CONV (tmconv,
         FORK_CONV (tmconv,
           FORK_CONV (EVAL_typeof,EVAL_typeof)
           THENC (TRY_CONV EQ_CONV))))       ORELSEC
      (REWR_CONV term_ok_Comb THENC
       FORK_CONV (tmconv,
         FORK_CONV (tmconv,EVAL_welltyped))) ORELSEC
      (REWR_CONV term_ok_Abs THENC
       FORK_CONV (tyconv,tmconv))            ORELSEC
      (REWR_CONV term_ok_Const THENC
       QUANT_CONV(
         FORK_CONV(lookup_conv,
           LAND_CONV tyconv)) THENC
       HO_REWR_CONV UNWIND_THM1)             ORELSEC
       (ALL_CONV o (assert (is_var o rand))))
      THENC DEPTH_CONV reduceLib.AND_CONV))
  in
    (tyconv,tmconv)
  end

end
