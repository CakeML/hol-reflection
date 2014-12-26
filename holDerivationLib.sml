structure holDerivationLib :> holDerivationLib = struct

open OpenTheoryMap pairSyntax pairTheory miscLib listLib stringLib optionLib
     holSyntaxSyntax holSyntaxTheory holSyntaxExtraTheory
     holDerivationTheory

val the_name_map : term from_ot ref = ref (Map.mkDict otname_cmp)
fun add_name_map ot ml =
  the_name_map := Map.insert(!the_name_map,ot,ml)

val () = add_name_map ([],"->") ``strlit"fun"``
val () = add_name_map ([],"select") ``strlit"@"``

datatype object =
    Num of int
  | Name of term (* of type mlstring *)
  | List of object list
  | TypeOp of thm (* |- FLOOKUP (tysof thy) name = SOME arity *)
  | Type of thm (* |- type_ok (tysof thy) ty *)
  | Const of thm (* |- FLOOKUP (tmsof thy) name = SOME ty0 *)
  | Var of term * thm (* name, |- type_ok (tysof thy) ty *)
  | Term of thm (* |- term_ok (sigof thy) tm *)
  | Thm of thm (* |- (thy,h) |- c *)

type state = {
  stack : object list,
  dict : (int,object) Redblackmap.dict,
  thms : thm Net.net
}

val init_state:state = {
  stack = [],
  dict = Redblackmap.mkDict Int.compare,
  thms = Net.empty
}

fun push (s:state) obj : state =
  { stack = obj::(#stack s),
    dict = #dict s,
    thms = #thms s}

fun peek (s:state) = hd(#stack s)

fun pop (s:state) : object * state =
  (peek s,
   {stack= tl(#stack s),
    dict = #dict s,
    thms = #thms s})

fun def k x (s:state) =
  {stack = #stack s,
   dict = Redblackmap.update(#dict s, k, K x),
   thms = #thms s}

fun remove k (s:state) : state =
  let
    val (dict,x) = Redblackmap.remove(#dict s,k)
  in
    {stack = x::(#stack s),
     dict = dict,
     thms = #thms s}
  end

val typeof_rws = [typeof_def,codomain_def]

local
  val c = computeLib.new_compset typeof_rws
in
  val EVAL_typeof = computeLib.CBV_CONV c
end

local
  val [var,const,comb0,abs0] =
    WELLTYPED_CLAUSES
    |> CONJUNCTS
  val comb = comb0 |> SPEC_ALL |> EQ_IMP_RULE |> snd
             |> REWRITE_RULE[GSYM AND_IMP_INTRO]
  val abs = abs0 |> SPEC_ALL |> EQ_IMP_RULE |> snd
             |> Ho_Rewrite.REWRITE_RULE[PULL_EXISTS]
in
  fun EVAL_welltyped tm =
    if is_Var (rand tm) then PART_MATCH I var tm
    else if is_Const (rand tm) then PART_MATCH I const tm
    else if is_Comb (rand tm) then
      let
        val (f,x) = dest_Comb (rand tm)
        val th1 = EVAL_welltyped (mk_welltyped f)
        val th2 = EVAL_welltyped (mk_welltyped x)
        val th3 = EVAL_typeof (mk_typeof f)
        val th4 = EVAL_typeof (mk_typeof x)
      in
        MATCH_MP (MATCH_MP comb th1) th2
        |> CONV_RULE(LAND_CONV(QUANT_CONV(
               LAND_CONV(REWR_CONV th3) THENC
               RAND_CONV(RAND_CONV(RATOR_CONV(RAND_CONV(
                         REWR_CONV th4))))) THENC
             REWR_CONV exists_rty_lemma))
        |> C MATCH_MP TRUTH
      end
    else
      let
        val (v,t) = dest_Abs (rand tm)
        val th1 = EVAL_welltyped (mk_welltyped t)
        val (n,ty) = dest_Var v
      in
        SPECL [n,ty] abs
        |> C MATCH_MP (CONJ (REFL v) th1)
      end
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
    REWR_CONV combinTheory.o_THM THENC
    RAND_CONV EVAL_VFREE_IN THENC
    REWR_CONV NOT_F

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

local
  val c = listLib.list_compset()
  val () = pairLib.add_pair_compset c
  val () = computeLib.add_thms (term_union_def::term_remove_def::term_image_def::orda_rws) c
  val () = add_type_info c
in
  val EVAL_hypset = computeLib.CBV_CONV c
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

val match_type_rws = [
  match_type_def,
  tymatch_def,
  holSyntaxLibTheory.REV_ASSOCD]

local
  val c = listLib.list_compset()
  val () = computeLib.scrub_const c ``set`` (* TODO: list_compset is arguably broken because of this *)
  val () = optionLib.OPTION_rws c
  val () = pairLib.add_pair_compset c
  val () = computeLib.add_thms match_type_rws c
  val () = add_type_info c
in
  val EVAL_match_type = computeLib.CBV_CONV c
end

fun prove_is_instance type_ok_ty0 type_ok_ty =
  let
    val ty0 = type_ok_ty0 |> concl |> rand
    val ty = type_ok_ty |> concl |> rand
    val th1 = EVAL_match_type ``match_type ^ty0 ^ty``
    val th2 =
      MATCH_MP type_ok_arities_match
        (CONJ type_ok_ty0 type_ok_ty)
      |> MATCH_MP match_type_SOME
      |> C MATCH_MP th1
  in
    MATCH_MP is_instance_lemma th2
  end

val strcat_thm = prove(
  ``strcat (strlit s1) (strlit s2) = strlit (s1 ++ s2)``,
  rw[mlstringTheory.strcat_def,mlstringTheory.implode_def])

val vsubst_inst_rws = [
  VSUBST_thm,
  inst_eval_def,
  inst_core_eval_def,
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
  val () = computeLib.add_thms [alpha_lt_def,sortingTheory.SORTED_DEF] c
  val () = computeLib.add_conv(``orda``,3,EVAL_orda) c
  val () = computeLib.add_datatype_info c (valOf(TypeBase.fetch``:cpn``))
in
  val EVAL_SORTED_alpha_lt = computeLib.CBV_CONV c
end

fun prove_hypset_ok h =
  h |>
  (REWR_CONV(hypset_ok_def) THENC
   EVAL_SORTED_alpha_lt)
  |> EQT_ELIM

val listc = listLib.list_compset()

val get_hyp = snd o dest_pair o rand o rator o concl
val HYP_CONV = RATOR_CONV o RAND_CONV o RAND_CONV
fun HYPC_CONV c =
  HYP_CONV c THENC RAND_CONV c

type reader = {
  theory_ok : thm, (* |- theory_ok thy *)
  axiom : thm list -> thm, (* map (|- term_ok thy) (c::h) -> |- (thy,h) |- c *)
  const : term -> thm,
   (* name -> |- FLOOKUP (tmsof thy) name = SOME ty0 *)
  typeOp : term -> thm
   (* name -> |- FLOOKUP (tysof thy) name = SOME arity *)
}

fun trimr s = String.substring(s,0,String.size s - 1)
fun trimlr s = String.substring(s,1,String.size s - 2)

fun unimplemented l =
  mk_HOL_ERR"holDerivationLib""readLine"("unimplemented: "^l)

fun default_name ((ns,n):otname) = mlstringSyntax.mk_strlit(stringLib.fromMLstring n)

fun readLine (r:reader) s l =
  let
    val c = String.sub(l,0)
  in
    if c = #"#" then s
    else if c = #"\"" then
      let
        val otname = string_to_otname (trimlr l)
        val name = Map.find(!the_name_map,otname)
                   handle Map.NotFound => default_name otname
      in
        name |> Name |> push s
      end
    else if Char.isDigit(c) orelse c = #"-" then
      Option.valOf(Int.fromString l)
      |> Num |> push s
    else if l = "absTerm" then
      let
        val (Term term_ok_b,s) = pop s
        val (Var (x,type_ok_ty),s) = pop s
      in
        MATCH_MP (SPEC x term_ok_Abs)
          (CONJ term_ok_b type_ok_ty)
        |> Term |> push s
      end
    else if l = "absThm" then
      let
        val (Thm eqth,s) = pop s
        val h = eqth |> get_hyp |> listSyntax.dest_list |> fst
        val (Var (x,type_ok_ty),s) = pop s
        val P =
          combinSyntax.mk_o(negation,
            mk_comb(VFREE_IN_tm,mk_Var(x,rand(concl type_ok_ty))))
        val ths =
          map (EVAL_not_VFREE_IN o curry mk_comb P) h
      in
        MATCH_MP (MATCH_MP absThm type_ok_ty) eqth
        |> C MATCH_MP (join_EVERY P ths)
        |> Thm |> push s
      end
    else if l = "appTerm" then
      let
        val (Term term_ok_x,s) = pop s
        val (Term term_ok_f,s) = pop s
        val wt =
          mk_Comb(term_ok_f |> concl |> rand,
                  term_ok_x |> concl |> rand)
          |> mk_welltyped
          |> EVAL_welltyped
      in
        MATCH_MP term_ok_Comb
          (LIST_CONJ [term_ok_x,term_ok_f,wt])
        |> Term |> push s
      end
    else if l = "appThm" then
      let
        val (Thm xy,s) = pop s
        val (Thm fg,s) = pop s
        val th1 =
          MATCH_MP (MATCH_MP appThm fg) xy
        val th2 = EVAL_welltyped (fst(dest_imp(concl th1)))
        val th3 = MP th1 th2
      in
        CONV_RULE(HYP_CONV EVAL_hypset) th3
        |> Thm |> push s
      end
    else if l = "assume" then
      let
        val (Term term_ok_p,s) = pop s
        val th1 = MATCH_MP (MATCH_MP assume (#theory_ok r)) term_ok_p
        val th2 = EVAL_typeof (fst(dest_imp(concl th1)))
                  |> EQT_ELIM
      in
        MP th1 th2
        |> Thm |> push s
      end
    else if l = "axiom" then
      let
        val (Term term_ok_c,s) = pop s
        val (List hs,s) = pop s
        val term_ok_hs = map (fn (Term th) => th) hs
      in
        term_ok_c::term_ok_hs
        |> #axiom r
        |> Thm |> push s
      end
    else if l = "betaConv" then
      let
        val (Term term_ok_tm,s) = pop s
        val typeof_thm = EVAL_typeof(mk_typeof(rand(rand(rator(rand(concl term_ok_tm))))))
        val th1 = MATCH_MP betaConv (#theory_ok r)
                 |> C MATCH_MP term_ok_tm
                 |> C MATCH_MP typeof_thm
        val th2 = EVAL_subst(rand(rand(concl th1)))
      in
        th1
        |> CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV th2)))
        |> Thm |> push s
      end
    else if l = "cons" then
      let
        val (List t,s) = pop s
        val (h,s) = pop s
      in
        List (h::t) |> push s
      end
    else if l = "const" then
      let
        val (Name n,s) = pop s
      in
        (#const r) n
        |> Const |> push s
      end
    else if l = "constTerm" then
      let
        val (Type type_ok_ty,s) = pop s
        val (Const lookup,s) = pop s
        val th1 = MATCH_MP term_ok_Const
                  (CONJ lookup type_ok_ty)
        val type_ok_ty0 =
          MATCH_MP lookup_type_ok
            (CONJ (#theory_ok r) lookup)
        val th2 = prove_is_instance type_ok_ty0 type_ok_ty
      in
        MP th1 th2
        |> Term |> push s
      end
    else if l = "deductAntisym" then
      let
        val (Thm th1,s) = pop s
        val (Thm th2,s) = pop s
        val th3 = MATCH_MP deductAntisym (CONJ th1 th2)
        val th4 = EVAL_typeof(lhs(fst(dest_imp(concl th3))))
      in
        MATCH_MP th3 th4
        |> CONV_RULE(HYP_CONV EVAL_hypset)
        |> Thm |> push s
      end
    else if l = "def" then
      let
        val (Num k,s) = pop s
        val x = peek s
      in
         def k x s
      end
    else if l = "eqMp" then
      let
        val (Thm th1,s) = pop s
        val (Thm th2,s) = pop s
        val th3 = MATCH_MP (MATCH_MP eqMp th2) th1
        val th4 = EVAL_ACONV (fst(dest_imp(concl th3)))
                  |> EQT_ELIM
      in
        MP th3 th4
        |> CONV_RULE(HYP_CONV EVAL_hypset)
        |> Thm |> push s
      end
    else if l = "hdTl" then
      let
        val (List (h::t),s) = pop s
      in
        push s h |> C push (List t)
      end
    else if l = "nil" then
      push s (List [])
    else if l = "opType" then
      let
        val (List args,s) = pop s
        val (TypeOp lookup,s) = pop s
        val th1 = MATCH_MP type_ok_Tyapp lookup
        val tysig = lookup |> concl |> lhs |> rator |> rand
        fun f (Type th) = th
        val th2 = join_EVERY (mk_comb(type_ok_tm,tysig)) (map f args)
        val th3 = MATCH_MP th1 th2
        val th4 = computeLib.CBV_CONV listc (fst(dest_imp(concl th3)))
                  |> EQT_ELIM
      in
        MP th3 th4
        |> Type |> push s
      end
    else if l = "pop" then
      pop s |> snd
    else if l = "pragma" then
      pop s |> snd
    else if l = "proveHyp" then
      let
        val (Thm th1,s) = pop s
        val (Thm th2,s) = pop s
      in
        MATCH_MP proveHyp (CONJ th1 th2)
        |> CONV_RULE(HYP_CONV EVAL_hypset)
        |> Thm |> push s
      end
    else if l = "ref" then
      let
        val (Num k,s) = pop s
      in
        Redblackmap.find(#dict s,k)
        |> push s
      end
    else if l = "refl" then
      let
        val (Term term_ok_tm,s) = pop s
        val th1 = MATCH_MP refl
                    (CONJ (#theory_ok r) term_ok_tm)
        val th2 = EVAL_typeof(lhs(fst(dest_imp(concl th1))))
      in
        MATCH_MP th1 th2
        |> Thm |> push s
      end
    else if l = "remove" then
      let
        val (Num k,s) = pop s
      in
        remove k s
      end
    else if l = "subst" then
      let
        val (Thm th,s) = pop s
        val (List [List l1,List l2],s) = pop s
        val th1 = MATCH_MP subst_rule th
        val P = th1 |> concl |> dest_imp |> fst
          |> rator |> rand
        fun f (List [Name a, Type type_ok_ty]) =
          let
            val ty = type_ok_ty |> concl |> rand
            val v = mk_Tyvar a
            val th1 =
              type_ok_ty |>
              CONV_RULE(RAND_CONV(
                REWR_CONV(SYM(ISPECL[ty,v] FST))))
            val th2 = mk_comb(P,rand(rand(concl th1)))
              |> BETA_CONV |> SYM |> C EQ_MP th1
          in
            th2
          end
        val tyinth = join_EVERY P (map f l1)
        val th2 = MATCH_MP th1 tyinth
        val P = th2 |> concl |> dest_imp |> fst
          |> rator |> rand
        fun f (List [Var (n,type_ok_ty),Term term_ok_tm]) =
          let
            val ty = type_ok_ty |> concl |> rand
            val v = mk_Var(n,ty)
            val tm = term_ok_tm |> concl |> rand
            val typeof_th = EVAL_typeof (mk_typeof tm)
          in
            mk_comb(P,mk_pair(tm,v))
              |> (PAIRED_BETA_CONV THENC
                  REWR_CONV exists_var_lemma)
              |> SYM
              |> C EQ_MP (CONJ typeof_th term_ok_tm)
          end
        val substh = join_EVERY P (map f l2)
      in
        MATCH_MP th2 substh
        |> CONV_RULE(HYPC_CONV EVAL_subst)
        |> Thm |> push s
      end
    else if l = "sym" then
      let
        val (Thm th,s) = pop s
      in
        MATCH_MP sym th
        |> Thm |> push s
      end
    else if l = "thm" then
      let
        val (Term term_ok_p,s) = pop s
        val (List hs0,s) = pop s
        val (Thm th,s) = pop s
        val hs1 = map (fn (Term th) => th) hs0
        fun e th1 th2 =
          ``orda [] ^(rand(concl th1)) ^(rand(concl th2))``
          |> EVAL_orda |> concl |> rhs
        fun lt th1 th2 = e th1 th2 |> same_const``Less``
        val hs2 = sort lt hs1
        (* only if hs0 might contain duplicates
        fun d [] acc = acc
          | d [h] acc = h::acc
          | d (h1::h2::hs) acc =
            if e h1 h2 |> same_const``Equal`` then
              d hs (h1::acc)
            else
              d hs (h2::h1::acc)
        val hs3 = rev (d hs2 [])
        *)
        val hs3 = hs2
        val th1 = MATCH_MP thm th
        val th2 = MATCH_MP th1 (MATCH_MP term_ok_welltyped term_ok_p)
        val th3 = EVAL_ACONV (fst(dest_imp(concl th2)))
                  |> EQT_ELIM |> MATCH_MP th2
        val P = rand(rator(fst(dest_imp(concl th3))))
        fun f term_ok_x =
          let
            val x = term_ok_x |> concl |> rand
          in
            mk_comb(P,x)
            |> BETA_CONV |> SYM
            |> EQ_MP (CONJ term_ok_x (EVAL_typeof x))
          end
        val th4 = MATCH_MP th3 (join_EVERY P (map f hs3))
        val th5 = MATCH_MP th4 (prove_hypset_ok (rand(fst(dest_imp(concl th4)))))
        val th6 = EVAL_ACONV (fst(dest_imp(concl th5)))
                  |> EQT_ELIM |> MATCH_MP th5
      in
        th6 |> Thm |> push s
      end
    else if l = "trans" then
      let
        val (Thm th2,s) = pop s
        val (Thm th1,s) = pop s
        val th3 = MATCH_MP (MATCH_MP trans th1) th2
        val th4 = EVAL_ACONV (fst(dest_imp(concl th3)))
                  |> EQT_ELIM
      in
        MATCH_MP th3 th4
        |> Thm |> push s
      end
    else if l = "typeOp" then
      let
        val (Name n,s) = pop s
      in
        (#typeOp r) n
        |> TypeOp |> push s
      end
    else if l = "var" then
      let
        val (Type type_ok_ty,s) = pop s
        val (Name n,s) = pop s
      in
        Var (n,type_ok_ty)
        |> push s
      end
    else if l = "varTerm" then
      let
        val (Var (n,type_ok_ty),s) = pop s
      in
        term_ok_Var |> SPEC n
        |> C MATCH_MP type_ok_ty
        |> Term |> push s
      end
    else if l = "varType" then
      let
        val (Name n,s) = pop s
      in
        type_ok_Tyvar
        |> SPECL[#theory_ok r |> concl |> rand,n]
        |> Type |> push s
      end
    else if l = "version" then
      let
        val (Num k,s) = pop s
        val _ = assert (equal 6) k
      in
        s
      end
    else raise unimplemented l
  end

fun readArticle r istr =
  let
    fun loop s =
      case TextIO.inputLine istr of NONE => s
      | SOME l => readLine r s (trimr l) |> loop
    val s = loop init_state
    val () = TextIO.closeIn istr
  in
    #thms s
  end

end