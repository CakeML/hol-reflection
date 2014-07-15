load "holSyntaxSyntax";

open HolKernel boolLib bossLib lcsymtacs
open miscLib pairSyntax stringSyntax listSyntax holSyntaxSyntax
open reflectionTheory pred_setTheory setSpecTheory holSyntaxTheory holSemanticsTheory holSemanticsExtraTheory

val _ = temp_tight_equality()
val _ = new_theory"sketch"

local open String in
fun tyvar_to_deep s =
  if sub(s,0) = #"'" then
    if size s = 2 then str(Char.toUpper (sub(s,1)))
    else extract(s,1,NONE)
  else s
end

fun type_to_deep ty =
  if is_type ty then
    case dest_thy_type ty of { Args = args, Thy = thy, Tyop = tyop } =>
      let
        val name = fromMLstring tyop
        val args = List.map type_to_deep args
        val args = mk_list(args,type_ty)
      in
        mk_Tyapp(name,args)
      end
  else
    let
      val name = dest_vartype ty
      val name = tyvar_to_deep name
      val name = fromMLstring name
    in
      mk_Tyvar(name)
    end

fun term_to_deep tm =
  case dest_term tm of
    VAR(x,ty) => mk_Var(fromMLstring x, type_to_deep ty)
  | CONST {Name,Thy,Ty} => mk_Const(fromMLstring Name, type_to_deep Ty)
  | COMB (f,x) => mk_Comb(term_to_deep f, term_to_deep x)
  | LAMB (x,b) =>
      let
        val (x,ty) = dest_var x
      in
        mk_Abs(fromMLstring x, type_to_deep ty, term_to_deep b)
      end

fun underscores [] = ""
  | underscores (x::xs) = "_" ^ x ^ underscores xs

fun type_name (ty : hol_type) =
  if is_type ty then case dest_thy_type ty of
    { Args = args, Thy = thy, Tyop = tyop } =>
      tyop ^ underscores (map type_name args)
  else
    ty |> dest_vartype |> tyvar_to_deep

val U = mk_vartype("'U")
fun mk_in_var (ty : hol_type) =
  mk_var ("in_" ^ type_name ty, ty --> U)

val in_bool_tm = ``in_bool``
val in_fun_tm = ``in_fun``

fun mk_in (ty : hol_type) =
  if is_type ty then case dest_thy_type ty of
      { Args = [], Thy = thy, Tyop = "bool" } =>
        in_bool_tm
    | { Args = [ty1,ty2], Thy = thy, Tyop = "fun" } =>
        mk_comb(mk_comb(in_fun_tm, mk_in ty1), mk_in ty2)
    | { Args = args, Thy = thy, Tyop = tyop } =>
        mk_in_var ty
  else
    mk_in_var ty


fun genv x =
  (*
  let
    val (name,ty) = dest_var x in
  in
    genvar ty
  end
  *)
  variant [] x

val mem = ``mem:'U->'U->bool``
val tysig = genv ``tysig:tyenv``
val tmsig = genv ``tmsig:tmenv``
val tyass = genv ``tyass:'U tyass``
val tmass = genv ``tmass:'U tmass``
val tyval = genv ``tyval:'U tyval``
val tmval = genv ``tmval:'U tmval``
val signatur = mk_pair(tysig,tmsig)
val interpretation = mk_pair(tyass,tmass)
val valuation = mk_pair(tyval,tmval)
val termsem_tm = ``termsem0 ^mem``
fun mk_termsem d =
  list_mk_comb(termsem_tm,[tmsig,interpretation,valuation,d])

val good_context_def = Define`
  good_context ^mem ^tysig ^tmsig ^tyass ^tmass ^tyval ^tmval ⇔
    is_set_theory ^mem ∧
    is_interpretation ^signatur ^interpretation ∧
    is_std_interpretation ^interpretation ∧
    is_valuation ^tysig ^tyass ^valuation`
val good_context = good_context_def |> concl |> strip_forall |> snd |> lhs

val Var_thm = prove(
  ``^tmval (x,ty) = inty v ⇒
    ∀mem. inty v = termsem0 mem ^tmsig ^interpretation ^valuation (Var x ty)``,
  rw[termsem_def])

val Const_thm = prove(
  ``instance ^tmsig ^interpretation name ty ^tyval = inty c ⇒
    ∀mem. inty c = termsem0 mem ^tmsig ^interpretation ^valuation (Const name ty)``,
  rw[termsem_def])

val instance_tm = Term.inst[alpha|->``:'U``]``instance``
fun mk_instance name ty =
  list_mk_comb(instance_tm,[tmsig,interpretation,name,ty,tyval])

val Comb_thm = prove(
  ``^good_context ⇒
    in_fun ina inb f = termsem ^tmsig ^interpretation ^valuation ftm ∧
    ina x = termsem ^tmsig ^interpretation ^valuation xtm ⇒
    is_in ina ⇒ is_in inb
    ⇒
    inb (f x) =
      termsem ^tmsig ^interpretation ^valuation (Comb ftm xtm)``,
  rw[good_context_def,termsem_def] >>
  rpt(first_x_assum(SUBST1_TAC o SYM)) >>
  rw[in_fun_def] >>
  match_mp_tac EQ_SYM >>
  match_mp_tac apply_abstract_matchable >>
  simp[] >>
  imp_res_tac is_in_range_thm >>
  fs[BIJ_DEF,ext_def,INJ_DEF] >>
  AP_TERM_TAC >>
  AP_TERM_TAC >>
  match_mp_tac is_in_finv_left >>
  simp[]) |> UNDISCH

val Abs_thm = prove(
  ``^good_context ⇒
    ∀ina inb f x ty b.
    range ina = typesem tyass tyval ty ⇒
    range inb = typesem tyass tyval (typeof b) ⇒
    is_in ina ⇒ is_in inb ⇒
    (∀m. m <: range ina ⇒
      inb (f (finv ina m)) =
        termsem tmsig (tyass,tmass) (tyval,((x,ty) =+ m) tmval) b) ⇒
    term_ok (tysig,tmsig) b
    ⇒
    in_fun ina inb f =
      termsem tmsig (tyass,tmass) (tyval,tmval) (Abs x ty b)``,
  rw[termsem_def,in_fun_def,good_context_def] >>
  match_mp_tac (UNDISCH abstract_eq) >> simp[] >>
  rw[] >>
  match_mp_tac (UNDISCH termsem_typesem) >>
  simp[] >>
  qexists_tac`(tysig,tmsig)` >> simp[] >>
  fs[is_std_interpretation_def] >>
  fs[is_valuation_def,is_term_valuation_def] >>
  simp[combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> metis_tac[]) |> UNDISCH

fun var_to_cert v =
  let
    val v_deep = term_to_deep (assert is_var v)
    val (x_deep,ty_deep) = dest_Var v_deep
    val l = mk_comb(mk_in (type_of v),v)
    val a = mk_eq(mk_comb(tmval,mk_pair(x_deep,ty_deep)),l)
  in
    MATCH_MP Var_thm (ASSUME a) |> SPEC mem
  end

fun const_to_cert c =
  let
    val c_deep = term_to_deep (assert is_const c)
    val (name_deep,ty_deep) = dest_Const c_deep
    val l = mk_comb(mk_in (type_of c),c)
    val a = mk_eq(mk_instance name_deep ty_deep,l)
  in
    MATCH_MP Const_thm (ASSUME a) |> SPEC mem
  end

val good_context_is_in_in_bool = prove(mk_imp(good_context,rand(concl(is_in_in_bool))),
  rw[good_context_def,is_in_in_bool]) |> UNDISCH

val good_context_extend_tmval = prove(
  ``^good_context ∧
     m <: typesem ^tyass ^tyval ty ⇒
     good_context ^mem ^tysig ^tmsig ^tyass ^tmass ^tyval (((x,ty) =+ m) ^tmval)``,
  rw[good_context_def,is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> rw[])

fun term_to_cert tm =
  case dest_term tm of
    VAR _ => var_to_cert tm
  | CONST _ => const_to_cert tm
  | COMB(t1,t2) =>
    let
      val c1 = term_to_cert t1
      val c2 = term_to_cert t2
    in
      MATCH_MP (Comb_thm) (CONJ c1 c2)
      |> UNDISCH |> UNDISCH
      |> PROVE_HYP good_context_is_in_in_bool
    end
  | LAMB(x,b) =>
    let
      val (xd,tyd) = dest_Var(term_to_deep x)
      val bd = term_to_deep b
      val cx = var_to_cert x
      val cb = term_to_cert b
      val ina = cx |> concl |> lhs |> rator
      val inb = cb |> concl |> lhs |> rator
      val th = Abs_thm |> ISPECL[ina,inb,tm,xd,tyd,bd] |> funpow 4 UNDISCH
      val goal = (mk_set(hyp cb @ hyp th), th |> concl |> dest_imp |> fst)
      val th1 = TAC_PROOF(goal,
        rw[] >>
        match_mp_tac (MP_CANON (DISCH_ALL cb)) >>
        simp[combinTheory.APPLY_UPDATE_THM] >>
        conj_tac >- (
          match_mp_tac good_context_extend_tmval >>
          rw[] ) >>
        metis_tac[is_in_finv_right] )
      val th2 = MP th th1
    in
      UNDISCH th2
    end

val test_tm = ``λg. g (f T)``
val test = term_to_cert test_tm
(*
val tm = ``λx:bool. f x``
term_to_cert tm
*)

(*
val it = set_goal goal
show_assums := true
*)

val base_tysig_def = Define`
  base_tysig = FEMPTY |++ [("fun",2);("bool",0)]`
val base_tmsig_def = Define`
  base_tmsig = FEMPTY |++ [("=",Fun (Tyvar "A") (Tyvar "A"))]`

(*
val P = ``x:bool``
val tysig = ``base_tysig``
val tmsig = ``base_tmsig``
val thm = prove(
  ``is_set_theory ^mem ∧
    is_interpretation (^tysig,^tmsig) (tyass,tmass) ∧
    is_std_interpretation (tyass,tmass) ∧
    is_valuation ^tysig tmass (tyval,tmval) ∧
    tmval ("x",Bool) = in_bool x
    ⇒
    in_bool x =
      termsem ^tmsig (tyass,tmass) (tyval,tmval) (Var "x" Bool)``,
  rw[termsem_def])


val P = ``(f:bool->bool) x``
val tysig = ``base_tysig``
val tmsig = ``base_tmsig``

val P = ``λ(x:bool). x``
val tysig = ``base_tysig``
val tmsig = ``base_tmsig``
val Abs_thm = store_thm("Abs_thm",
  ``is_set_theory ^mem ∧
    is_interpretation (^tysig,^tmsig) (tyass,tmass) ∧
    is_std_interpretation (tyass,tmass) ∧
    is_valuation ^tysig tmass (tyval,tmval)
    ⇒
    in_fun in_bool in_bool ^P =
      termsem ^tmsig (tyass,tmass) (tyval,tmval) (^(term_to_deep P))``,
  rw[termsem_def,in_fun_def] >>
  rw[typesem_def] >>
  `tyass "bool" [] = boolset` by (
    fs[is_std_interpretation_def,is_std_type_assignment_def] )>>
  `range in_bool = boolset` by (
    imp_res_tac is_in_in_bool >>
    imp_res_tac is_in_range_thm >>
    imp_res_tac is_extensional >>
    fs[extensional_def] >>
    pop_assum kall_tac >>
    simp[mem_boolset] >>
    fs[BIJ_IFF_INV,ext_def,in_bool_def,boolean_def] >>
    metis_tac[] ) >>
  simp[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[combinTheory.APPLY_UPDATE_THM] >>
  imp_res_tac is_in_in_bool >>
  imp_res_tac is_in_range_thm >>
  rfs[ext_def,BIJ_DEF,INJ_DEF] >>
  metis_tac[is_in_finv_right,is_in_in_bool])

rw[typesem_def] >>
`tyass "bool" [] = boolset` by (
  fs[is_std_interpretation_def,is_std_type_assignment_def] )>>

`range in_bool = boolset` by (
  imp_res_tac is_in_in_bool >>
  imp_res_tac is_in_range_thm >>
  imp_res_tac is_extensional >>
  fs[extensional_def] >>
  pop_assum kall_tac >>
  simp[mem_boolset] >>
  fs[BIJ_IFF_INV,ext_def,in_bool_def,boolean_def] >>
  metis_tac[] ) >>
simp[] >>
match_mp_tac (UNDISCH abstract_eq) >>
simp[combinTheory.APPLY_UPDATE_THM] >>
imp_res_tac is_in_in_bool >>
imp_res_tac is_in_range_thm >>
rfs[ext_def,BIJ_DEF,INJ_DEF] >>
metis_tac[is_in_finv_right,is_in_in_bool])
*)

(*
P = ``ARB (c:α->β) (x:ind->ind) (ARB:α list)``
P_deep = ``Comb (Const ...) ...``
*)
val c_def = Define`c : γ = ARB`

val tysig = ``FEMPTY |++ [("list",1);("ind",0)]``
val tmsig = ``FEMPTY |+ ("c",(Tyvar "'c"))``
val P_deep = ``ARB:term``

val example =
  ``is_set_theory ^mem ∧
    BIJ (in_α : α -> 'U) UNIV (ext (tyval "'a")) ∧
    BIJ (in_β : β -> 'U) UNIV (ext (tyval "'b")) ∧
    BIJ (in_ind : ind -> 'U) UNIV (ext (tyass "ind" [])) ∧
    BIJ (in_list_α : α list -> 'U) UNIV (ext (tyass "list" [tyval "'a"])) ∧
    is_interpretation (^tysig,^tmsig) (tyass,tmass) ∧
    is_std_interpretation (tyass,tmass) ∧
    tmass "c" [range (in_fun in_α in_β)] = in_fun in_α in_β c ∧
    is_valuation ^tysig tmass (tyval,tmval) ∧
    tmval ("x",Fun Ind Ind) = in_fun in_ind in_ind x
    ⇒
    in_fun in_α (in_fun in_β in_ind) P =
       termsem ^tmsig (tyass,tmass) (tyval,tmval) ^P_deep``

val example_sequent =
  ( [ ``is_set_theory ^mem``
    , ``is_interpretation (^tysig,^tmsig) (tyass,tmass)``
    , ``is_std_interpretation (tyass,tmass)``
    , ``is_valuation ^tysig tmass (tyval,tmval)``
    , ``BIJ (in_α : α -> 'U) UNIV (ext (tyval "'a"))``
    , ``BIJ (in_β : β -> 'U) UNIV (ext (tyval "'b"))``
    , ``BIJ (in_ind : ind -> 'U) UNIV (ext (tyass "ind" []))``
    , ``BIJ (in_list_α : α list -> 'U) UNIV (ext (tyass "list" [tyval "'a"]))``
    , ``tmass "c" [range (in_fun in_α in_β)] = in_fun in_α in_β c``
    , ``tmval ("x",Fun Ind Ind) = in_fun in_ind in_ind x``
    ]
  , ``in_fun in_α (in_fun in_β in_ind) P =
        termsem ^tmsig (tyass,tmass) (tyval,tmval) ^P_deep`` )

val _ = export_theory()
