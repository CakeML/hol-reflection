open HolKernel boolLib bossLib lcsymtacs
open miscLib stringSyntax listSyntax pred_setTheory
open setSpecTheory holSemanticsTheory holSemanticsExtraTheory

val _ = temp_tight_equality()
val _ = new_theory"sketch"

(* TODO: use mk_syntax_fns *)

local open String in
fun tyvar_to_deep s =
  if sub(s,0) = #"'" then
    if size s = 2 then str(Char.toUpper (sub(s,1)))
    else extract(s,1,NONE)
  else s
end

val type_ty = ``:type``

fun type_to_deep ty =
  if is_type ty then
    case dest_thy_type ty of { Args = args, Thy = thy, Tyop = tyop } =>
      let
        val name = fromMLstring tyop
        val args = List.map type_to_deep args
        val args = mk_list(args,type_ty)
      in
        ``Tyapp ^name ^args``
      end
  else
    let
      val name = dest_vartype ty
      val name = tyvar_to_deep name
      val name = fromMLstring name
    in
      ``Tyvar ^name``
    end

fun term_to_deep tm =
  case dest_term tm of
    VAR(x,ty) => ``Var ^(fromMLstring x) ^(type_to_deep ty)``
  | CONST {Name,Thy,Ty} => ``Const ^(fromMLstring Name) ^(type_to_deep Ty)``
  | COMB (f,x) => ``Comb ^(term_to_deep f) ^(term_to_deep x)``
  | LAMB (x,b) =>
      let
        val (x,ty) = dest_var x
      in
        ``Abs ^(fromMLstring x) ^(type_to_deep ty) ^(term_to_deep b)``
      end

val mem = ``mem:'U->'U->bool``

val ext_def = Define`
  ext0 ^mem s = { a | mem a s }`
val _ = Parse.overload_on("ext",``ext0 ^mem``)

val finv_def = Define`
  finv f x = @y. f y = x`

val range_def = Define`
  range0 ^mem (f : α -> 'U) = @x. BIJ f UNIV {a | mem a x}`
val _ = Parse.overload_on("range",``range0 ^mem``)

val in_bool_def = Define`
  in_bool0 ^mem = Boolean`
val _ = Parse.overload_on("in_bool",``in_bool0 ^mem``)

val is_in_def = Define`
  is_in0 ^mem f = ∃x. BIJ f UNIV {a | mem a x}`
val _ = Parse.overload_on("is_in",``is_in0 ^mem``)

val is_in_in_bool = store_thm("is_in_in_bool",
  ``is_set_theory ^mem ⇒
    is_in in_bool``,
  rw[is_in_def,BIJ_IFF_INV] >>
  qexists_tac`boolset` >>
  rw[in_bool_def,boolean_in_boolset] >>
  qexists_tac`λx. x = True` >>
  rw[in_bool_def,boolean_eq_true] >>
  rfs[mem_boolset,boolean_eq_true,true_neq_false,boolean_def])

val in_fun_def = Define`
  in_fun0 ^mem ina inb f =
    Abstract (range ina) (range inb) (λx. inb (f (finv ina x)))`
val _ = Parse.overload_on("in_fun",``in_fun0 ^mem``)

val out_fun_def = Define`
  out_fun0 ^mem ina inb mf x = finv inb (mf ' (ina x))`
val _ = Parse.overload_on("out_fun",``out_fun0 ^mem``)

val is_in_range_thm = store_thm("is_in_range_thm",
  ``∀f. is_in f ⇒ BIJ f UNIV (ext (range f))``,
  rw[is_in_def,range_def] >>
  SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >>
  rw[ext_def])

val is_in_finv_left = store_thm("is_in_finv_left",
  ``∀ina.
    is_in ina ⇒ ∀x. finv ina (ina x) = x``,
  rw[finv_def] >>
  SELECT_ELIM_TAC >>
  conj_tac >-metis_tac[] >>
  fs[is_in_def,BIJ_DEF,INJ_DEF])

val is_in_finv_right = store_thm("is_in_finv_right",
  ``∀ina.
    is_in ina ⇒ ∀x. x <: range ina ⇒
      (ina (finv ina x)) = x``,
  rw[finv_def] >>
  SELECT_ELIM_TAC >>
  conj_tac >-(
    imp_res_tac is_in_range_thm >>
    fs[ext_def,BIJ_DEF,SURJ_DEF] ) >>
  rw[])

val is_in_in_fun = store_thm("is_in_in_fun",
  ``is_set_theory ^mem ⇒
    ∀ina inb. is_in ina ∧ is_in inb ⇒ is_in (in_fun ina inb)``,
  rw[] >>
  rw[is_in_def,BIJ_IFF_INV] >>
  qexists_tac`Funspace (range ina) (range inb)` >>
  conj_tac >- (
    rw[in_fun_def] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[range_def] >>
    SELECT_ELIM_TAC >>
    conj_tac >- metis_tac[is_in_def] >>
    rw[] >>
    SELECT_ELIM_TAC >>
    conj_tac >- metis_tac[is_in_def] >>
    rw[] >>
    fs[BIJ_IFF_INV] ) >>
  qexists_tac`out_fun ina inb` >>
  conj_tac >- (
    rw[out_fun_def,in_fun_def,FUN_EQ_THM] >>
    qmatch_abbrev_tac`finv invb (Abstract s t f ' a) = Z` >>
    rfs[] >>
    `Abstract s t f ' a = f a` by (
      match_mp_tac (UNDISCH apply_abstract) >>
      imp_res_tac is_in_range_thm >>
      fs[ext_def,BIJ_IFF_INV] >>
      unabbrev_all_tac >> fs[] ) >>
    rw[Abbr`Z`,Abbr`f`,Abbr`a`,Abbr`invb`] >>
    imp_res_tac is_in_finv_left >>
    simp[] ) >>
  rw[in_fun_def,out_fun_def] >>
  first_x_assum(mp_tac o
    MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO](UNDISCH in_funspace_abstract))) >>
  simp[AND_IMP_INTRO] >>
  discharge_hyps >- (
    imp_res_tac is_in_range_thm >>
    fs[ext_def,BIJ_IFF_INV] >>
    metis_tac[] ) >>
  rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  gen_tac >>
  qspecl_then[`f`,`ina (finv ina x)`,`range ina`,`range inb`]mp_tac
    (UNDISCH apply_abstract) >>
  discharge_hyps >- (
    imp_res_tac is_in_range_thm >>
    fs[ext_def,BIJ_DEF,INJ_DEF] ) >>
  rw[] >>
  imp_res_tac is_in_finv_right >>
  rw[])

val Abs_thm = store_thm("Abs_thm",
  ``is_set_theory ^mem ∧
    is_interpretation (tysig,tmsig) (tyass,tmass) ∧
    is_std_interpretation (tyass,tmass) ∧
    is_valuation tysig tyass (tyval,tmval) ∧
    is_in ina ∧
    is_in inb ∧
    range ina = typesem tyass tyval ty ∧
    range inb = typesem tyass tyval (typeof b) ∧
    term_ok (tysig,tmsig) b ∧
    (∀m. m <: range ina ⇒
      inb (f (finv ina m)) =
        termsem tmsig (tyass,tmass) (tyval,((x,ty) =+ m) tmval) b)
    ⇒
    in_fun ina inb f =
      termsem tmsig (tyass,tmass) (tyval,tmval) (Abs x ty b)``,
  rw[termsem_def,in_fun_def] >>
  match_mp_tac (UNDISCH abstract_eq) >> simp[] >>
  rw[] >>
  match_mp_tac (UNDISCH termsem_typesem) >>
  simp[] >>
  qexists_tac`(tysig,tmsig)` >> simp[] >>
  fs[is_std_interpretation_def] >>
  fs[is_valuation_def,is_term_valuation_def] >>
  simp[combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> metis_tac[])

fun underscores [] = ""
  | underscores (x::xs) = "_" ^ x ^ underscores xs

fun type_name (ty : hol_type) =
  if is_type ty then case dest_thy_type ty of
    { Args = args, Thy = thy, Tyop = tyop } =>
      tyop ^ underscores (map type_name args)
  else
    dest_vartype ty

fun mk_in_var (ty : hol_type) =
  mk_var ("in_" ^ type_name ty, ``:^(ty) -> 'U``)

fun mk_in (ty : hol_type) =
  if is_type ty then case dest_thy_type ty of
      { Args = [], Thy = thy, Tyop = "bool" } =>
        ``in_bool``
    | { Args = [ty1,ty2], Thy = thy, Tyop = "fun" } =>
        ``in_fun ^(mk_in ty1) ^(mk_in ty2)``
    | { Args = args, Thy = thy, Tyop = tyop } =>
        mk_in_var ty
  else
    mk_in_var ty

open pairSyntax

val tysig = genvar ``:tyenv``
val tmsig = genvar ``:tmenv``
val tyass = genvar ``:'U tyass``
val tmass = genvar ``:'U tmass``
val tyval = genvar ``:'U tyval``
val tmval = genvar ``:'U tmval``
val signaturet = mk_pair(tysig,tmsig)
val interpretation = mk_pair(tyass,tmass)
val valuation = mk_pair(tyval,tmval)
val termsem_tm = ``termsem0 ^mem``
fun mk_termsem d =
  list_mk_comb(termsem_tm,[tmsig,interpretation,valuation,d])

val Var_thm = store_thm("Var_thm",
  ``^tmval (x,ty) = inty v ⇒
    ∀mem. inty v = termsem0 mem ^tmsig (^tyass,^tmass) (^tyval,^tmval) (Var x ty)``,
  rw[termsem_def])

val good_context_def = Define`
  good_context ^mem ^tysig ^tmsig ^tyass ^tmass ^tyval ^tmval ⇔
    is_set_theory ^mem ∧
    is_interpretation ^signaturet ^interpretation ∧
    is_std_interpretation ^interpretation ∧
    is_valuation ^tysig ^tyass ^valuation`
val good_context = good_context_def |> concl |> strip_forall |> snd |> lhs

val Comb_thm = store_thm("Comb_thm",
  ``^good_context ⇒
    is_in ina ∧ is_in inb ⇒
    in_fun ina inb f = termsem ^tmsig ^interpretation ^valuation ftm ∧
    ina x = termsem ^tmsig ^interpretation ^valuation xtm
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

fun var_to_cert v =
  let
    val v_deep = term_to_deep (assert is_var v)
    val (_,[x_deep,ty_deep]) = strip_comb v_deep
    val l = mk_comb(mk_in (type_of v),v)
    val a = mk_eq(mk_comb(tmval,mk_pair(x_deep,ty_deep)),l)
  in
    MATCH_MP Var_thm (ASSUME a) |> SPEC mem
  end

(*
fun term_to_cert tm =
  case dest_term tm of
    VAR _ => var_to_cert tm
  | CONST _ => raise(Fail"unimpleented")
  | COMB(t1,t2) =>
    let
      val c1 = term_to_cert t1
      val c2 = term_to_cert t2
    in

  Comb_thm
*)

(*
fun const_to_cert c =
  let
    val c_deep = term_to_deep (assert is_const c)

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
