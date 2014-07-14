open HolKernel boolLib bossLib lcsymtacs
open pred_setTheory
open holSemanticsTheory

val _ = temp_tight_equality()
val _ = new_theory"sketch"

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

(*
val in_bool_is_bij = store_thm("in_bool_is_bij",
  ``is_set_theory ^mem ==> BIJ in_bool UNIV (ext (range in_bool))``,
  rw[in_bool_def,ext_def,range_def,BIJ_IFF_INV] >- (

    rw[in_bool_def,boolean_in_boolset] ) >>
  qexists_tac`λx. x = True` >>
  rw[in_bool_def,boolean_eq_true] >>
  rfs[mem_boolset,boolean_eq_true,true_neq_false,boolean_def])
*)

val in_fun_def = Define`
  in_fun0 ^mem ina inb f =
    Abstract (range ina) (range inb) (λx. inb (f (finv ina x)))`
val _ = Parse.overload_on("in_fun",``in_fun0 ^mem``)

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
 

val _ = export_theory()
