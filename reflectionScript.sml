open HolKernel boolLib bossLib lcsymtacs listTheory finite_mapTheory alistTheory pred_setTheory pairTheory
open miscLib miscTheory setSpecTheory setModelTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory

val _ = temp_tight_equality()
val _ = new_theory"reflection"

val mem = ``mem:'U->'U-> bool``
val indin = ``indin:ind->'U``

datatype simple_type = Ind | Bool | Fun of simple_type * simple_type

fun type_name Ind = "ind"
  | type_name Bool = "bool"
  | type_name (Fun (s,t)) = "fun_" ^ type_name s ^ "_" ^ type_name t

fun type_type Ind = mk_type("ind",[])
  | type_type Bool = mk_type("bool",[])
  | type_type (Fun (s,t)) = (type_type s --> type_type t) : hol_type


fun set_type t = let val u = mk_vartype("'U") in
  (u --> u --> mk_type("bool",[])) --> (mk_type("ind",[]) --> u)
                                   --> u
end

fun in_type t = let val u = mk_vartype("'U") in
  (u --> u --> mk_type("bool",[])) --> (mk_type("ind",[]) --> u)
                                   --> type_type t --> u
end

fun out_type t = let val u = mk_vartype("'U") in
  (u --> u --> mk_type("bool",[])) --> (mk_type("ind",[]) --> u)
                                   --> u --> type_type t
end

fun set_var t = mk_var ("set_" ^ type_name t, set_type t)
fun in_var t = mk_var ("in_" ^ type_name t, in_type t)
fun out_var t = mk_var ("out_" ^ type_name t, out_type t)

fun set_const t = mk_const ("set_" ^ type_name t, set_type t)
fun in_const t = mk_const ("in_" ^ type_name t, in_type t)
fun out_const t = mk_const ("out_" ^ type_name t, out_type t)

fun set_expr Bool = `set_bool ^mem ^indin = boolset`
  | set_expr Ind = `
      set_ind ^mem ^indin = @indset. (!i. mem (indin i) indset)
                                  /\ (!x. mem x indset ==> ?i. x = indin i)`
  | set_expr (Fun (s,t)) = `
      ^(set_var (Fun (s,t))) ^mem ^indin =
        Funspace (^(set_const s) mem indin) (^(set_const t) mem indin)`

fun in_expr Bool =
      `(in_bool ^mem ^indin T = True) /\ (in_bool ^mem ^indin F = False)`
  | in_expr Ind =
      `in_ind ^mem ^indin i = indin i`
  | in_expr (Fun (s,t)) =
      `^(in_var (Fun (s,t))) ^mem ^indin f =
           Abstract (^(set_const s) mem indin) (^(set_const t) mem indin) \x.
             ^(in_const t) mem indin (f (^(out_const s) mem indin x))`

fun out_expr t =
  `^(out_var t) ^mem ^indin x = @y. ^(in_const t) mem indin y = x`

fun mk t = ( xDefine ("set_" ^ type_name t) (set_expr t)
           , xDefine ("in_" ^ type_name t) (in_expr t)
           , xDefine ("out_" ^ type_name t) (out_expr t) )

val res1 = mk Bool;
val res2 = mk Ind;
val res3 = mk (Fun (Bool,Bool));
val res4 = mk (Fun (Ind,Ind));
val res5 = mk (Fun (Ind,Bool));
val res6 = mk (Fun (Fun (Ind,Ind), Fun (Ind,Bool)));

val _ = export_theory()
