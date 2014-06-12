open HolKernel boolLib bossLib lcsymtacs listTheory finite_mapTheory alistTheory pred_setTheory pairTheory
open miscLib miscTheory setSpecTheory setModelTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory

val _ = temp_tight_equality()
val _ = new_theory"manualReflection"

val mem = ``mem:'U->'U-> bool``
val indin = ``indin:ind->'U``

val set_bool_def = xDefine "set_bool"`
  set_bool ^mem ^indin = boolset`

val in_bool_def = xDefine "in_bool"`
  (in_bool ^mem ^indin T = True) /\ (in_bool ^mem ^indin F = False)`

val out_bool_def = xDefine "out_bool"`
  out_bool ^mem ^indin x = (x = True)`

(* Alternatively: out_bool ^mem ^indin x = @b. x = in_bool mem indin b *)
  
val set_ind_def = xDefine "set_ind"`
  set_ind ^mem ^indin = @indset. (!i. mem (indin i) indset)
                              /\ (!x. mem x indset ==> ?i. x = indin i)`

val in_ind_def = xDefine "in_ind"`
  in_ind ^mem ^indin i = indin i`
  
val out_ind_def = xDefine "out_ind"`
  out_ind ^mem ^indin x = @i. indin i = x`

(* Alternatively: out_ind ^mem ^indin x = @i. x = in_ind mem indin i *)

val set_fun_ind_bool_def = xDefine "set_fun_ind_bool"`
  set_fun_ind_bool ^mem ^indin = 
    Funspace (set_ind mem indin) (set_bool mem indin)`

val in_fun_ind_bool = xDefine "in_fun_ind_bool"`
  in_fun_ind_bool ^mem ^indin f =
    Abstract (set_ind mem indin) (set_bool mem indin) \x.
      in_bool mem indin (f (out_ind mem indin x))`
  
val out_fun_ind_bool_def = xDefine "out_fun_ind_bool"`
  out_fun_ind_bool ^mem ^indin x = \i.
    out_bool mem indin (apply mem x (in_bool mem indin i))`

(* Alternatively: 
 *   out_fun_ind_bool ^mem ^indin x = @f. x = in_fun_ind_bool mem indin f
 *)

val _ = export_theory()
