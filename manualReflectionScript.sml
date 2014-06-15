open HolKernel boolLib bossLib lcsymtacs listTheory finite_mapTheory alistTheory pred_setTheory pairTheory
open miscLib miscTheory setSpecTheory setModelTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory

val _ = temp_tight_equality()
val _ = new_theory"manualReflection"

val mem = ``mem:'U->'U-> bool``
val indin = ``indin:ind->'U``

val is_in_def = Define`
  is_in ^mem x f = BIJ f UNIV {y | mem y x}`

val OK = ``is_set_theory ^mem /\ ?indset. is_in mem indset ^indin``

val set_bool_def = Define`
  set_bool ^mem ^indin = boolset`

val in_bool_def = Define`
  in_bool ^mem ^indin = Boolean`

val boolset_in_bool = store_thm("boolset_in_bool",
  ``^OK ⇒ is_in mem boolset (in_bool mem indin)``,
  rw[is_in_def,BIJ_IFF_INV] >- (
    rw[in_bool_def,boolean_in_boolset] ) >>
  qexists_tac`λx. x = True` >>
  rw[in_bool_def,boolean_eq_true] >>
  rfs[mem_boolset,boolean_eq_true,true_neq_false,boolean_def])

val out_bool_def = Define`
  out_bool ^mem ^indin x = (x = True)`

(* Alternatively: out_bool ^mem ^indin x = @b. x = in_bool mem indin b *)

val set_ind_def = xDefine "set_ind"`
  set_ind ^mem ^indin = @indset. is_in mem indset indin`

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



(* Simple signatures etc. *)

val std_type_env_def = xDefine "std_type_env"`
  std_type_env = FUPDATE_LIST FEMPTY ["fun", 2; "bool", 0; "ind", 0]`

val std_term_env_def = xDefine "std_term_env"`
  std_term_env = FUPDATE_LIST FEMPTY
                   [ "=", Fun (Tyvar"A") (Fun (Tyvar"A") Bool)
                   ; "S", Fun (Fun (Tyvar"A")
                                   (Fun (Tyvar"B") (Tyvar"C")))
                              (Fun (Fun (Tyvar"A") (Tyvar"B"))
                                   (Fun (Tyvar"A") (Tyvar"C")))
                   ; "K", Fun (Tyvar"A") (Fun (Tyvar"B") (Tyvar"A"))
                   ; "I", Fun (Tyvar"A") (Tyvar"A")
                   ]`

val std_sig_def = xDefine "std_sig"`
  std_sig = (std_type_env, std_term_env)`;

val std_sig_thm = store_thm("std_sig_thm", ``is_std_sig std_sig``, EVAL_TAC)


val std_tyass_def = xDefine "std_tyass"`
     std_tyass ^mem ^indin "bool" [] = boolset
  /\ std_tyass ^mem ^indin "ind" [] = set_ind mem indin
  /\ std_tyass ^mem ^indin "fun" [x;y] = Funspace x y`

val std_tmass_def = xDefine "std_tmass"`
     std_tmass ^mem ^indin "=" [x] =
       (Abstract x (Funspace x boolset) \i.
          Abstract x boolset \j.
            in_bool mem indin (i = j))
  /\ std_tmass ^mem ^indin "S" [x;y;z] =
       (Abstract (Funspace x (Funspace y z))
                 (Funspace (Funspace x y) (Funspace x z)) \i.
          Abstract (Funspace x y) (Funspace x z) \j.
            Abstract x z \k. (i ' k) ' (j ' k))
  /\ std_tmass ^mem ^indin "K" [x;y] =
       Abstract x (Funspace y x) (\i. Abstract y x \j. i)
  /\ std_tmass ^mem ^indin "I" [x] =
       Abstract x x (\i. i)`

val std_int_def = xDefine "std_int"`
  std_int ^mem ^indin = 
    (std_tyass mem indin, std_tmass mem indin)`


(*
load "manualReflectionTheory";
open manualReflectionTheory;
open holSyntaxTheory finite_mapTheory;

g `!mem indin. OK ==> is_interpretation std_sig (std_int mem indin)`;
e GEN_TAC;
e GEN_TAC;
e DISCH_TAC;
e EVAL_TAC;

e CONJ_TAC;
e (REWRITE_TAC [FEVERY_DEF]);
e EVAL_TAC;

e (RW_TAC (srw_ss()) []);
e (Cases_on `ls`);
e EVAL_TAC;
 *)


val _ = export_theory()
