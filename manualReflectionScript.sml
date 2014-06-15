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

val set_ind_def = Define`
  set_ind ^mem ^indin = @indset. is_in mem indset indin`

val in_ind_def = Define`
  in_ind ^mem ^indin i = indin i`

val out_ind_def = Define`
  out_ind ^mem ^indin x = @i. indin i = x`

(* Alternatively: out_ind ^mem ^indin x = @i. x = in_ind mem indin i *)

val set_fun_ind_bool_def = Define`
  set_fun_ind_bool ^mem ^indin =
    Funspace (set_ind mem indin) (set_bool mem indin)`

val in_fun_ind_bool = Define`
  in_fun_ind_bool ^mem ^indin f =
    Abstract (set_ind mem indin) (set_bool mem indin) \x.
      in_bool mem indin (f (out_ind mem indin x))`

val out_fun_ind_bool_def = Define`
  out_fun_ind_bool ^mem ^indin x = \i.
    out_bool mem indin (apply mem x (in_bool mem indin i))`

(* Alternatively: 
 *   out_fun_ind_bool ^mem ^indin x = @f. x = in_fun_ind_bool mem indin f
 *)


(* Simple signatures etc. *)

val std_type_env_def = Define`
  std_type_env = FUPDATE_LIST FEMPTY ["fun", 2; "bool", 0; "ind", 0]`

val std_term_env_def = Define`
  std_term_env = FUPDATE_LIST FEMPTY
                   [ "=", Fun (Tyvar"A") (Fun (Tyvar"A") Bool)
                   ; "S", Fun (Fun (Tyvar"A")
                                   (Fun (Tyvar"B") (Tyvar"C")))
                              (Fun (Fun (Tyvar"A") (Tyvar"B"))
                                   (Fun (Tyvar"A") (Tyvar"C")))
                   ; "K", Fun (Tyvar"A") (Fun (Tyvar"B") (Tyvar"A"))
                   ; "I", Fun (Tyvar"A") (Tyvar"A")
                   ]`

val std_sig_def = Define`
  std_sig = (std_type_env, std_term_env)`;

val std_sig_thm = store_thm("std_sig_thm", ``is_std_sig std_sig``, EVAL_TAC)


val std_tyass_def = Define`
     std_tyass ^mem ^indin tyop args =
     case (tyop,args) of
     | ("bool",[]) => boolset
     | ("fun",[x;y]) => Funspace x y
     | ("ind",[]) => set_ind mem indin
     | _ => ∅`

val std_tmass_def = Define`
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

val std_int_interprets_std_sig = store_thm("std_int_interprets_std_sig",
 ``∀mem indin. ^OK ⇒ is_interpretation std_sig (std_int mem indin)``,
 simp[is_interpretation_def,std_int_def] >>
 rpt gen_tac >> strip_tac >>
 conj_asm1_tac >- (
   rw[is_type_assignment_def,FEVERY_ALL_FLOOKUP] >>
   fs[std_sig_def,std_type_env_def,flookup_fupdate_list] >>
   BasicProvers.EVERY_CASE_TAC >> rw[std_tyass_def] >>
   BasicProvers.EVERY_CASE_TAC >> fs[]
   >- metis_tac[funspace_inhabited]
   >- metis_tac[mem_boolset]
   >- (
     rw[set_ind_def] >>
     SELECT_ELIM_TAC >>
     conj_tac >- metis_tac[] >>
     rw[is_in_def] >> fs[BIJ_IFF_INV] >>
     metis_tac[] )) >>
 `is_std_type_assignment (std_tyass mem indin)` by (
   rw[std_tyass_def,is_std_type_assignment_def,FUN_EQ_THM] ) >>
 rw[is_term_assignment_def,FEVERY_ALL_FLOOKUP] >>
 fs[std_sig_def,std_term_env_def,flookup_fupdate_list] >>
 BasicProvers.EVERY_CASE_TAC >> rw[std_tmass_def] >>
 CONV_TAC(ONCE_DEPTH_CONV(fn tm => if can (match_term``STRING_SORT (tyvars X)``) tm then EVAL tm else NO_CONV tm)) >>
 imp_res_tac typesem_Fun >> rw[std_tmass_def] >> rw[typesem_def] >>
 rw[std_tyass_def] >>
 match_mp_tac (UNDISCH abstract_in_funspace) >> rw[] >>
 match_mp_tac (UNDISCH abstract_in_funspace) >> rw[] >>
 rw[in_bool_def,boolean_in_boolset] >>
 match_mp_tac (UNDISCH abstract_in_funspace) >> rw[] >>
 match_mp_tac (UNDISCH apply_in_rng) >>
 qexists_tac`(τ "B")` >>
 conj_tac >- (
   match_mp_tac (UNDISCH apply_in_rng) >>
   metis_tac[] ) >>
 match_mp_tac (UNDISCH apply_in_rng) >>
 metis_tac[] )

val _ = export_theory()
