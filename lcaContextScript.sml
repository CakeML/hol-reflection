open HolKernel boolLib bossLib lcsymtacs
open pred_setTheory cardinalTheory reflectionTheory
open lcaTheory reflectionLib
val _ = new_theory"lcaContext"

val _ = Globals.max_print_depth := 15

val uneta = prove(
  ``(∀x. f x = g x) ⇔ f = \x. g x``,
  rw[FUN_EQ_THM])
fun preprocess def =
  SIMP_RULE (std_ss++boolSimps.ETA_ss) [uneta] def

(* IN *)
val extends_init_thm = hol_extends_init
val def = IN_DEF
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
(* INJ *)
val def = preprocess INJ_DEF
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
(* cardleq *)
val def = preprocess cardleq_def
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
(* UNIV *)
val def = UNIV_DEF
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
(* SUBSET *)
val def = preprocess SUBSET_DEF
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
(* POW *)
val POW_alt = METIS_PROVE[EXTENSION,IN_DEF,IN_POW]``∀s x. POW s x ⇔ x ⊆ s``
val def = preprocess POW_alt
val (upd,extends_init_thm) = build_ConstDef extends_init_thm def
(* SUC_REP *)

(* plan for building context:

LCA_def: ConstSpec LCA_exists
Proof: LCA_exists (from num_Axiom)
ConstDef: strongly_inaccessible_alt
ConstDef: countable_def
ConstDef: strong_limit_cardinal_def
ConstDef: my_regular_cardinal_alt
(* recursive defn *)
Proof: somehow get something like num_Axiom from the below
(* 0, SUC *)
ConstDef: SUC_DEF
ConstDef: ZERO_DEF
(* countable *)
ConstDef: countable_def
(* :num *)
Proof: TypeDefn EXISTS_NUM_REP
Const_Def: IS_NUM_REP
Proof: ZERO_REP: ConstSpec ZERO_REP_EXISTS
Proof: SUC_REP: ConstSpec infinity_ax
(* POW *)
ConstDef: POW_alt
(* ⊆ *)
ConstDef: SUBSET_DEF
(* UNIV *)
ConstDef: UNIV_DEF
(* ≺ ( overload for ≼ ) *)
ConstDef: cardleq_def
ConstDef: INJ_DEF
ConstDef: IN_DEF
hol_ctxt
*)

(* dependencies:
  stuff in HOL model (T, ∃, ∧, etc.)
  ≺, countable -- (expands to INJ, or further)
  ∈, ⊆, UNIV, POW -- (expands if necessary)
  0, SUC
  machinery for making recursive definitions...?

  strongly_inaccessible_alt
  my_regular_cardinal_alt
  strong_limit_cardinal_def
  countable_def
*)

val _ = export_theory()
