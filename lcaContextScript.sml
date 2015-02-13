open HolKernel boolLib bossLib lcsymtacs
val _ = new_theory"lcaContext"

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
SUC_REP: ConstSpec infinity_ax
(* POW *)
ConstDef:
  val POW_alt = METIS_PROVE[EXTENSION,IN_DEF,IN_POW]``POW s x ⇔ x ⊆ s``
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
