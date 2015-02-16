signature holSyntaxLib = sig
  include Abbrev

  val EVAL_typeof : conv
  val EVAL_welltyped : conv

  val EVAL_orda : conv
  val EVAL_SORTED_alpha_lt : conv
  val EVAL_ACONV : conv

  val EVAL_match_type : conv

  val EVAL_not_VFREE_IN : conv

  val EVAL_subst : conv

  val EVAL_hypset : conv

  val add_type_info : computeLib.compset -> unit

  val fix_list_compset : computeLib.compset -> unit
end
