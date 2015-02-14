signature holDerivationLib = sig
  include Abbrev

  (* TODO: move to another lib? *)
  val EVAL_typeof : conv
  val EVAL_not_VFREE_IN : conv

  type reader = {
    theory_ok : thm, (* |- theory_ok thy *)
    axiom : thm list -> thm, (* map (|- term_ok thy) (c::h) -> |- (thy,h) |- c *)
    const : term -> thm,
     (* name -> |- FLOOKUP (tmsof thy) name = SOME ty0 *)
    typeOp : term -> thm
     (* name -> |- FLOOKUP (tysof thy) name = SOME arity *)
  }

  val readArticle : reader -> TextIO.instream -> thm Net.net

  val hol_ctxt_reader : reader

end
