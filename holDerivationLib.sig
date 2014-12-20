signature holDerivationLib = sig
  include Abbrev

  type reader = {
    theory_ok : thm, (* |- theory_ok thy *)
    axiom : term -> thm option, (* c -> |- c ∈ axsof thy *)
    const : term -> thm,
     (* name -> |- FLOOKUP (tmsof thy) name = SOME ty0 *)
    typeOp : term -> thm
     (* name -> |- FLOOKUP (tysof thy) name = SOME arity *)
  }

  val readArticle : reader -> TextIO.instream -> thm Net.net

end
