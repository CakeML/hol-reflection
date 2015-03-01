signature lcaLib = sig
  type thm = Abbrev.thm
  type term = Abbrev.term
  type update = reflectionLib.update

  val build_master_theorem :
    update list -> (* ctxt *)
    thm -> (* inner_ctxt extends lca_ctxt *)
    thm -> (* term_ok (sigof ctxt) inner_phi *)
    thm -> (* typeof inner_phi = Fun Num (Fun Num Bool) *)
    term -> (* phi *)
    thm
end
