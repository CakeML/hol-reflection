signature lcaLib = sig
  type thm = Abbrev.thm
  type term = Abbrev.term
  type update = reflectionLib.update

  val build_master_theorem :
    update list -> (* ctxt *)
    thm -> (* ctxt extends lca_ctxt *)
    thm -> (* term_ok (sigof ctxt) phi *)
    thm -> (* typeof phi = Fun Num (Fun Num Bool) *)
    term -> (* phi *)
    thm
end
