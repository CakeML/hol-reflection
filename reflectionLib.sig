signature reflectionLib = sig include Abbrev
  val mem : term
  val term_to_deep : term -> term
  type update = {
    sound_update_thm  : thm, (* |- sound_update ctxt upd *)
    constrainable_thm : thm, (* |- constrainable_update upd *)
    updates_thm : thm, (* |- upd updates ctxt *)
    extends_init_thm : thm, (* |- ctxt extends init_ctxt *)
    tys : hol_type list,
    consts : term list,
    axs : thm list }
  val update_to_inner : update -> term
  type interpretation_cert = {
    good_context_thm : thm,
    models_thm : thm,
    wf_to_inners : thm list,
    sig_assums : thm list,
    int_assums : thm list
  }
  val build_interpretation : update list -> hol_type list -> term list -> interpretation_cert
end
