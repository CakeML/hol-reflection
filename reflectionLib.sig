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
  val build_interpretation : update list -> hol_type list -> term list -> thm
end
