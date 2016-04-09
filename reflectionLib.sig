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
  val pack_ctxt : update list -> thm
  val unpack_ctxt : thm -> update list
  val update_to_inner : update -> term
  type interpretation_cert = {
    good_context_thm : thm,
    models_thm : thm,
    wf_to_inners : thm list,
    sig_assums : thm list,
    int_assums : thm list
  }
  val build_interpretation : term list -> update list -> hol_type list -> term list -> interpretation_cert
  val build_ConstDef : (*extends_init*)thm -> (*def*)thm -> update * (*extends_init*)thm
  val termsem_cert : update list -> term -> thm
  val termsem_cert_unint : term -> thm
  val prop_to_loeb_hyp : update list -> term -> thm
  val prop_to_loeb_hyp0 : thm -> thm

  val mk_to_inner   : (hol_type,hol_type)Lib.subst -> hol_type -> term
  val to_inner_prop : (hol_type,hol_type)Lib.subst -> hol_type -> term
  val base_types_of_term : term -> hol_type list
  val base_terms_of_term : term -> term list

  val prove_wf_to_inner : hol_type -> thm

(*
  datatype axiomatic_update =
    NewType of hol_type
  | NewConstant of term
  | NewAxiom of thm

  val build_axiomatic_interpretation :
    (*axiom*)thm -> interpretation_cert
*)

end
