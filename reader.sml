open Opentheory OpenTheoryMap

(* TODO: move *)
val () = OpenTheory_tyop_name
  {tyop={Thy="min",Tyop="ind"},
   name=(string_to_otname"ind")}

val the_record = ref {
  name=({Thy="",Tyop=""}:thy_tyop),
  ax=TRUTH,
  args=([]:hol_type list),
  rep=({Thy="",Name=""}:thy_const),
  abs=({Thy="",Name=""}:thy_const)}

val (reader:reader) = {
  define_tyop = (fn r => (the_record := r; define_tyop_in_thy r)),
  define_const = define_const_in_thy I,
  axiom = axiom_in_db,
  const_name = (fn ot =>
    const_name_in_map ot
    handle NotFound => {Thy="scratch",Name=(snd ot)}),
  tyop_name = (fn ot =>
    if snd ot = "natural" then {Thy="scratch",Tyop="num"} else
     tyop_name_in_map ot)}

read_article "/tmp/natural-def.art" reader
!the_record
definitions "-"
definition"IND_SUC_def"
print_apropos``IND_SUC``
