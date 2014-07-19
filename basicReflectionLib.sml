structure basicReflectionLib = struct
local
  open HolKernel boolLib bossLib holSyntaxSyntax listSyntax pairSyntax stringSyntax
in

fun n_imp_and_intro 0 = ALL_CONV
  | n_imp_and_intro n = REWR_CONV (GSYM AND_IMP_INTRO) THENC
                       (RAND_CONV (n_imp_and_intro (n-1)))

datatype type_view = Tyvar of string | Tyapp of string * string * hol_type list

local open String in
fun tyvar_to_deep s =
  if sub(s,0) = #"'" then
    if size s = 2 then str(Char.toUpper (sub(s,1)))
    else extract(s,1,NONE)
  else s
end

fun type_view (ty : hol_type) =
  if is_type ty then
    case dest_thy_type ty of { Args = args, Thy = thy, Tyop = tyop } =>
      Tyapp (thy, tyop, args)
  else
    Tyvar (tyvar_to_deep (dest_vartype ty))

fun type_to_deep ty = case type_view ty of
    Tyvar name => mk_Tyvar (fromMLstring name)
  | Tyapp (thy,name,args) =>
      mk_Tyapp(fromMLstring name, mk_list(List.map type_to_deep args, type_ty))

fun term_to_deep tm =
  case dest_term tm of
    VAR(x,ty) => mk_Var(fromMLstring x, type_to_deep ty)
  | CONST {Name,Thy,Ty} => mk_Const(fromMLstring Name, type_to_deep Ty)
  | COMB (f,x) => mk_Comb(term_to_deep f, term_to_deep x)
  | LAMB (x,b) =>
      let
        val (x,ty) = dest_var x
      in
        mk_Abs(fromMLstring x, type_to_deep ty, term_to_deep b)
      end

fun underscores [] = ""
  | underscores (x::xs) = "_" ^ x ^ underscores xs

fun type_name (ty : hol_type) = case type_view ty of
    Tyvar name            => tyvar_to_deep name
  | Tyapp (thy,tyop,args) => tyop ^ underscores (map type_name args)

val U = mk_vartype("'U")
fun mk_in_var (ty : hol_type) =
  mk_var ("in_" ^ type_name ty, ty --> U)

val mem = ``mem:'U->'U->bool``
local
  open holSemanticsTheory
  fun genv x = (* genvar (type_of x) *)
    variant [] x
in
  val tysig = genv ``tysig:tysig``
  val tmsig = genv ``tmsig:tmsig``
  val tyass = genv ``tyass:'U tyass``
  val tmass = genv ``tmass:'U tmass``
  val tyval = genv ``tyval:'U tyval``
  val tmval = genv ``tmval:'U tmval``
end

val signatur = mk_pair(tysig,tmsig)
val interpretation = mk_pair(tyass,tmass)
val valuation = mk_pair(tyval,tmval)
val termsem_tm = ``termsem0 ^mem``
fun mk_termsem d =
  list_mk_comb(termsem_tm,[tmsig,interpretation,valuation,d])

val EVAL_STRING_SORT =
  CONV_TAC (DEPTH_CONV (fn tm => if can (match_term ``STRING_SORT (tyvars X)``) tm
                        then EVAL tm else raise UNCHANGED))

(* given [...,A,...] |- P and H |- A <=> B1 /\ ... /\ Bn
   produce [...,B1,...,Bn,...] ∪ H |- P *)
fun simplify_assum th simpth =
  let
    val A = lhs(concl simpth)
    val th1 = DISCH A th
    val th2 = CONV_RULE(LAND_CONV(REWR_CONV simpth)) th1
    val n = length(strip_conj(rhs(concl simpth)))
    val th3 = CONV_RULE (n_imp_and_intro (n-1)) th2
  in
    funpow n UNDISCH th3
  end

(* given [...,A',...] |- P and H |- !x1..xn. B1 /\ ... /\ Bn ==> A
   produce [...,B1',...,Bn',...] ∪ H |- P *)
fun replace_assum th simpth =
  let
    val c = simpth |> concl
    val (xs,b) = c |> strip_forall
    val (B,A) = dest_imp b handle HOL_ERR _ => (T,b)
    val A' = first (can (match_term A)) (hyp th)
    val th1 = DISCH A' th
    val (s,_) = match_term A A'
    val th2 = ISPECL (map (fn x => #residue(first (equal (fst(dest_var x)) o fst o dest_var o #redex) s)) xs) simpth
    val n = B |> strip_conj |> length
    val th3 = CONV_RULE (n_imp_and_intro (n-1)) th2
    val th4 = funpow n UNDISCH th3 handle HOL_ERR _ => th3
  in
    MP th1 th4
  end

end
end
