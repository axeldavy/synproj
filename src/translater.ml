open Aez
open Smt
open Asttypes
open Typed_ast
open Ident
open Format

let formulas=ref []

let nfun f = fun n -> f

let add_formula f = 
  (*Format.fprintf Format.std_formatter "@;Adding FORMULA :";
  Formula.print Format.std_formatter (f (Term.make_int (Num.Int(0))));*)
  formulas := f :: !formulas

let declare_symbol name t_in t_out =
  let x = Hstring.make name in (* creation d'un symbole *)
  Symbol.declare x t_in t_out; (* declaration de son type *)
  x

let symbol_of ident =
  Hstring.make (Ident.string_of ident)

let num_aux = ref 0

let declare_aux t_in t_out =
  incr num_aux;
  declare_symbol ("aux"^ (string_of_int !num_aux)) t_in t_out

let translate_log_op = function
  | Op_and -> Formula.And
  | Op_or -> Formula.Or
  | Op_impl -> Formula.Imp
  | Op_not -> Formula.Not
  | _ -> assert false

let translate_cmp_op = function 
  | Op_eq -> Formula.Eq
  | Op_lt -> Formula.Lt
  | Op_le -> Formula.Le
  | Op_neq-> Formula.Neq
  | _ -> assert false

let translate_arith_op = function
  | Op_add | Op_add_f -> Term.Plus
  | Op_sub | Op_sub_f -> Term.Minus
  | Op_mul | Op_mul_f -> Term.Mult
  | Op_div | Op_div_f -> Term.Div
  | Op_mod -> Term.Modulo
  | _ -> assert false

let translate_type = function
  | Tbool -> Type.type_bool
  | Tint -> Type.type_int
  | Treal -> Type.type_real

let rec translate_expr e =
  (* Traduit une expression en Smt.Term, avec éventuellement des effets de bord *)
  match e.texpr_desc with
    | TE_const(Cbool(true)) -> nfun Term.t_true
    | TE_const(Cbool(false)) -> nfun Term.t_false
    | TE_const(Cint(n)) -> nfun (Term.make_int (Num.Int n))
    | TE_const(Creal(f)) -> assert false;

    | TE_ident(i) -> (fun n -> Term.make_app (symbol_of i) [n])

    | TE_op((Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge 
		| Op_and | Op_or | Op_impl | Op_not as ope), lst) -> 
	    (* Op. bool. => Nécessité d'une variable auxiliaire + d'une formule *)
      let aux = declare_aux [ Type.type_int ] Type.type_bool in
      let aux_n n = (* aux(n) = true *)
	Formula.make_lit Formula.Eq [ Term.make_app aux [n]; Term.t_true ]
      in
      let cmp = (
	match ope with
	  | Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge ->
	    let te1,te2 = match lst with
	      | [a;b] -> a,b
	      | _ -> assert false
	    in
	    let top,e1,e2 = match ope with 
	      | Op_gt -> Op_lt, te2, te1
	      | Op_ge -> Op_le, te2, te1
	      | o -> o, te1, te2
	    in
	    let t1, t2 = translate_expr e1, translate_expr e2 in
	    fun n -> (Formula.make_lit (translate_cmp_op top) [t1 n;t2 n])
	      
	  | Op_and | Op_or | Op_impl | Op_not -> 
	    let tlst=List.map translate_expr lst in
	    fun n -> Formula.make (translate_log_op ope) 
	      (List.map (fun t -> Formula.make_lit Formula.Eq [t n; Term.t_true]) tlst)

	  | _ -> assert false )
      in
      add_formula (fun n -> (Formula.make Formula.And [ Formula.make Formula.Imp [ aux_n n; cmp n] ;
							Formula.make Formula.Imp [ cmp n; aux_n n ] ]));
      fun n -> Term.make_app aux [n]

    | TE_op(Op_add | Op_sub | Op_mul | Op_div | Op_mod
	       | Op_add_f | Op_sub_f | Op_mul_f | Op_div_f as ope, [e1;e2]) ->
      let t1, t2=translate_expr e1, translate_expr e2 in
      fun n -> Term.make_arith (translate_arith_op ope) (t1 n) (t2 n)

    | TE_op(Op_if, [e1;e2;e3]) ->
      let t1=translate_expr e1 in
      let t2=translate_expr e2 in
      let t3=translate_expr e3 in
      fun n -> Term.make_ite (Formula.make_lit Formula.Eq [(t1 n); Term.t_true]) (t2 n) (t3 n)

    | TE_op(_,_) -> assert false

    | TE_app(ident,lst) -> 
      let tlst = List.map translate_expr lst in
      fun n -> Term.make_app (symbol_of ident) (List.map (fun t -> t n) tlst)

    | TE_prim(ident,lst) -> assert false (* Comment traiter int_of_float et float_of_int ? *)

    | TE_arrow(e1,e2) -> 
      let t1=translate_expr e1 in
      let t2=translate_expr e2 in
      fun n -> Term.make_ite (Formula.make_lit Formula.Eq [n; Term.make_int (Num.Int 0)]) 
	(t1 n) (t2 n)

    | TE_pre(e) -> 
      (match e.texpr_desc with
	| TE_ident(ident) -> 
	  fun n -> Term.make_app (symbol_of ident) [ Term.make_arith Term.Minus 
					      n (Term.make_int (Num.Int 1)) ]
	| _ ->
	  let aux = declare_aux [ Type.type_int ] Type.type_bool in
	  let te=translate_expr e in
	  add_formula (fun n -> Formula.make_lit Formula.Eq [ Term.make_app aux [n]; te n ]);
	  fun n -> Term.make_app aux [ Term.make_arith Term.Minus 
					 n (Term.make_int (Num.Int 1)) ]
      )
	  

    | TE_tuple(lst) -> assert false (* ??? *)
      

let translate_equs eqs =
  List.iter (fun eq -> let texpr=translate_expr eq.teq_expr in
		       add_formula (fun n -> (Formula.make_lit Formula.Eq 
						[ Term.make_app (symbol_of (List.hd eq.teq_patt.tpatt_desc)) [n];
						  texpr n ]))) eqs

let translate_node nd =
  let _ = List.map (fun (id,t) -> declare_symbol (Ident.string_of id) 
    [ Type.type_int ] (translate_type t)) nd.tn_input in
  let _ = List.map (fun (id,t) -> declare_symbol (Ident.string_of id) 
    [ Type.type_int ] (translate_type t)) nd.tn_output in
  let _ = List.map (fun (id,t) -> declare_symbol (Ident.string_of id) 
    [ Type.type_int ] (translate_type t)) nd.tn_local in
  translate_equs nd.tn_equs

let translate ft main =
  let ok_ident=ref "" in
  List.iter (fun t -> if t.tn_name.name=main then (let ident,_=List.hd t.tn_output in ok_ident:=Ident.string_of ident); 
    translate_node t) ft;
  !formulas, (Hstring.make !ok_ident)
