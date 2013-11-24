open Aez
open Smt
open Asttypes
open Typed_ast
open Ident

let formulas=ref []

let add_formula f = 
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

let etranslate_expr e n =
  let rec translate_expr e =
  (* Traduit une expression en Smt.Term, avec éventuellement des effets de bord *)
  match e.texpr_desc with
    | TE_const(Cbool(true)) -> Term.t_true
    | TE_const(Cbool(false)) -> Term.t_false
    | TE_const(Cint(n)) -> Term.make_int (Num.Int n)
    | TE_const(Creal(f)) -> assert false;

    | TE_ident(i) -> Term.make_app (symbol_of i) [n]

    | TE_op((Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge 
		| Op_and | Op_or | Op_impl | Op_not as ope), lst) -> 
	    (* Op. bool. => Nécessité d'une variable auxiliaire + d'une formule *)
      let aux = declare_aux [ Type.type_int ] Type.type_bool in
      let aux_n n = (* aux(n) = true *)
	Formula.make_lit Formula.Eq [ Term.make_app aux [n]; Term.t_true ]
      in
      let cmp =
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
	    Formula.make_lit (translate_cmp_op top) [(translate_expr e1);(translate_expr e2)]
	      
	  | Op_and | Op_or | Op_impl | Op_not -> 
	    Formula.make (translate_log_op ope) 
	      (List.map (fun t -> Formula.make_lit Formula.Eq [translate_expr t; Term.t_true]) lst)

	  | _ -> assert false
      in
      add_formula (fun n -> (Formula.make Formula.And [ Formula.make Formula.Imp [ aux_n n; cmp ] ;
							Formula.make Formula.Imp [ cmp; aux_n n ] ]));
      Term.make_app aux [n]

    | TE_op(Op_add | Op_sub | Op_mul | Op_div | Op_mod
	       | Op_add_f | Op_sub_f | Op_mul_f | Op_div_f as ope, [e1;e2]) ->
      Term.make_arith (translate_arith_op ope) (translate_expr e1) (translate_expr e2)

    | TE_op(Op_if, [e1;e2;e3]) ->
      let t1=translate_expr e1 in
      let t2=translate_expr e2 in
      let t3=translate_expr e3 in
      Term.make_ite (Formula.make_lit Formula.Eq [t1; Term.t_true]) t2 t3

    | TE_op(_,_) -> assert false

    | TE_app(ident,lst) -> Term.make_app (symbol_of ident) (List.map translate_expr lst)

    | TE_prim(ident,lst) -> assert false (* Comment traiter int_of_float et float_of_int ? *)

    | TE_arrow(e1,e2) -> 
      Term.make_ite (Formula.make_lit Formula.Eq [n; Term.make_int (Num.Int 0)]) 
	(translate_expr e1) (translate_expr e2)

    | TE_pre(e) -> 
      (match e.texpr_desc with
	| TE_ident(ident) -> 
	  Term.make_app (symbol_of ident) [ Term.make_arith Term.Minus 
					      n (Term.make_int (Num.Int 1)) ]
	| _ ->
	  let aux = declare_aux [ Type.type_int ] Type.type_bool in
	  add_formula (fun n -> Formula.make_lit Formula.Eq [ Term.make_app aux [n]; (translate_expr e) ]);
	  Term.make_app aux [ Term.make_arith Term.Minus 
				n (Term.make_int (Num.Int 1)) ]
      )
	  

    | TE_tuple(lst) -> assert false (* ??? *)
  in
  translate_expr e
      

let translate_equs eqs =
  List.iter (fun eq -> add_formula (fun n -> (Formula.make_lit Formula.Eq 
						[ Term.make_app (symbol_of (List.hd eq.teq_patt.tpatt_desc)) [n];
						  etranslate_expr eq.teq_expr n ]))) eqs

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
  List.iter (fun t -> if t.tn_name.name=main then (let ident,_=List.hd t.tn_input in ok_ident:=Ident.string_of ident); 
    translate_node t) ft;
  !formulas, (Hstring.make !ok_ident)
