open Aez
open Smt
open Asttypes
open Typed_ast
open Ident
open Format

let formulas=ref []

let nfun f = fun n -> f

let nodes = Hashtbl.create 19

let nodenumcall = Hashtbl.create 19

(* liste des appels de node à traiter 
   Pour caque appel, il faut des variables locales DIFFERENTES *)
let nodecalls = ref []

let add_formula f = 
  (*Format.fprintf Format.std_formatter "@;Adding FORMULA :";
  Formula.print Format.std_formatter (f (Term.make_int (Num.Int(0))));*)
  formulas := f :: !formulas

let declare_symbol name t_in t_out =
  let x = Hstring.make name in (* creation d'un symbole *)
  print_string ("Declare "^name^"\n");
  Symbol.declare x t_in t_out; (* declaration de son type *)
  x

let of_ident ident ncall =
  (Ident.string_of ident ^ "__call" ^ string_of_int ncall)

let symbol_of ident ncall =
  Hstring.make (of_ident ident ncall)

(* Nombre de fonctions auxiliaires créées *)
let num_aux = ref 0

let nthcomp ident n ncall =
  of_ident ident ncall ^ "c_" ^ (string_of_int n)

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
  
let fixed_Formula_Make_And l =
   if List.tl(l) = []
   then
      List.hd(l)
   else
      Formula.make Formula.And l  


let declare_node nd ncall =
  let input = List.map (fun (id,t) -> declare_symbol (of_ident id ncall) 
    [ Type.type_int ] (translate_type t)) nd.tn_input in
  let app_input = List.map (fun t -> fun n -> Term.make_app t [n]) input in
  let output = List.map (fun (id,t) -> declare_symbol (of_ident id ncall) 
    [ Type.type_int ] (translate_type t)) nd.tn_output in
  let app_output = List.map (fun t -> fun n -> Term.make_app t [n]) output in
  let _ = List.map (fun (id,t) -> declare_symbol (of_ident id ncall) 
    [ Type.type_int ] (translate_type t)) nd.tn_local in
  (*let rec declare_output lst k =
    match lst,k with
      | [],_ -> ()
      | [id,t],0 -> 
	let smb=declare_symbol (ident_of nd.tn_name ncall) (List.map (fun (id,t) -> translate_type t) nd.tn_input) (translate_type t) in
	add_formula (fun n -> Formula.make_lit Formula.Eq [Term.make_app smb (app_input n); Term.make_app (symbol_of id ncall) [n]]); 
      | (id,t)::q,k -> 
	let smb=declare_symbol (nthcomp nd.tn_name k ncall) (List.map (fun (id,t) -> translate_type t) nd.tn_input) (translate_type t) in
	add_formula (fun n -> Formula.make_lit Formula.Eq [Term.make_app smb (app_input n); Term.make_app (symbol_of id ncall) [n]]); 
	declare_node q (k+1)
  in
  declare_output nd.tn_output 0; USELESS*)
  app_input,app_output

let single l =
  match l with
  | [e] -> e;
  | _ -> assert false
  
let translate_exprs e ncall =
  let rec translate_expr e =
  (* Traduit une expression en Smt.Term, avec éventuellement des effets de bord *)
    match e.texpr_desc with
      | TE_const(Cbool(true)) -> [nfun Term.t_true]
      | TE_const(Cbool(false)) -> [nfun Term.t_false]
      | TE_const(Cint(n)) -> [nfun (Term.make_int (Num.Int n))]
      | TE_const(Creal(f)) -> assert false;

      | TE_ident(i) -> [(fun n -> Term.make_app (symbol_of i ncall) [n])]

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
	      let [t1], [t2] = translate_expr e1, translate_expr e2 in (*t1 et t2 ne sont pas des tuples*)
	      fun n -> (Formula.make_lit (translate_cmp_op top) [t1 n;t2 n])
		
	    | Op_and | Op_or | Op_impl | Op_not -> 
	      let tlst=List.map translate_expr lst in
	      fun n -> Formula.make (translate_log_op ope) 
		(List.map (fun t -> Formula.make_lit Formula.Eq [(single t) n; Term.t_true]) tlst)
	    
	    | _ -> assert false )
	in
	add_formula (fun n -> (Formula.make Formula.And [ Formula.make Formula.Imp [ aux_n n; cmp n] ;
							  Formula.make Formula.Imp [ cmp n; aux_n n ] ]));
	[(fun n -> Term.make_app aux [n])]
	  
      | TE_op(Op_add | Op_sub | Op_mul | Op_div | Op_mod
		 | Op_add_f | Op_sub_f | Op_mul_f | Op_div_f as ope, [e1;e2]) ->
	let [t1], [t2] =translate_expr e1, translate_expr e2 in (*e1 et e2 n'ont pas le droit d'être des tuples *)
	[(fun n -> Term.make_arith (translate_arith_op ope) (t1 n) (t2 n))]

      | TE_op(Op_if, [e1;e2;e3]) ->
	let t1=single (translate_expr e1) in
	let t2=translate_expr e2 in
	let t3=translate_expr e3 in
	List.map2 (fun e2' e3' -> (fun n -> Term.make_ite (Formula.make_lit Formula.Eq [(t1 n); Term.t_true]) (e2' n) (e3' n))) t2 t3

      | TE_op(_,_) -> assert false

      | TE_app(ident,lst) -> 
	( match ident.kind with
	  | Node -> let nc=Hashtbl.find nodenumcall ident.name in
		    nodecalls := (ident.name,nc) :: !nodecalls;
		    Hashtbl.replace nodenumcall ident.name (nc+1);
		    let ndin, ndout=declare_node (Hashtbl.find nodes ident.name) nc in
		    let tlst=List.map (fun e -> single (translate_expr e)) lst in
		    List.iter2 (fun p t -> add_formula (fun n -> Formula.make_lit Formula.Eq [p n; t n])) 
		      ndin tlst;
		    ndout

	  (* j'ai un doute sur la possibilité de ce cas *)
	  | _ -> assert false(*let tlst = List.map translate_expr lst in
		 (fun n -> Term.make_app (symbol_of ident ncall) (List.map (fun t -> t n) tlst))*)
	)
	  
      | TE_prim(ident,lst) -> assert false (* Comment traiter int_of_float et float_of_int ? *)

      | TE_arrow(e1,e2) -> 
	let t1=translate_expr e1 in
	let t2=translate_expr e2 in
	List.map2 (fun  e1' e2'  -> (fun n -> Term.make_ite (Formula.make_lit Formula.Eq [n; Term.make_int (Num.Int 0)]) 
	  (e1' n) (e2' n))) t1 t2

      | TE_pre(e) -> 
	(match e.texpr_desc with
	  | TE_ident(ident) -> 
	    [(fun n -> Term.make_app (symbol_of ident ncall) [ Term.make_arith Term.Minus 
							  n (Term.make_int (Num.Int 1)) ])]
	  | _ ->
	    let te=translate_expr e in
	    let single_element e' =
	      let aux = declare_aux [ Type.type_int ] Type.type_bool in    
	      add_formula (fun n -> Formula.make_lit Formula.Eq [ Term.make_app aux [n]; e' n ]);
	      (fun n -> Term.make_app aux [ Term.make_arith Term.Minus 
					    n (Term.make_int (Num.Int 1)) ])
	    in List.map single_element te
	)
	  

      | TE_tuple(lst) -> List.map (fun e -> single(translate_expr e)) lst (* todo: tuples de tuples *)
  in
  translate_expr e

let translate_equs eqs ncall =
  let assign_expr_to_descr texpr descr =
    add_formula (fun n -> Formula.make_lit Formula.Eq [ Term.make_app (symbol_of descr ncall) [n] ; texpr n ])
  in
  let assign_exprs_to_descrs l_texpr l_descr =
    List.iter2 assign_expr_to_descr l_texpr l_descr
  in
  let write_eq eq =
    let l_texpr=translate_exprs eq.teq_expr ncall in
	assign_exprs_to_descrs l_texpr eq.teq_patt.tpatt_desc
  in
  List.iter write_eq eqs

let rec translate_node nd ncall =
  translate_equs nd.tn_equs ncall;
  match !nodecalls with
    | [] -> ()
    | (nd,k)::q -> nodecalls:=q; translate_node (Hashtbl.find nodes nd) k

let translate ft main =
  List.iter (fun t -> Hashtbl.add nodes t.tn_name.name t; 
    Hashtbl.add nodenumcall t.tn_name.name 0) ft;
  let mainnode=Hashtbl.find nodes main in
  let ok_ident=(let ident,_=List.hd mainnode.tn_output in of_ident ident 0) in
  let _ =declare_node mainnode 0 in
  translate_node mainnode 0;
  !formulas, (Hstring.make ok_ident)
