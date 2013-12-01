open Aez
open Smt
open Asttypes
open Typed_ast
open Ident
open Format


(* Pour retrouver facilement les nodes, les traiter dans l'ordre des appels,
   et différencier les noms de variables de chaque appel *)

let nodes = Hashtbl.create 19

let nodenumcall = Hashtbl.create 19

(* liste des appels de node à traiter 
   Pour caque appel, il faut des variables locales DIFFERENTES *)
let nodecalls = ref []


(* Stocke les formules associées au programme *)
let formulas=ref []

let nfun f = fun n -> f

let add_formula f = 
  formulas := f :: !formulas

let declare_symbol name t_in t_out =
  let x = Hstring.make name in (* creation d'un symbole *)
  Symbol.declare x t_in t_out; (* declaration de son type *)
  x

let of_ident ident ncall =
  (Ident.string_of ident ^ "__call" ^ string_of_int ncall)

let symbol_of ident ncall =
  Hstring.make (of_ident ident ncall)

(* Nombre de variables auxiliaires créées *)
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

(* Déclaration des variables pour un nouvel appel d'un node *)

let declare_node nd ncall =
  let input = List.map (fun (id,t) -> declare_symbol (of_ident id ncall) 
    [ Type.type_int ] (translate_type t)) nd.tn_input in
  let app_input = List.map (fun t -> fun n -> Term.make_app t [n]) input in
  let output = List.map (fun (id,t) -> declare_symbol (of_ident id ncall) 
    [ Type.type_int ] (translate_type t)) nd.tn_output in
  let app_output = List.map (fun t -> fun n -> Term.make_app t [n]) output in
  let _ = List.map (fun (id,t) -> declare_symbol (of_ident id ncall) 
    [ Type.type_int ] (translate_type t)) nd.tn_local in
  app_input,app_output

let rec encodage_flottant f =
(* Codage de flottant = (puissance de 2)*mantisse de longueur bornée
  on va convertir en Num.Ratio ou Num.Int*)
  if f < 0.
    then
    Num.minus_num (encodage_flottant (-. f))
  else if floor f = f (* inclut f = 0*)
    then
    Num.Int (int_of_float f)
  else
    Num.quo_num (encodage_flottant (2. *. f)) (Num.Int 2) 
    (* nombre d'appel borné car mantisse bornée*)

(* Renvoie la tête d'une liste d'un seul élément *)
let single l =
  match l with
  | [e] -> e;
  | _ -> assert false

(* Traduction des expressions. ncall est le numéro d'appel du node
   pour différencier les appels *)
let translate_exprs e ncall =
  let rec translate_expr e =
  (* Traduit une expression en ([n] -> Smt.Term) list, 
     en générant par effet de bord des formules annexes *)
    match e.texpr_desc with
      | TE_const(Cbool(true)) -> [nfun Term.t_true]
      | TE_const(Cbool(false)) -> [nfun Term.t_false]
      | TE_const(Cint(n)) -> [nfun (Term.make_int (Num.Int n))]
      | TE_const(Creal(f)) -> [nfun (Term.make_int (encodage_flottant f))];

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
		| [a; b] -> a,b
		| _ -> assert false
	      in
	      let top,e1,e2 = match ope with 
		| Op_gt -> Op_lt, te2, te1 (* pas de > / >= dans SMT *)
		| Op_ge -> Op_le, te2, te1
		| o -> o, te1, te2
	      in
	      let [t1], [t2] = translate_expr e1, translate_expr e2 in 
	      (* t1 et t2 ne peuvent pas être des tuples *)
	      fun n -> (Formula.make_lit (translate_cmp_op top) [t1 n;t2 n])
		
	    | Op_and | Op_or | Op_impl | Op_not -> 
	      let tlst=List.map translate_expr lst in
	      fun n -> Formula.make (translate_log_op ope) 
		(List.map 
		   (fun t -> Formula.make_lit Formula.Eq [(single t) n; 
							  Term.t_true]) 
		   tlst)
	    
	    | _ -> assert false )
	in
	add_formula (fun n -> 
	  (Formula.make Formula.And 
	     [ Formula.make Formula.Imp [ aux_n n; cmp n] ;
	       Formula.make Formula.Imp [ cmp n; aux_n n ] ]));
	[(fun n -> Term.make_app aux [n])]
	  
      | TE_op(Op_add | Op_sub | Op_mul | Op_div | Op_mod
		 | Op_add_f | Op_sub_f | Op_mul_f | Op_div_f as ope, [e1;e2]) ->
	let [t1], [t2] =translate_expr e1, translate_expr e2 in 
	(* e1 et e2 n'ont pas le droit d'être des tuples *)
	[(fun n -> Term.make_arith (translate_arith_op ope) (t1 n) (t2 n))]

      | TE_op(Op_if, [e1; e2; e3]) ->
	let t1=single (translate_expr e1) in
	let t2=translate_expr e2 in
	let t3=translate_expr e3 in
	List.map2 (fun e2' e3' -> 
	  (fun n -> Term.make_ite (Formula.make_lit Formula.Eq [(t1 n); 
								Term.t_true]) 
	    (e2' n) (e3' n))) t2 t3

      | TE_op(_,_) -> assert false (* Cas impossible syntaxiquement *)

      | TE_app(ident,lst) -> 
	( match ident.kind with
	  | Node -> 
	    (* Nouvel appel de node, il faut le signaler 
	       pour qu'il soit traité plus tard *)
	    let nc=Hashtbl.find nodenumcall ident.name in
	    nodecalls := (ident.name,nc) :: !nodecalls;
	    Hashtbl.replace nodenumcall ident.name (nc+1);
	    (* Déclaration et récupération des canaux d'entrée et sortie *)
	    let ndin, ndout=declare_node (Hashtbl.find nodes ident.name) nc in
	    let tlst=List.map (fun e -> single (translate_expr e)) lst in
	    (* Association des canaux d'entrées *)
	    List.iter2 (fun p t -> add_formula 
	      (fun n -> Formula.make_lit Formula.Eq [p n; t n])) 
	      ndin tlst;
	    ndout

	  | _ -> assert false
	)
	  
      | TE_prim(ident,lst) -> assert false 
      (* Comment traiter int_of_float et float_of_int ? *)

      | TE_arrow(e1,e2) -> 
	let t1=translate_expr e1 in
	let t2=translate_expr e2 in
	List.map2 (fun  e1' e2'  -> 
	  (fun n -> Term.make_ite 
	    (Formula.make_lit Formula.Eq [n; Term.make_int (Num.Int 0)]) 
	  (e1' n) (e2' n))) t1 t2

      | TE_pre(e) -> 
	(match e.texpr_desc with
	  | TE_ident(ident) -> 
	    (* Traitement direct : pas de tuple possible *)
	    [(fun n -> Term.make_app (symbol_of ident ncall) 
	      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ])]
	  | _ ->
	    let te=translate_expr e in
	    let single_element e' tpe =
	      (* Traitement élément par élément du tuple *)
	      let aux = declare_aux [ Type.type_int ] (translate_type tpe) in
	      add_formula (fun n -> 
		Formula.make_lit Formula.Eq [ Term.make_app aux [n]; e' n ]);
	      (fun n -> Term.make_app aux [ Term.make_arith Term.Minus 
					    n (Term.make_int (Num.Int 1)) ])
	    in
	    let rec handle_pre es tps =
	      (match (es,tps) with
		| [],[] -> []
		| ex::q,t::r -> single_element ex t :: handle_pre q r
		| _ -> assert false)
	    in
	    handle_pre te e.texpr_type
	)

      | TE_tuple(lst) -> List.map (fun e -> single (translate_expr e)) lst
	(* Tuple de tuples -> non typable *)
  in
  translate_expr e


(* Traduction des équations à l'intérieur d'un Node *)
let translate_equs eqs ncall =
  (* Assignation d'une variable (simple) à son expression *)
  let assign_expr_to_descr texpr descr =
    add_formula (fun n -> 
      Formula.make_lit Formula.Eq [ Term.make_app (symbol_of descr ncall) [n];
				    texpr n ])
  in
  (* Pour les tuples *)
  let assign_exprs_to_descrs l_texpr l_descr =
    List.iter2 assign_expr_to_descr l_texpr l_descr
  in
  let write_eq eq =
    let l_texpr=translate_exprs eq.teq_expr ncall in
	assign_exprs_to_descrs l_texpr eq.teq_patt.tpatt_desc
  in
  List.iter write_eq eqs

(* Traduction de chaque appel de Node *)
let rec translate_node nd ncall =
  translate_equs nd.tn_equs ncall;
  match !nodecalls with
    | [] -> ()
    | (nd,k)::q -> nodecalls:=q; translate_node (Hashtbl.find nodes nd) k

(* Traduction de tout le fichier *)
let translate ft main =
  List.iter (fun t -> Hashtbl.add nodes t.tn_name.name t; 
    Hashtbl.add nodenumcall t.tn_name.name 0) ft;
  let mainnode=Hashtbl.find nodes main in
  let ok_ident=(let ident,_=List.hd mainnode.tn_output in of_ident ident 0) in
  let _ =declare_node mainnode 0 in
  translate_node mainnode 0;
  !formulas, (Hstring.make ok_ident)
