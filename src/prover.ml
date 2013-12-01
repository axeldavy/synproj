open List
open Aez
open Smt
open Format

type result =
  | TRUE
  | FALSE
  | UNKNOWN
  
let declare_symbol name t_in t_out =
let x = Hstring.make name in (* creation d’un symbole *)
Symbol.declare x t_in t_out; (* declaration de son type *)
x

let handle_error error =
   Format.fprintf Format.std_formatter "erreur détectée dans le prouveur: ";
   match (error) with
   |DuplicateTypeName(ht) -> Format.fprintf Format.std_formatter "type déjà déclaré: ";
   |DuplicateSymb(ht) -> Format.fprintf Format.std_formatter "Symbole dupliqué: ";
   |UnknownType(ht) -> Format.fprintf Format.std_formatter "Type non déclaré: ";
   |UnknownSymb(ht) -> Format.fprintf Format.std_formatter "Symbole non déclarée: ";
   Hstring.print Format.std_formatter ht;
   Format.fprintf Format.std_formatter "@;"

let fixed_Formula_Make_And l =
   if tl(l) = []
   then
      hd(l)
   else
      Formula.make Formula.And l
      
let fixed_Formula_Make_Or l =
   if tl(l) = []
   then
      hd(l)
   else
      Formula.make Formula.Or l 

let define_prop eqs ok_ident = 
    (fun n ->  Formula.make_lit Formula.Eq [ Term.make_app ok_ident [n]; Term.t_true ] )

let define_delta eqs ok_ident =
    (fun n-> 
        let apply_n =
            (fun eq -> eq n) in
        let l = List.map apply_n eqs in
	    fixed_Formula_Make_And l
     )

module Base_solver = Smt.Make(struct end)

let prove_base k delta prop verbose =
    Base_solver.clear ();
    for i=0 to k do
        if (verbose)
        then
        begin
            Format.fprintf Format.std_formatter "base delta : " ;
            Formula.print Format.std_formatter (delta (Term.make_int (Num.Int i)));
            Format.fprintf Format.std_formatter "@;";
	end;
        Base_solver.assume ~id:0 (delta (Term.make_int (Num.Int i)));
    done;
    Base_solver.check();
    let l = ref([]) in
    for i=0 to k do
	l := (prop (Term.make_int (Num.Int i)) )::!l;
	if (verbose)
        then
        begin
            Format.fprintf Format.std_formatter "base prop: " ;
            Formula.print Format.std_formatter (prop (Term.make_int (Num.Int i)) );
            Format.fprintf Format.std_formatter "@;";
	end;
    done;
    Base_solver.entails ~id:0 (fixed_Formula_Make_And !l)

module Induction_solver = Smt.Make(struct end)

let prove_induction k delta prop verbose=
    let n = Term.make_app (Hstring.make "n") [] in
    let n_mv = ref(n) in
    Induction_solver.clear ();
    Induction_solver.assume ~id:0 (Formula.make_lit Formula.Le [Term.make_int (Num.Int 0); n]);
    for i=0 to (k-1) do 
        if (verbose)
        then
        begin
            Format.fprintf Format.std_formatter "induction delta : " ;
            Formula.print Format.std_formatter (delta !n_mv);
            Format.fprintf Format.std_formatter "@;";
            Format.fprintf Format.std_formatter "induction prop hypothesis : " ;
            Formula.print Format.std_formatter (prop !n_mv);
            Format.fprintf Format.std_formatter "@;";
	end;
	Induction_solver.assume ~id:0 (delta !n_mv);
	Induction_solver.assume ~id:0 (prop !n_mv);
	n_mv:= Term.make_arith Term.Plus !n_mv (Term.make_int (Num.Int 1));
    done;
    if (verbose)
    then
    begin
        Format.fprintf Format.std_formatter "induction delta : " ;
        Formula.print Format.std_formatter (delta !n_mv);
        Format.fprintf Format.std_formatter "@;";
    end;
    Induction_solver.assume ~id:0 (delta !n_mv);
    Induction_solver.check();
    if (verbose)
    then
    begin
        Format.fprintf Format.std_formatter "induction prop to show : " ;
        Formula.print Format.std_formatter (prop !n_mv);
        Format.fprintf Format.std_formatter "@;";
    end;
    Induction_solver.entails ~id:0 (prop !n_mv)



let prover eqs ok_ident verbose =
    let delta = define_delta eqs ok_ident in
    let prop = define_prop eqs ok_ident in
    let k_max = 10 in 
    let rec prover_k k delta prop =
       if (k > k_max)
       then
	   UNKNOWN
       else
           let base = prove_base k delta prop verbose in
           let induction = prove_induction k delta prop verbose in
           if not base then FALSE
           else if induction then TRUE
           else begin 
                if (verbose)
                then
		  Format.fprintf Format.std_formatter "\n";
		prover_k (k+1) delta prop
		end
     in
     try
        ignore(declare_symbol "n" [] Type.type_int);
        prover_k 0 delta prop
     with |Smt.Error(error) ->
       handle_error error;
       UNKNOWN

