open List
open Aez
open Smt

type result =
  | TRUE
  | FALSE
  | UNKNOWN
  
let declare_symbol name t_in t_out =
let x = Hstring.make name in (* creation d’un symbole *)
Symbol.declare x t_in t_out; (* declaration de son type *)
x

  

let define_prop eqs ok_ident = 
    (fun n ->  Formula.make_lit Formula.Eq [ Term.make_app ok_ident [n]; Term.t_true ] )

let define_delta eqs ok_ident =
    (fun n-> 
        let apply_n =
            (fun eq -> eq n) in
        let l = List.map apply_n eqs in
	    Formula.make Formula.And l
     )

module Base_solver = Smt.Make(struct end)

let prove_base k delta prop =
    Base_solver.clear ();
    for i=0 to k do
        Base_solver.assume ~id:0 (delta (Term.make_int (Num.Int i)));
    done;
    Base_solver.check();
    let l = ref([]) in
    for i=0 to k do
	l := (prop (Term.make_int (Num.Int i)) )::!l;
    done;
    Base_solver.entails ~id:0 (Formula.make Formula.And !l)

module Induction_solver = Smt.Make(struct end)

let prove_induction k delta prop =
    let n = Term.make_app (declare_symbol "n" [] Type.type_int) [] in
    let n_mv = ref(n) in
    Induction_solver.clear ();
    Induction_solver.assume ~id:0 (Formula.make_lit Formula.Le [Term.make_int (Num.Int 0); n]);
    for i=0 to (k-1) do 
	Induction_solver.assume ~id:0 (delta !n_mv);
	Induction_solver.assume ~id:0 (prop !n_mv);
	n_mv:= Term.make_arith Term.Plus !n_mv (Term.make_int (Num.Int 1));
    done;
    Induction_solver.assume ~id:0 (delta !n_mv);
    Induction_solver.check();
    Induction_solver.entails ~id:0 (prop !n_mv)



let prover eqs ok_ident =
    let delta = define_delta eqs ok_ident in
    let prop = define_prop eqs ok_ident in
    let k_max = 10 in 
    let rec prover_k k delta prop =
       if (k > k_max)
       then
	   UNKNOWN
       else
           let base = prove_base k delta prop in
           let induction = prove_induction k delta prop in
           if not base then FALSE
           else if induction then TRUE
           else prover_k (k+1) delta prop
     in
     prover_k 0 delta prop

