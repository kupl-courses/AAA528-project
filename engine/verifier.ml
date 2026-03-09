open Utils 
open Program 


(* Implement a partial correctness verifier *)
let verify : Args.t -> Syntax.pgm -> bool 
=fun args pgm -> ignore (args, pgm); raise (Failure "Not_implemented: Verifier.verify")
