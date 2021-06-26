(* Source code *)

type literal = 
    | INT of int
    | STRING of string
    | BOOL of bool
    
type expression = 
    | Unit
    | Variable of string
    | Literal of literal

type test = 
    | Drop 
    | Skip
    | Test of field * int 
    | Disj of test * test
    | Conj of test * test
    | Neg of test 
   
type probNetKAT = 
    | Filter of test
    | Assign of field * int 
    | Union of probNetKAT * probNetKAT 
    | Sequence of probNetKAT * probNetKAT
    | Choice of probNetKAT * probNetKAT * float 
    | Iteration of probNetKAT