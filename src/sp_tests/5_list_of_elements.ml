effect Produce : int -> unit 

let rec string_of_int_list li : string = 
  match li with 
  | [] -> ""
  | x :: xs -> string_of_int x ^ "; " ^ string_of_int_list xs 

let rec pos li : bool =
  match li with 
  | [] -> true 
  | x :: xs -> if x <= 0 then false else pos xs 

let producer () 
(*@ requires (true, _^* )  @*)
(*@ ensures (true, Produce(3).Produce(5)) @*)
= 
  perform (Produce 3); 
  perform (Produce 5)


let main
(*@ requires (true, emp)  @*)
(*@ ensures (true, {l->[1]}.[pos(l)].{l->l++[3]}.[pos(l)].{l->l++[5]}) @*)

=
  let l = Sys.opaque_identity (ref [1]) in 
  print_string (string_of_int_list !l ^ "\n");
  match producer () with
  | v -> ()
  | effect (Produce x) k -> 
    assert (pos !l); 
    l := List.append (!l) [x]; 
    print_string (string_of_int_list !l ^ "\n");
    (continue k ())

(*      
For main:                                                          
{l->[1]}.Produce(3).Produce(5)
    currenct effects    continuation k                               stack /\ heap /\ assertion 
    --------------------------------------------------------------------------------
    {l->[1]}            Produce(3).Produce(5)                                l->[1]
    Produce(3)          [pos l].{l->l++[x]}.[pos l].Produce(5)        x=3 /\ l->[1]
    [pos l]             {l->l++[x]}.[pos l].Produce(5)                x=3 /\ l->[1]   /\ true 
    {l->l++[x]}         [pos l].Produce(5)                            x=3 /\ l->[1;3]
    [pos l]             Produce(5)                                    x=3 /\ l->[1;3] /\ true 
    Produce(5)          [pos l].{l->l++[x]}.[pos l]                   x=5 /\ l->[1;3] 
    [pos l]             {l->l++[x]}.[pos l]                           x=5 /\ l->[1;3] /\ true 
    {l->l++[x]}         [pos l]                                       x=5 /\ l->[1;3;5] 
    [pos l]             emp                                           x=5 /\ l->[1;3;5]/\true 
*)
 