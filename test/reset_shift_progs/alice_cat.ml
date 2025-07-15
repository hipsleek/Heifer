let alice_cat ()
(*@ ens res = "Alice has a dog and the dog has a bone." @*)
= "Alice" ^ reset(" has " ^ shift (fun k -> (k "a dog" ^ " and the dog" ^ k "a bone.")))
