
let (mutlist:(((int ref) list) ref)) = ref [ref 2]


let set_all_zero li = List.map (fun a -> a := 0) (!li)  ;;


set_all_zero (mutlist);;

assert (!mutlist = [ref 0]);;