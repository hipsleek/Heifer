
open Pretty


exception Foo of string



let () =
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
(*    let outputfile = (Sys.getcwd ()^ "/" ^ Sys.argv.(2)) in
print_string (inputfile ^ "\n" ^ outputfile^"\n");*)
  let ic = open_in inputfile in
  try
      let lines =  (input_lines ic ) in
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in
      let entailments = Parser.entialments Lexer.token (Lexing.from_string line) in
      
      entailments
      |> List.iteri (fun no str ->
         let case = Sleek.parse_specification str in
         let correct, verdict, history = Sleek.verify_specification case in
         "\n====================================\n"^
         (if correct then "Succeed\n" else "Fail\n")^
         Sleek.show_verification ~case ~no ~verdict ~verbose:(not correct) ~history |> print_endline;
         assert correct);


      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)

    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;
