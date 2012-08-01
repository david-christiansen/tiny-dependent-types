module Toplevel

open Microsoft.FSharp.Text.Lexing
open System


open Nat
open AST
open Result
open Typechecker

type state = State of Global.env

let lex (str : String) : Lexing.LexBuffer<char> = Lexing.LexBuffer<char>.FromString(str)

let parse (lexbuf : Lexing.LexBuffer<char>) : term result =
  try
    lexbuf |> Grammar.parse Lexical.token |> Result.Success
  with
    | exn -> let pos = lexbuf.EndPos
             in Result.Failure <| sprintf "%s near line %d, column %d\n"
                                    (exn.Message) (pos.Line+1) pos.Column

let printToken (tok : Grammar.token) : string =
  match tok with
    | Grammar.EOF -> "EOF"
    | Grammar.PI  -> "PI"
    | Grammar.LAMBDA -> "LAMBDA"
    | Grammar.ARROW -> "ARROW"
    | Grammar.COLON -> "COLON"
    | Grammar.ID x  -> "ID " + x
    | Grammar.DOT -> "DOT"
    | Grammar.LPAR -> "LPAR"
    | Grammar.RPAR -> "RPAR"
    | Grammar.SET  -> "SET"
    | Grammar.UNDERSCORE -> "UNDERSCORE"

let tryParse state input =
(*  seq {
    let lexbuf = lex input
    while not lexbuf.IsPastEndOfStream do
      match Lexical.token lexbuf with
        | Grammar.EOF -> yield! []
        | tok -> yield tok
  } |> Seq.map printToken |> Seq.reduce (fun x y -> x + ", " + y) |> printf "Lexer result: %s\n"*)
  let parsed = lex input |> parse
  //Result.fold (fun x -> printf "Parsed %s\n" (pprintTerm x)) (printf "%s\n") parsed
  res {
    let! t = parsed
    let (State globEnv) = state
    let! typ = typecheck emptyEnv globEnv t
    return (pprintTerm t, pprintTerm typ)
  } |> Result.fold
         (fun (x, y) ->
           printf "Typechecking yielded:\n %A  :  %A\n" x y)
         (printf "No type: %s\n")
  res {
    let! t = parsed
    let! result = eval t
    return pprintTerm result
  } |> Result.fold (printf "Result: %s\n") (printf "%s\n")

let rec loop (s : state) : unit =
  printf "> "
  let input = Console.ReadLine ()
  if input = ":q" || input = ":quit"
  then printf "bye!\n"
  else tryParse s input ; loop s

let postulate x tp = function
  State (Global.Env defs) -> State (Global.Env ((x, Prim (x, tp), tp) :: defs))

let startState : state =
  State Global.empty |>
  postulate "Bool" (Univ Z) |>
  postulate "true" (Free "Bool") |>
  postulate "false" (Free "Bool")


let main () : unit =
  loop startState

main ()

