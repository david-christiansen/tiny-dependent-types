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
  res {
    let! t = lex input |> parse
    let (State globEnv) = state
    let! typ = typecheck emptyEnv globEnv t
    let! result = eval t
    return (pprintTerm result, pprintTerm typ)
  } |> Result.fold
         (fun (x, y) ->
           printfn "  %s  :  %s" x y)
         (printf " Error: %s\n")

let rec loop (s : state) : unit =
  printf "\n> "
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
  printfn "Silly dependent type checker version 0.0.0.\n:q to quit."
  loop startState

main ()

