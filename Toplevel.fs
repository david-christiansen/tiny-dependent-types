module Toplevel

open Microsoft.FSharp.Text.Lexing
open System
open Mono.Terminal


open Nat
open AST
open Result
open Typechecker

type state = State of Global.env

let postulate x tp = function
  State (Global.Env defs) -> State (Global.Env ((x, Prim (x, tp), tp) :: defs))


let lex (str : String) : Lexing.LexBuffer<char> = Lexing.LexBuffer<char>.FromString(str)

let parse (lexbuf : Lexing.LexBuffer<char>) : command result =
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
    | Grammar.PIPE   -> "PIPE"
    | Grammar.ARROW -> "ARROW"
    | Grammar.COLON -> "COLON"
    | Grammar.ID x  -> "ID " + x
    | Grammar.DOT -> "DOT"
    | Grammar.LPAR -> "LPAR"
    | Grammar.RPAR -> "RPAR"
    | Grammar.SET  -> "SET"
    | Grammar.STRING x -> sprintf "STRING %A" x
    | Grammar.UNDERSCORE -> "UNDERSCORE"
    | Grammar.CMD_QUIT   -> "CMD_QUIT"
    | Grammar.CMD_POSTULATE   -> "CMD_POSTULATE"
    | Grammar.CMD_SHOWSTATE   -> "CMD_SHOWSTATE"
    | Grammar.CMD_DATADEF     -> "CMD_DATADEF"
    | Grammar.CMD_LOAD -> "CMD_LOAD"

let evaluate state expr =
  res {
    let (State globEnv) = state
    let! typ = typecheck emptyEnv globEnv expr
    let! result = eval expr
    return (pprintTerm result, pprintTerm typ)
  } |> Result.fold
         (fun (x, y) ->
           printfn "  %s  :  %s" x y)
         (printf " Error: %s\n")

let rec loop (le : LineEditor) (s : state) : unit =
  printf "\n"
  let input = le.Edit("> ","")

  lex input
  |> parse
  |> Result.fold (function
                  | Eval e -> evaluate s e ; loop le s
                  | Postulate (x, ty) -> loop le (postulate x ty s)
                  | ShowState -> showState s ; loop le s
                  | Load x -> printfn "loading %A" x ; loop le s
                  | DataDef (x,y,z) -> printfn "%A -- %A -- %A" x y z; loop le s
                  | Quit -> printfn "bye!")
                 (fun err -> printfn "%s" err ; loop le s)
and showState = function
  | State (Global.Env ss) ->
      for (x, defn, ty) in ss do
        printfn "%s  =  %s  :  %s" x (pprintTerm defn) (pprintTerm ty)

let startState : state =
  State Global.empty |>
  postulate "Bool" (Univ Z) |>
  postulate "true" (Free "Bool") |>
  postulate "false" (Free "Bool")

let main () : unit =
  let le = new LineEditor("sillytypes")

  printfn "Silly dependent type checker version 0.0.0.\n:q to quit."
  loop le startState

main ()

