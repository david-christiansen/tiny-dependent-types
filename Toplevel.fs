(*
----------------------------------------------------------------------
Copyright (c) 2012 David Raymond Christiansen

Permission is hereby granted, free of charge, to any person
obtaining a copy of this software and associated documentation
files (the "Software"), to deal in the Software without
restriction, including without limitation the rights to use, copy,
modify, merge, publish, distribute, sublicense, and/or sell copies
of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

 * The above copyright notice and this permission notice shall be
  included in all copies or substantial portions of the Software.

 * The software is provided "as is", without warranty of any kind,
  express or implied, including but not limited to the warranties of
  merchantability, fitness for a particular purpose and
  noninfringement.  In no event shall the authors or copyright
  holders be liable for any claim, damages or other liability,
  whether in an action of contract, tort or otherwise, arising from,
  out of or in connection with the software or the use or other
  dealings in the software.
----------------------------------------------------------------------
*)

module Toplevel

open Microsoft.FSharp.Text.Lexing
open System
open Mono.Terminal


open Nat
open AST
open Result
open Typechecker

type state = State of Global.env

let stateContains (s : state) (x : string) : (string * term * term) option =
  let rec findName = function
    | [] -> None
    | (x', tm, tp) :: _ when x = x' -> Some (x', tm, tp)
    | _ :: defs -> findName defs
  match s with
    | State (Global.Env defs) -> findName defs

let postulate x tp = function
  State (Global.Env defs) -> State (Global.Env ((x, Postulated (x, tp), tp) :: defs))

let define x tm tp = function
  State (Global.Env defs) -> State (Global.Env ((x, tm, tp) :: defs))


let lex (str : String) : Lexing.LexBuffer<char> = Lexing.LexBuffer<char>.FromString(str)

let parse (lexbuf : Lexing.LexBuffer<char>) : command result =
  try
    lexbuf |> Grammar.command Lexical.token |> Result.Success
  with
    | exn -> let pos = lexbuf.EndPos
             in Result.Failure <| sprintf "%s near line %d, column %d\n"
                                    (exn.Message) (pos.Line+1) pos.Column

let printToken (tok : Grammar.token) : string =
  match tok with
    | Grammar.EOF -> "EOF"
    | Grammar.SEPARATOR -> "SEPARATOR"
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
    | Grammar.MAKE_EQUAL -> "MAKE_EQUAL"
    | Grammar.STRING x -> sprintf "STRING %A" x
    | Grammar.UNDERSCORE -> "UNDERSCORE"
    | Grammar.CMD_QUIT   -> "CMD_QUIT"
    | Grammar.CMD_POSTULATE   -> "CMD_POSTULATE"
    | Grammar.CMD_SHOWSTATE   -> "CMD_SHOWSTATE"
    | Grammar.CMD_DATADEF     -> "CMD_DATADEF"
    | Grammar.CMD_DEF         -> "CMD_DEF"
    | Grammar.CMD_LOAD -> "CMD_LOAD"

let evaluate state expr =
  res {
    let (State globEnv) = state
    let! typ = typecheck emptyEnv globEnv expr
    let! result = eval globEnv expr
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
  |> Result.bind (handleCmd s)
  |> Result.fold (loop le)
                 (fun err -> printfn "%s" err ; loop le s)

and handleCmd (s : state) (cmd : command) : state result =
  match cmd with
    | Eval e -> evaluate s e ; Success s
    | Postulate (x, ty) -> Success (postulate x ty s)
    | ShowState -> showState s ; Success s
    | Load x -> printfn "loading %A..." x ;
                loadFile s x
    | DataDef (x,y,z) -> printfn "%A -- %A -- %A" x y z; Success s
    | Def (x, t) -> doDefine s x t
    | Quit -> System.Environment.Exit(0) ; Failure "exiting failed"

and handleCmds (s : state) (cmds : command list) : state result =
  match cmds with
    | [] -> Success s
    | c :: cs -> res {
        let! newState = handleCmd s c
        let! rest = handleCmds newState cs
        return rest
      }

and showState = function
  | State (Global.Env ss) ->
      for (x, defn, ty) in ss do
        printfn "%s  =  %s  :  %s" x (pprintTerm defn) (pprintTerm ty)

and loadFile (s : state) (filename : string) : state result =
  let contents = System.IO.File.ReadAllText(filename)
  let lexbuf = lex contents
  try
    lexbuf |> Grammar.file Lexical.token |> handleCmds s
  with
    | exn -> let pos = lexbuf.EndPos
             sprintf "%s near line %d, column %d\n"
                 (exn.Message) (pos.Line+1) pos.Column;
             |> Failure

and doDefine (s : state) (x : string) (t : term) : state result =
  match stateContains s x with
    | None ->
      res {
        let (State globEnv) = s
        let! typ = typecheck emptyEnv globEnv t
        let! result = eval globEnv t
        return define x result typ s
      }
    | Some (x, tm, tp) ->
      Failure
      <| sprintf "%s already defined as %s  :  %s" x (pprintTerm tm) (pprintTerm tp)


let startState : state =
  let emptyState = State Global.empty
  loadFile emptyState "prelude"
  |> Result.fold (id)
       (fun err -> printfn "Could not load prelude.\nThere is no stdlib.\n Error: %s" err ;
                   emptyState)

let main () : unit =
  let le = new LineEditor("deptypes")

  printfn "Silly dependent type checker version 0.0.0.\n:q to quit."
  loop le startState

main ()

