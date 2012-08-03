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

module AST

open Nat
open Utils


type term =
  | Bound of nat
  | Free of string
  | Pi of string * term * term
  | Lambda of string * term * term
  | Sigma of string * term * term
  | Pair of string * term * term
  | Fst of term
  | Snd of term
  | App of term * term
  | Univ of nat
  | Postulated of string * term
  | Datatype of datatype * (term list)
  | Constructor of construct * (term list)

and datatype = {
    name : string
    signature : (string option * term) list
  }

and construct = {
    name : string
    signature : (string option * term) list
    result : (datatype * term list)
  }

type case = Case of (string * term)

type command =
  | Eval of term
  | Postulate of (string * term)
  | ShowState
  | DataDef of (string * term * case list)
  | Def of (string * term)
  | Load of string
  | ToggleDebug
  | Quit

let subscriptStringOf (str : string) =
  str.Replace("-", "₋")
     .Replace("0", "₀")
     .Replace("1", "₁")
     .Replace("2", "₂")
     .Replace("3", "₃")
     .Replace("4", "₄")
     .Replace("5", "₅")
     .Replace("6", "₆")
     .Replace("7", "₇")
     .Replace("8", "₈")
     .Replace("9", "₉")

let rec usesBinding n t =
  match t with
    | Bound n' when n = n' -> true
    | Bound _ -> false
    | Free _ -> false
    | Pi (_, t1, t2) -> usesBinding n t1 || usesBinding (S n) t2
    | Lambda (_, t1, t2) -> usesBinding n t1 || usesBinding (S n) t2
    | Sigma (_, t1, t2) -> usesBinding n t1 || usesBinding (S n) t2
    | Pair (_, t1, t2) -> usesBinding n t1 || usesBinding (S n) t2
    | Fst t' -> usesBinding n t'
    | Snd t' -> usesBinding n t'
    | App (t1, t2) -> usesBinding n t1 || usesBinding n t2
    | Univ _ -> false
    | Postulated _ -> false
    | Datatype _ -> false
    | Constructor (_, args) ->
      let rec bindingIn n = function
        | [] -> false
        | ar :: ars -> usesBinding n ar || bindingIn (S n) ars
      bindingIn n args

let rec pprintTerm t = pprintTerm' t []
and pprintTerm' t ctx =
  match t with
    | Bound n -> "%" + ctx.Item(intOfNat n) + "%" + pprintNat n
    | Free str -> "`" + str + "`"
    | Pi (x, t1, t2) when not (usesBinding Z t2) ->
        "(" + pprintTerm' t1 ctx +
        " → " + pprintTerm' t2 (""::ctx) + ")"
    | Pi (x, t1, t2) -> "Π" + x + ":" + pprintTerm' t1 ctx +
                        "." + pprintTerm' t2 (x::ctx)
    | Lambda (x, t1, t2) -> "λ" + x + ":" + pprintTerm' t1 ctx +
                            "." + pprintTerm' t2 (x::ctx)
    | Sigma (_, ty, p) when not (usesBinding Z p) ->
        "(" + pprintTerm' ty ctx +
        " × " + pprintTerm' p (""::ctx) + ")"
    | Sigma (x, ty, p) -> "Σ" + x + ":" + pprintTerm' ty ctx +
                          "." + pprintTerm' p (x::ctx)
    | Pair (_, a, b) when not (usesBinding Z b) ->
        "{" + pprintTerm' a ctx + " ; " + pprintTerm' b (""::ctx) + "}"
    | Pair (x, w, prf) -> "{" + x + "|" +
                          pprintTerm' w ctx + ";" +
                          pprintTerm' prf (x::ctx) + "}"
    | Fst t' -> "fst " + pprintTerm' t' ctx
    | Snd t' -> "snd " + pprintTerm' t' ctx
    | App (t1, t2) -> "(" + pprintTerm' t1 ctx + ") " +
                      "(" + pprintTerm' t2 ctx + ")"
    | Univ Z -> "Set"
    | Univ n -> "Set" + subscriptStringOf (sprintf "%i" (intOfNat n))
    | Postulated (str, tp) -> "%" + str + ":(" + pprintTerm tp + ")%"
    | Datatype ({name = n}, []) -> n
    | Datatype ({name = n}, args) ->
        "(" + n + " " +
        (List.map (fun arg -> pprintTerm' arg ctx) args
         |> join " ") + ")"
    | Constructor (c, []) -> c.name
    | Constructor (c, args) ->
        "(" + c.name + " " +
        (List.map (fun arg -> pprintTerm' arg ctx) args
         |> join " ") +
        ")"
