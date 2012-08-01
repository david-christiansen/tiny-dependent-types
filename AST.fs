
module AST

open Nat


type term =
  | Bound of nat
  | Free of string
  | Pi of string * term * term
  | Lambda of string * term * term
  | App of term * term
  | Univ of nat
  | Prim of string * term

type case = Case of (string * term)

type command =
  | Eval of term
  | Postulate of (string * term)
  | ShowState
  | DataDef of (string * term * case list)
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

let rec pprintTerm t = pprintTerm' t []
and pprintTerm' t ctx =
  match t with
    | Bound n -> "%" + ctx.Item(intOfNat n) + "%" + pprintNat n
    | Free str -> "`" + str + "`"
    | Pi (x, t1, t2) -> "Π" + x + ":" + pprintTerm' t1 ctx +
                        "." + pprintTerm' t2 (x::ctx)
    | Lambda (x, t1, t2) -> "λ" + x + ":" + pprintTerm' t1 ctx +
                            "." + pprintTerm' t2 (x::ctx)
    | App (t1, t2) -> "(" + pprintTerm' t1 ctx + ") " +
                      "(" + pprintTerm' t2 ctx + ")"
    | Univ Z -> "Set"
    | Univ n -> "Set" + subscriptStringOf (sprintf "%i" (intOfNat n))
    | Prim (str, tp) -> "%" + str + ":(" + pprintTerm tp + ")%"
