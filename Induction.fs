module Induction

open Utils
open Nat
open AST

let rec boundArgs (n : nat) =
  match n with
    | Z -> []
    | S n' -> Bound n' :: boundArgs n'

let targets d contents =
  let rec argsToPi = function
    | [] -> Pi ("x",
                Datatype (d, boundArgs (natOfInt d.signature.Length)),
                contents)
    | (name, ty) :: args -> Pi (name, ty, argsToPi args)
  argsToPi d.signature

let motive d contents =
  let motiveT = targets d (Univ Z) (* TODO: Predicativity *)
  Pi ("P", motiveT, contents)

let noMethods d =
  targets d (motive d (App (Free "P", Free "x")))
  |> Grammar.fixVars

let methType d c goal =
  (* Compute induction hypotheses *)
  let rec hyps goal = function
    | [] -> App (goal, Constructor (c, boundArgs (natOfInt c.signature.Length)))
    | (r, Datatype (d', dargs)) :: cargs when d = d' ->
        Pi (r+"'", App (goal, Free r), hyps goal cargs)
    | _ :: cargs -> hyps goal cargs
  let rec argsToPi = function
    | [] -> hyps goal c.signature
    | (name, ty) :: args -> Pi (name, ty, argsToPi args)
  argsToPi c.signature |> Grammar.fixVars

let elimType d cs =
  let methTypes = List.map (fun c -> "m" + c.name, methType d c (Free "P")) cs
  let rec mtToPi = function
    | [] -> (App (Free "P", Free "x"))
    | (m, mt) :: methods -> Pi (m, mt, mtToPi methods)
  targets d (motive d (mtToPi methTypes))
  |> Grammar.fixVars
