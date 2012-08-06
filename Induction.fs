module Induction

open Utils
open Nat
open AST

let targets d contents =
  let rec boundArgs (n : nat) =
    match n with
      | Z -> []
      | S n' -> Bound n' :: boundArgs n'
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

