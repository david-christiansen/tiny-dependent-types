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

(* Compute induction hypotheses *)
let methType d c goal =
  (* The premises for the motive application *)
  let cPremises dataargs =
    List.foldBack (fun res ar -> App (ar, res))
                  (List.rev dataargs)
                  goal

  (* Generate induction hypotheses *)
  let rec hyps goal = function
    | [] -> App (cPremises (snd c.result),
                 (Constructor (c, boundArgs (natOfInt c.signature.Length))))
    | (r, Datatype (d', dargs)) :: cargs when d = d' ->
        Pi (r+"IH",
            shiftUp Z (App (cPremises dargs, Free r)),
            shiftUp Z (hyps goal cargs))
    | _ :: cargs -> hyps goal cargs
  (* TODO: replace following with a fold *)
  let rec argsToPi = function
    | [] -> hyps goal c.signature
    | (name, ty) :: args -> Pi (name, ty, argsToPi args)
  argsToPi c.signature |> Grammar.fixVars

let subjectType d =
  let rec computeSubject = function
    | [] -> Pi ("x",
                Datatype (d, boundArgs (natOfInt d.signature.Length)),
                App (List.foldBack (fun res ar -> App (ar, res))
                                   (List.rev (boundArgs (natOfInt d.signature.Length)))
                                   (Free "P")
                     |> shiftUp Z,
                     Free "x"))
    | (x, t) :: moreSig -> Pi (x, t, computeSubject moreSig)
  computeSubject d.signature

let elimType d cs =
  let methTypes = List.map (fun c -> "m" + c.name, methType d c (Free "P")) cs
  let rec mtToPi = function
    | [] -> subjectType d //(App (Free "P", Free "x"))
    | (m, mt) :: methods -> Pi (m, mt, mtToPi methods)
  motive d (mtToPi methTypes) |> Grammar.fixVars

let numIndArgs (d : datatype) (cs : construct list) =
  d.signature.Length + // Targets
  1 + // Motive
  cs.Length + // Methods
  1 // Subject
