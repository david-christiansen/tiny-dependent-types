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

module Typechecker

open Nat
open AST
open Result
open Utils


module Global =
  type env = Env of (string * term * term) list

  let empty = Env []

  let rec lookup (x : string) = function Env env -> lookup' x env
  and lookup' (x : string) = function
    | [] -> Failure <| x + " not found in environment."
    | (y, t1, t2) :: rest when x = y -> Success (t1, t2)
    | _ :: rest -> lookup' x rest

  let lookupTerm (x : string) (e : env) = Result.map fst (lookup x e)

  let lookupType (x : string) (e : env) = Result.map snd (lookup x e)


type env = Env of term list

let rec getEnv n s =
  match n, s with
    | _, Env []        -> Failure "Ran out of variables. Parser bug?"
    | Z, Env (t::ts)   -> Success t
    | S n, Env (t::ts) -> getEnv n (Env ts)

let addEnv t = function
  | Env ts -> Env (t :: ts)

let envWith t = Env (t :: [])

let emptyEnv = Env []

let rec eval (globals : Global.env) = function
  | Bound n -> Failure "Too high of index on bound var. Parser error?"
  | Free x -> Global.lookupTerm x globals
  | Pi (x, ty, body) -> Success <| Pi (x, ty, body)
  | Lambda (x, ty, body) -> Success <| Lambda (x, ty, body)
  | Sigma (x, ty, p) -> Success <| Sigma (x, ty, p)
  | Pair (x, w, prf) -> res {
      let! w' = eval globals w
      return Pair (x, w', prf)
    }
  | Fst (Pair (x, w, prf)) -> Success w
  | Fst x -> Failure <| sprintf "Can't take first projection of %s" (pprintTerm x)
  | Snd (Pair (x, w, prf)) -> Result.bind (eval globals) (subst Z w prf)
  | Snd x -> Failure <| sprintf "Can't take second projection of %s" (pprintTerm x)
  | App (t1, t2) -> res {
      let! fn = eval globals t1
      let! arg = eval globals t2
      let! result = apply globals fn arg
      return result
    }
  | Univ n -> Success <| Univ n
  | Postulated (str, tp) -> Success <| Postulated (str, tp)
  | Datatype d -> Success <| Datatype d
  | Constructor c -> Success <| Constructor c
  | ConstrApp (c, args) -> res {
      let! args' = Result.mapList (eval globals) args
      return ConstrApp (c, args')
    }

and apply (globals : Global.env) (t1 : term) (t2 : term) : term result =
  match t1 with
    | Lambda (x, ty, body) -> res {
        let! body' = subst Z t2 body
        let! result = eval globals body'
        return result
      }
    | Pi (x, ty, body) -> res {
        let! body' = subst Z t2 body
        let! result = eval globals body'
        return result
      }
    | Constructor c -> res {
        let! arg = eval globals t2
        return ConstrApp (c, [arg])
      }
    | ConstrApp (c, args) -> res {
        let! x =
          Result.failIf (c.signature.Length <= args.Length)
            (sprintf "Too many arguments to %s." c.name)
        let! newArg = eval globals t2
        let args' = snoc args newArg
        return ConstrApp (c, args')
      }
    | _ -> Failure "Can only apply lambda or pi"

(* Substitute t for the bound var with index n in subject *)
and subst (n : nat) (t : term) (subject : term) : term result =
  match subject with
    | Bound n' when n = n' -> Success t
    | Bound m -> Success <| Bound m
    | Free x -> Success <| Free x
    | Pi (x, ty, body) -> res {
          let! ty' = subst n t ty
          let! body' = subst (S n) t body
          return Pi (x, ty', body')
        }
    | Lambda (x, ty, body) -> res {
        let! ty' = subst n t ty
        let! body' = subst (S n) t body
        return Lambda (x, ty', body')
      }
    | Sigma (x, ty, p) -> res {
        let! ty' = subst n t ty
        let! p' = subst (S n) t p
        return Sigma (x, ty', p')
      }
    | Pair (x, w, prf) -> res {
        let! w' = subst n t w
        let! prf' = subst (S n) t prf
        return Pair (x, w', prf')
      }
    | Fst p -> Result.map Fst (subst n t p)
    | Snd p -> Result.map Snd (subst n t p)
    | App (t1, t2) -> res {
        let! t1' = subst n t t1
        let! t2' = subst n t t2
        return App (t1', t2')
      }
    | Univ n -> Success <| Univ n
    | Postulated (str, tp) -> Success <| Postulated (str, tp)
    | Datatype d -> Success <| Datatype d
    | Constructor info ->
        res {
          let! newSig = substSignature n t info.signature
          return Constructor {info with signature = newSig}
        }
    | ConstrApp (c, args) ->
        res {
          let! args' = Result.mapList (subst n t) args
          let! newSig = substSignature n t c.signature
          return ConstrApp ({c with signature = newSig}, args')
        }
and substSignature (n : nat) (t : term) = function
  | [] -> Success []
  | (x, ty) :: rest -> res {
      let! ty' = subst n t ty
      let! ss' = substSignature (S n) t rest
      return (x, ty') :: ss'
    }


let equiv (globals : Global.env) t1 t2 : unit result =
  if eval globals t1 = eval globals t2
  then Success ()
  else Failure <| sprintf "%s ≢ %s" (pprintTerm t1) (pprintTerm t2)


let rec shiftUp (cutoff : nat) (subject : term) : term =
  let shiftBinding =
    function (id, arg, body) -> (id, shiftUp cutoff arg, shiftUp (S cutoff) body)
  let rec shiftSignature (cutoff : nat) = function
    | [] -> []
    | (x, t) :: rest -> (x, shiftUp cutoff t) :: shiftSignature (S cutoff) rest
  match subject with
    | Bound n when cutoff @<= n -> Bound (S n)
    | Bound n -> Bound n
    | Free x -> Free x
    | Pi (x, tp, tm) -> Pi (shiftBinding (x, tp, tm))
    | Lambda (x, tp, tm) -> Lambda (shiftBinding (x, tp, tm))
    | Sigma (x, ty, p) -> Sigma (shiftBinding (x, ty, p))
    | Pair (x, w, prf) -> Pair (shiftBinding (x, w, prf))
    | Fst p -> Fst (shiftUp cutoff p)
    | Snd p -> Snd (shiftUp cutoff p)
    | App (t1, t2) -> App (shiftUp cutoff t1, shiftUp cutoff t2)
    | Univ n -> Univ n
    | Postulated (str, tp) -> Postulated (str, tp)
    | Datatype d -> Datatype d
    | Constructor info ->
        Constructor {
          info with
            signature = shiftSignature cutoff info.signature
        }
    | ConstrApp (c, args) ->
        let c' = {c with signature = shiftSignature cutoff c.signature}
        ConstrApp (c', List.map (shiftUp cutoff) args)



let rec typecheck gamma (globals : Global.env) = function
  | Bound n -> getEnv n gamma
  | Free x -> Global.lookupType x globals
  | Pi (x, tp, tm) -> res {
      let gamma' = addEnv (shiftUp Z tp) gamma
      let! bodyType = typecheck gamma' globals tm
      return Univ Z (* TODO: predicativity *)
    }
  | Lambda (x, tp, tm) -> res {
      let gamma' = addEnv (shiftUp Z tp) gamma
      let! bodyType = typecheck gamma' globals tm
      return Pi (x, tp, bodyType)
    }
  | Sigma (x, ty, p) -> res {
      let gamma' = addEnv (shiftUp Z ty) gamma
      let! bodyType = typecheck gamma' globals p
      return Univ Z (* TODO: predicativity *)
    }
  | Pair (x, w, prf) -> res {
      let! witnessT = typecheck gamma globals w
      let gamma' = addEnv (shiftUp Z witnessT) gamma
      let! p = typecheck gamma' globals prf
      return Sigma (x, witnessT, p)
    }
  | Fst p -> res {
      let! pairT = typecheck gamma globals p
      let! result =
        match pairT with
          | Sigma (x, ty, p) -> Success ty
          | t -> Failure <| sprintf "Cannot take first projection of non-Σ-type %s"
                              (pprintTerm t)
      return result
    }
  | Snd p -> res {
      let! pairT = typecheck gamma globals p
      let! second' =
        match pairT with
          | Sigma (x, ty, p) -> Success p
          | t -> Failure <| sprintf "Cannot take second projection of non-Σ-type %s"
                              (pprintTerm t)
      let! first = eval globals (Fst p)
      let! second = subst Z first second'
      return second
    }
  | App (t1, t2) -> res {
      let! tp1 = typecheck gamma globals t1
      let! tp2 = typecheck gamma globals t2
      let! matches =
        match tp1 with
          | Pi (_, tp1arg, tp1body) -> equiv globals tp1arg tp2
          | _ -> Failure
                 <| sprintf "Can only apply Π-types. Attempted to apply %s to %s."
                    (pprintTerm tp1) (pprintTerm tp2)
      let! t' = apply globals tp1 t2
      return t'
    }
  | Univ n -> Success <| Univ (S n)
  | Postulated (_, t) -> Success t
  | Datatype d -> Success <| Univ Z (* TODO: predicativity *)
  | Constructor info ->
      let rec constrType = function
        | [] -> Datatype info.result
        | (Some x, xt) :: ss -> Pi (x, xt, constrType ss)
        | (None, ty) :: ss -> Pi ("_", ty, constrType ss)
      Success <| constrType info.signature
  | ConstrApp (c, args) ->
    try
      res {
        let! argTypes = List.map (typecheck gamma globals) args |> Result.sequence
        let argSig = List.zip argTypes (List.map snd c.signature)
        let! matches = List.map (uncurry (equiv globals)) argSig |> Result.sequence_
        return Datatype c.result
      }
    with
      | :? System.ArgumentException ->
        sprintf "Wrong number of arguments to %s" c.name
        |> Failure
