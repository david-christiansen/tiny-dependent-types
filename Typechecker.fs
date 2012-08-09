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
open Induction

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

let rec normalize (globals : Global.env) = function
  | Bound n -> Success <| Bound n
  | Free x -> Global.lookupTerm x globals
  | Pi (x, ty, body) -> res {
      let! ty' = normalize globals ty
      let! body' = normalize globals body
      return Pi (x, ty', body')
    }
  | Lambda (x, ty, body) -> res {
      let! ty' = normalize globals ty
      let! body' = normalize globals body
      return Lambda (x, ty', body')
    }
  | Sigma (x, ty, p) -> res {
      let! ty' = normalize globals ty
      let! p' = normalize globals p
      return Sigma (x, ty', p')
    }
  | Pair (x, w, prf) -> res {
      let! w' = normalize globals w
      let! prf' = normalize globals prf
      return Pair (x, w', prf')
    }
  | Fst x -> res {
      let! x' = normalize globals x
      let! first =
        match x' with
          | (Pair (x, w, prf)) -> Success w
          | _ -> Failure <| sprintf "Can't take first projection of %s" (pprintTerm x')
      return first
    }
  | Snd x -> res {
      let! x' = normalize globals x
      let! second =
        match x' with
          | (Pair (x, w, prf)) -> subst Z w prf
          | _ -> Failure <| sprintf "Can't take second projection of %s" (pprintTerm x')
      let! second' = normalize globals second
      return second'
    }
  | App (t1, t2) -> res {
      let! fn = normalize globals t1
      let! arg = normalize globals t2
      let! result = apply globals fn arg
      return result
    }
  | Univ n -> Success <| Univ n
  | Postulated (str, tp) -> Success <| Postulated (str, tp)
  | Datatype (d, args) -> res {
      let! args' = Result.mapList (normalize globals) args
      return Datatype (d, args')
    }
  | Constructor (c, args) -> res {
      let! args' = Result.mapList (normalize globals) args
      return Constructor (c, args')
    }
  | Ind (d, cs, args) -> res {
      let! args' = Result.mapList (normalize globals) args
      return Ind (d, cs, args')
    }

and apply (globals : Global.env) (t1 : term) (t2 : term) : term result =
  match t1 with
    | Lambda (x, ty, body) -> res {
        let! body' = subst Z t2 body
        let! result = normalize globals body'
        return result
      }
    | Pi (x, ty, body) -> res {
        let! body' = subst Z t2 body
        let! result = normalize globals body'
        return result
      }
    | Datatype (d, args) -> res {
        do! Result.failIf (d.signature.Length <= args.Length)
              (sprintf "Too many arguments to %s. Typechecker bug?" d.name)
        let! newArg = normalize globals t2
        let args' = snoc args newArg
        return Datatype (d, args')
      }
    | Constructor (c, args) -> res {
        do! Result.failIf (c.signature.Length <= args.Length)
              (sprintf "Too many arguments to %s. Typechecker bug?" c.name)
        let! newArg = normalize globals t2
        let args' = snoc args newArg
        return Constructor (c, args')
      }
    | Ind (d, cs, args) -> res {
        do! Result.failIf (args.Length >= numIndArgs d cs) ("Too many args to eliminator.")
        let! newArg = normalize globals t2
        let args' = snoc args newArg
        if args'.Length = numIndArgs d cs
          then return! doInduction globals d cs args'
          else return Ind (d, cs, args')
      }
    | _ -> Success <| App (t1, t2)

and doInduction (globals : Global.env) (d : datatype) (cs : construct list) (args : term list) : term result =
  if args.Length <> numIndArgs d cs
  then Failure "Type check error - wrong nr. args to eliminator"
  else res {
    let (Constructor (c, cArgs) :: more) = args // subject
    let more' = List.drop (d.signature.Length) more // targets
    let (motive :: methods) = more' // motive

    (* select method *)
    let meth = methods.Item(List.findIndex (fun c' -> c = c') cs)

    (* recurse on constr args - that is, provide induction hypotheses *)
    let! indHyps = Result.sequence <| List.choose (function
        | Constructor (c', a') ->
            Some <| doInduction globals d cs (Constructor (c', a') :: more)
        | _ -> None) cArgs

    (* finally apply method *)
    return! Result.foldList (flip (apply globals)) (Success meth) (cArgs @ indHyps)
  }

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
    | Datatype (d, args) -> res {
        let! args' = Result.mapList (subst n t) args
        let! newSig = substSignature n t d.signature
        return Datatype ({d with signature = newSig}, args')
      }
    | Constructor (c, args) -> res {
        let! args' = Result.mapList (subst n t) args
        let! newSig = substSignature n t c.signature
        return Constructor ({c with signature = newSig}, args')
      }
    | Ind (d, cs, args) -> res {
        let! args' = Result.mapList (subst n t) args
        let! newDSig = substSignature n t d.signature
        let! newCs =
          Result.mapList
            (fun (c : construct) ->
               Result.map (fun sig' -> {c with signature = sig'})
                  <| substSignature n t c.signature)
            cs
        return Ind ({d with signature = newDSig}, newCs, args')
      }
and substSignature (n : nat) (t : term) = function
  | [] -> Success []
  | (x, ty) :: rest -> res {
      let! ty' = subst n t ty
      let! ss' = substSignature (S n) t rest
      return (x, ty') :: ss'
    }

let rec alphaEqual t1 t2 =
  match t1, t2 with
    | Bound n, Bound m -> n = m
    | Free x, Free y -> x = y
    | Pi (_, t1, t2), Pi (_, t1', t2') -> alphaEqual t1 t1' && alphaEqual t2 t2'
    | Lambda (_, t1, t2), Lambda (_, t1', t2') -> alphaEqual t1 t1' && alphaEqual t2 t2'
    | Sigma (_, t1, t2), Sigma (_, t1', t2') -> alphaEqual t1 t1' && alphaEqual t2 t2'
    | Pair (_, t1, t2), Pair (_, t1', t2') -> alphaEqual t1 t1' && alphaEqual t2 t2'
    | Fst t, Fst t' -> alphaEqual t t'
    | Snd t, Snd t' -> alphaEqual t t'
    | App (t1, t2), App (t1', t2') -> alphaEqual t1 t1' && alphaEqual t2 t2'
    | Univ n, Univ m -> n = m
    | Postulated (str, tp), Postulated (str', tp') -> str = str' && alphaEqual tp tp'
    | Datatype (d, args), Datatype (d', args') ->
        d = d' && args.Length = args'.Length &&
        List.zip args args' |> List.map (uncurry alphaEqual) |> List.fold (&&) true
    | Constructor (c, args), Constructor (c', args') ->
        c = c' && args.Length = args'.Length &&
        List.zip args args' |> List.map (uncurry alphaEqual) |> List.fold (&&) true
    | Ind (d, cs, args), Ind (d', cs', args') ->
        d = d' && cs = cs' &&
        List.zip args args' |> List.map (uncurry alphaEqual) |> List.fold (&&) true
    | _ -> false

let (=|=) t1 t2 = alphaEqual t1 t2

let equiv (globals : Global.env) t1 t2 : unit result =
  res {
    let! matches = Result.lift2 alphaEqual (normalize globals t1) (normalize globals t2)
    return! Result.failIf (not matches)
            <| sprintf "%s ≢ %s" (pprintTerm t1) (pprintTerm t2)
  }


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
    | Datatype (d, args) ->
        let d' = {d with signature = shiftSignature cutoff d.signature}
        Datatype (d', List.map (shiftUp cutoff) args)
    | Constructor (c, args) ->
        let c' = {c with signature = shiftSignature cutoff c.signature}
        Constructor (c', List.map (shiftUp cutoff) args)
    | Ind (d, cs, args) ->
        let d' = {d with signature = shiftSignature cutoff d.signature}
        let cs' =
          List.map (fun (c : construct) ->
                    {c with signature = shiftSignature cutoff c.signature})
                   cs
        Ind (d', cs', List.map (shiftUp cutoff) args)



let rec typecheck gamma (globals : Global.env) = function
  | Bound n -> getEnv n gamma
  | Free x -> Global.lookupType x globals
  | Pi (x, tp, tm) -> res {
      let gamma' = addEnv (shiftUp Z tp) gamma
      do! Result.guard (typecheck gamma' globals tm)
      return Univ Z (* TODO: predicativity *)
    }
  | Lambda (x, tp, tm) -> res {
      let! tp' = normalize globals tp
      let gamma' = addEnv (shiftUp Z tp) gamma
      let! bodyType = typecheck gamma' globals tm
      let! bodyType' = normalize globals bodyType
      return Pi (x, tp', bodyType')
    }
  | Sigma (x, ty, p) -> res {
      let gamma' = addEnv (shiftUp Z ty) gamma
      do! Result.guard(typecheck gamma' globals p)
      return Univ Z (* TODO: predicativity *)
    }
  | Pair (x, w, prf) -> res {
      let! witnessT = typecheck gamma globals w
      let! witnessT' = normalize globals witnessT
      let gamma' = addEnv (shiftUp Z witnessT) gamma
      let! p = typecheck gamma' globals prf
      let! p' = normalize globals p
      return Sigma (x, witnessT', p')
    }
  | Fst p -> res {
      let! pairT = typecheck gamma globals p
      let! result =
        match pairT with
          | Sigma (x, ty, p) -> Success ty
          | t -> Failure <| sprintf "Cannot take first projection of non-Σ-type %s"
                              (pprintTerm t)
      let! result' = normalize globals result
      return result'
    }
  | Snd p -> res {
      let! pairT = typecheck gamma globals p
      let! secondT =
        match pairT with
          | Sigma (x, ty, p) -> Success p
          | t -> Failure <| sprintf "Cannot take second projection of non-Σ-type %s"
                              (pprintTerm t)
      let! first = normalize globals (Fst p)
      let! secondT' = subst Z first secondT
      let! secondT'' = normalize globals secondT'
      return secondT''
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
  | Postulated (_, t) -> normalize globals t
  | Datatype (d, args) ->
      cType d.name gamma globals args d.signature (Univ Z) (* TODO: predicativity *)
  | Constructor (c, args) ->
      cType c.name gamma globals args c.signature (Datatype c.result)
  | Ind (d, cs, args) -> applyList gamma globals (elimType d cs) args

and cType name gamma globals arguments signature result =
  let rec makePi result = function
    | [] -> result
    | (x, xt) :: ss -> Pi (x, xt, makePi result ss)
  match arguments, signature with
    | [], ss -> Success <| makePi result ss
    | _, [] -> Failure <| sprintf "Too many arguments for %s." name
    | ar :: ars, (_, s) :: ss -> res {
        let! arT = typecheck gamma globals ar
        do! Result.guard (equiv globals arT s)
        let! newSig = substSignature Z ar ss
        return! cType name gamma globals ars newSig result
      }

and applyList (gamma : env) (globals : Global.env) (opT : term) = function
  | [] -> Success opT
  | arg :: args -> res {
      let! argT = typecheck gamma globals arg
      do! match opT with
            | Pi (_, opArgT, opBodyT) -> equiv globals opArgT argT
            | _ -> Failure
                   <| sprintf "Attempted to apply non-Π type %s to arguments %s"
                      (pprintTerm opT) (join " " (List.map pprintTerm (arg :: args)))
      let! opT' = apply globals opT arg
      return! applyList gamma globals opT' args
    }


