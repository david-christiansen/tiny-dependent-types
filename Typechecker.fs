module Typechecker

open Nat
open AST
open Result


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

let rec eval = function
  | Bound n -> Failure "Too high of index on bound var. Parser error?"
  | Free x -> Success (Free x)
  | Pi (x, ty, body) -> Success <| Pi (x, ty, body)
  | Lambda (x, ty, body) -> Success <| Lambda (x, ty, body)
  | App (t1, t2) -> res {
      let! fn = eval t1
      let! arg = eval t2
      let! result = apply fn arg
      return result
    }
  | Univ n -> Success <| Univ n
  | Prim (str, tp) -> Success <| Prim (str, tp)

and apply (t1 : term) (t2 : term) : term result =
  match t1 with
    | Lambda (x, ty, body) -> res {
        let! body' = subst Z t2 body
        let! result = eval body'
        return result
      }
    | Pi (x, ty, body) -> res {
        let! body' = subst Z t2 body
        let! result = eval body'
        return result
      }
    | _ -> Failure "Can only apply lambda or pi"

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
    | App (t1, t2) -> res {
        let! t1' = subst n t t1
        let! t2' = subst n t t2
        return App (t1', t2')
      }
    | Univ n -> Success <| Univ n
    | Prim (str, tp) -> Success <| Prim (str, tp)


let equiv t1 t2 : unit result =
  if eval t1 = eval t2
  then Success ()
  else Failure <| sprintf "%s ≢ %s" (pprintTerm t1) (pprintTerm t2)


let rec shiftUp cutoff = function
  | Bound n when cutoff @<= n -> Bound (S n)
  | Bound n -> Bound n
  | Free x -> Free x
  | Pi (x, tp, tm) -> Pi (x, shiftUp cutoff tp, shiftUp (S cutoff) tm)
  | Lambda (x, tp, tm) -> Lambda (x, shiftUp cutoff tp, shiftUp (S cutoff) tm)
  | App (t1, t2) -> App (shiftUp cutoff t1, shiftUp cutoff t2)
  | Univ n -> Univ n
  | Prim (str, tp) -> Prim (str, tp)

(*
let rec shiftDown = function
  | Bound (S n) -> Bound n
  | Bound Z -> failwithf "Cannot downshift Bound Z"
  | Free x -> Free x
  | Pi (x, tp, tm) -> Pi (x, shiftDown tp, shiftDown tm)
  | Lambda (x, tp, tm) -> Lambda (x, shiftDown tp, shiftDown tm)
  | App (t1, t2) -> App (shiftDown t1, shiftDown t2)
  | Univ n -> Univ n
  | Prim (str, tp) -> Prim (str, tp)
*)

let rec typecheck gamma (globals : Global.env) = function
  | Bound n -> getEnv n gamma
  | Free x -> Global.lookupType x globals
  | Pi _ -> Success <| Univ Z (* TODO: predicativity *)
  | Lambda (x, tp, tm) -> res {
      let gamma' = addEnv (shiftUp Z tp) gamma
      let! bodyType = typecheck gamma' globals tm
      return Pi (x, tp, bodyType)
    }
  | App (t1, t2) -> res {
      let! tp1 = typecheck gamma globals t1
      let! tp2 = typecheck gamma globals t2
      let! matches =
        match tp1 with
          | Pi (_, tp1arg, tp1body) -> equiv tp1arg tp2
          | _ -> Failure
                 <| sprintf "Can only apply Π-types. Attempted to apply %s to %s."
                    (pprintTerm tp1) (pprintTerm tp2)
      let! t' = apply tp1 t2
      return t'
    }
  | Univ n -> Success <| Univ n
  | Prim (_, t) -> Success t
