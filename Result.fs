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

module Result

type 'a result =
  | Success of 'a
  | Failure of string

module Result =
  let fold (onSuccess: 'a -> 'b) (onFail: string -> 'b) (res : 'a result) : 'b =
    match res with
      | Success a   -> onSuccess a
      | Failure msg -> onFail msg

  (* fmap *)
  let map (f : 'a -> 'b) (res : 'a result) : 'b result =
    match res with
      | Success a   -> Success <| f a
      | Failure msg -> Failure msg

  (* <*> *)
  let apply (f : ('a -> 'b) result) (x : 'a result) : 'b result =
    match f with
      | Success f' -> map f' x
      | Failure msg -> Failure msg

  let lift2 (f : 'a -> 'b -> 'c) (a : 'a result) (b : 'b result) : 'c result =
    apply (map f a) b

  let bind (f : 'a -> 'b result) (res : 'a result) : 'b result =
    match res with
      | Success a -> f a
      | Failure msg -> Failure msg

  let fromOption (err : string) = function
    | None -> Failure err
    | Some a -> Success a

  let filter (p : 'a -> bool) (err : 'a -> string) = function
      | Success a when p a -> Success a
      | Success a -> Failure <| err a
      | Failure msg -> Failure msg

  let guard (cond : 'a result) : unit result = map (fun _ -> ()) cond

  let failIf (cond : bool) (err : string) : unit result =
    if cond then Failure err else Success ()

  let foreach (op : 'a -> unit) = function
    | Success a -> op a ; ()
    | Failure _ -> ()

  let rec sequence (rs : 'a result list) : 'a list result =
    match rs with
      | [] -> Success []
      | Failure msg :: _ -> Failure msg
      | Success x :: rxs ->
        match sequence rxs with
          | Failure msg -> Failure msg
          | Success xs -> Success (x :: xs)

  (* Don't build up the intermediate list *)
  let rec sequence_ (rs: 'a result list) : unit result =
    match rs with
      | [] -> Success ()
      | Failure msg :: _ -> Failure msg
      | Success x :: rxs ->
        match sequence_ rxs with
          | Failure msg -> Failure msg
          | Success _ -> Success ()

  (* mapM *)
  let mapList (f : 'a -> 'b result) (rs : 'a list) : 'b list result =
    sequence (List.map f rs)

  let rec foldList (f : 'a -> 'b -> 'b result) (start : 'b result) (xs : 'a list) : 'b result =
    match xs with
      | [] -> start
      | y :: ys -> foldList f (bind (f y) start) ys

type ResultBuilder () =
  member x.Bind(v, f) = Result.bind f v
  member x.Return(v) = Success v
  member x.ReturnFrom(r) = r


let res = new ResultBuilder ()
