module Result

type 'a result =
  | Success of 'a
  | Failure of string


module Result =
  let fold (onSuccess: 'a -> 'b) (onFail: string -> 'b) (res : 'a result) : 'b =
    match res with
      | Success a   -> onSuccess a
      | Failure msg -> onFail msg

  let map (f : 'a -> 'b) (res : 'a result) : 'b result =
    match res with
      | Success a   -> Success <| f a
      | Failure msg -> Failure msg

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

  let foreach (op : 'a -> unit) = function
    | Success a -> op a ; ()
    | Failure _ -> ()

type ResultBuilder () =
  member x.Bind(v, f) = Result.bind f v
  member x.Return(v) = Success v
  member x.ReturnFrom(r) = r
  

let res = new ResultBuilder ()
