module Utils

let curry (f : ('a * 'b) -> 'c) = fun a -> fun b -> f (a, b)

let uncurry (f : 'a -> 'b -> 'c) = fun (a, b) -> f a b

let flip (f : 'a -> 'b -> 'c) : 'b -> 'a -> 'c = fun b a -> f a b

let rec snoc xs x =
  match xs with
    | [] -> [x]
    | y :: ys -> y :: (snoc ys x)

let gensymCounter = ref -1
let gensym () =
  gensymCounter := !gensymCounter + 1
  sprintf "%%gen%i" !gensymCounter

let join (sep : string) (strs : string list) : string =
  match strs with
    | [] -> ""
    | xs -> List.reduce (fun x y -> x + sep + y) xs

module List =
  let rec zip' (xs : 'a list) (ys : 'b list) : ('a * 'b) list =
    match xs, ys with
      | [], _ -> []
      | _, [] -> []
      | x :: xs', y :: ys' -> (x, y) :: zip' xs' ys'

  let rec drop (n : int) (xs : 'a list) : 'a list =
    if n < 0
    then raise (System.ArgumentOutOfRangeException (sprintf "drop requires n >= 0, got %A" n))
    else match xs with
           | [] -> []
           | y :: ys when n = 0 -> y :: ys
           | y :: ys -> drop (n - 1) ys

