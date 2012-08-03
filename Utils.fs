module Utils

let curry (f : ('a * 'b) -> 'c) = fun a -> fun b -> f (a, b)

let uncurry (f : 'a -> 'b -> 'c) = fun (a, b) -> f a b

let rec snoc xs x =
  match xs with
    | [] -> [x]
    | y :: ys -> y :: (snoc ys x)

let gensymCounter = ref -1
let gensym () =
  gensymCounter := !gensymCounter + 1
  sprintf "%%gen%i" !gensymCounter

let join (sep : string) (strs : string list) : string =
  List.reduce (fun x y -> x + sep + y) strs

module List =
  let rec zip' (xs : 'a list) (ys : 'b list) : ('a * 'b) list =
    match xs, ys with
      | [], _ -> []
      | _, [] -> []
      | x :: xs', y :: ys' -> (x, y) :: zip' xs' ys'
