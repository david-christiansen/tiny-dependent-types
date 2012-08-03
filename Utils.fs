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
