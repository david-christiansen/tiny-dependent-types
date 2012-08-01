module Nat

type nat = Z | S of nat

let rec natOfInt n =
  if n < 0
  then failwithf "The negative in %i cannot be converted to a natural number." n
  else if n = 0 then Z else S (natOfInt (n - 1))

let rec intOfNat n =
  match n with
    | Z -> 0
    | S n' -> intOfNat n' + 1

let rec pprintNat n = intOfNat n |> sprintf "%i"

let rec (@<=) (n : nat) (m : nat) =
  match n, m with
    | Z, _ -> true
    | S n', Z -> false
    | S n', S m' -> n' @<= m'

let rec (@+) (n : nat) (m : nat) =
  match n with
    | Z -> m
    | S n' -> S (n' @+ m)
