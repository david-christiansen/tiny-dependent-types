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

let rec max (n : nat) (m : nat) =
  if n @<= m then m else n
