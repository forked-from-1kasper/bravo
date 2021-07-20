type name =
  | Irrefutable
  | Name of string * int

let showName : name -> string = function
  | Irrefutable -> "_"
  | Name (p, n) -> if !Prefs.indices then p ^ "#" ^ string_of_int n else p

module Name = struct
  type t = name
  let compare x y =
    match (x, y) with
    | Irrefutable, Irrefutable -> 0
    | Irrefutable, Name _ -> -1
    | Name _, Irrefutable -> 1
    | Name (p, a), Name (q, b) ->
      if p = q then compare a b
      else compare p q
end

module Env = Map.Make(Name)
module Files = Set.Make(String)

let inc : int ref = ref 0
let gen () = inc := !inc + 1; !inc

let fresh : name -> name = function
  | Irrefutable -> Irrefutable | Name (p, _) -> Name (p, gen ())

let getDigit x = Char.chr (x + 0x80) |> Printf.sprintf "\xE2\x82%c"

let rec showSubscript x =
  if x < 0 then failwith "showSubscript: expected positive integer"
  else if x = 0 then "" else showSubscript (x / 10) ^ getDigit (x mod 10)

let freshName x = let n = gen () in Name (x ^ showSubscript n, n)