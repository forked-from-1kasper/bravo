open Ident

type exp =
  | EPre of int | EKan of int
  | EVar of name | EHole
  | EPi of exp * (name * exp) | ELam of exp * (name * exp) | EApp of exp * exp
  | ESig of exp * (name * exp) | EPair  of exp * exp | EFst of exp | ESnd of exp
  | EId of exp | ERefl of exp | EJ of exp
  | EPath of exp * exp * exp | EIdp of exp | ERev of exp | ETrans of exp * exp
  | EBoundary of exp * exp * exp | ELeft of exp * exp | ERight of exp * exp
  | ESymm of exp | EComp of exp * exp | EBLeft of exp * exp | EBRight of exp * exp | EBCong of exp * exp * exp
  | EMeet of exp * exp * exp | ECoe of exp * exp | ECong of exp * exp | EUA of exp

type tele = name * exp

type scope = Local | Global

type value =
  | VKan of int | VPre of int
  | Var of name * value | VHole
  | VPi of value * clos | VLam of value * clos | VApp of value * value
  | VSig of value * clos | VPair of value * value | VFst of value | VSnd of value
  | VId of value | VRefl of value | VJ of value
  | VPath of value * value * value | VIdp of value | VRev of value | VTrans of value * value
  | VBoundary of value * value * value | VLeft of value * value | VRight of value * value
  | VSymm of value | VComp of value * value | VBLeft of value * value | VBRight of value * value | VBCong of value * value * value
  | VMeet of value * value * value | VCoe of value * value | VCong of value * value | VUA of value

and clos = name * (value -> value)

and term = Exp of exp | Value of value

and record = scope * term * term

and ctx = record Env.t

let eLam p a b = ELam (a, (p, b))
let ePi  p a b = EPi  (a, (p, b))
let eSig p a b = ESig (a, (p, b))

let name x = Name (x, 0)
let decl x = EVar (name x)

let upVar p x ctx = match p with Irrefutable -> ctx | _ -> Env.add p x ctx
let upLocal (ctx : ctx) (p : name) t v : ctx = upVar p (Local, Value t, Value v) ctx
let upGlobal (ctx : ctx) (p : name) t v : ctx = upVar p (Global, Value t, Value v) ctx

let isGlobal : record -> bool = function Global, _, _ -> false | Local, _, _ -> true
let freshVar ns n = match Env.find_opt n ns with Some x -> x | None -> n

let rec telescope (ctor : name -> exp -> exp -> exp) (e : exp) : tele list -> exp = function
  | (p, a) :: xs -> ctor p a (telescope ctor e xs)
  | [] -> e

let parens b x = if b then "(" ^ x ^ ")" else x

let rec ppExp paren e = let x = match e with
  | EKan n -> "U" ^ showSubscript n
  | ELam (a, (p, b)) -> Printf.sprintf "λ %s, %s" (showTele p a) (showExp b)
  | EPi (a, (p, b)) -> showPiExp a p b
  | ESig (a, (p, b)) -> Printf.sprintf "Σ %s, %s" (showTele p a) (showExp b)
  | EPair (fst, snd) -> Printf.sprintf "(%s, %s)" (showExp fst) (showExp snd)
  | EFst exp -> ppExp true exp ^ ".1"
  | ESnd exp -> ppExp true exp ^ ".2"
  | EApp (f, x) -> Printf.sprintf "%s %s" (showExp f) (ppExp true x)
  | EVar p -> showName p
  | EHole -> "?"
  | EPre n -> "V" ^ showSubscript n
  | EPath (e, a, b) -> Printf.sprintf "Path %s %s %s" (ppExp true e) (ppExp true a) (ppExp true b)
  | EId e -> Printf.sprintf "Id %s" (ppExp true e)
  | ERefl e -> Printf.sprintf "refl %s" (ppExp true e)
  | EJ e -> Printf.sprintf "idJ %s" (ppExp true e)
  | EIdp e -> "idp " ^ ppExp true e
  | ERev p -> ppExp true p ^ "⁻¹"
  | ETrans (p, q) -> ppExp true p ^ " ⬝ " ^ ppExp true q
  | EBoundary (a, b, x) -> Printf.sprintf "∂ %s %s %s" (ppExp true a) (ppExp true b) (ppExp true x)
  | ELeft (a, b) -> Printf.sprintf "left %s %s" (ppExp true a) (ppExp true b)
  | ERight (a, b) -> Printf.sprintf "right %s %s" (ppExp true a) (ppExp true b)
  | ESymm e -> "∂-symm " ^ ppExp true e
  | EComp (a, b) -> Printf.sprintf "∂-comp %s %s" (ppExp true a) (ppExp true b)
  | EBLeft (a, b) -> Printf.sprintf "∂-left %s %s" (ppExp true a) (ppExp true b)
  | EBRight (a, b) -> Printf.sprintf "∂-right %s %s" (ppExp true a) (ppExp true b)
  | EBCong (f, x, e) -> Printf.sprintf "∂-cong %s %s %s" (ppExp true f) (ppExp true x) (ppExp true e)
  | EMeet (p, x, e) -> Printf.sprintf "meet %s %s %s" (ppExp true p) (ppExp true x) (ppExp true e)
  | ECoe (p, x) -> Printf.sprintf "coe %s %s" (ppExp true p) (ppExp true x)
  | ECong (a, b) -> Printf.sprintf "cong %s %s" (ppExp true a) (ppExp true b)
  | EUA e -> Printf.sprintf "ua %s" (ppExp true e)
  in match e with
  | EVar _ | EFst _ | ESnd _ | EPre _
  | EKan _ | EHole | EPair _ | ERev _ -> x
  | _ -> parens paren x

and showExp e = ppExp false e
and showTele p x = Printf.sprintf "(%s : %s)" (showName p) (showExp x)

and showPiExp a p b = match p with
  | Irrefutable -> Printf.sprintf "%s → %s" (ppExp true a) (showExp b)
  | _           -> Printf.sprintf "Π %s, %s" (showTele p a) (showExp b)

let rec ppValue paren v = let x = match v with
  | VKan n -> "U" ^ showSubscript n
  | VLam (x, (p, clos)) -> Printf.sprintf "λ %s, %s" (showTele p x) (showClos p x clos)
  | VPi (x, (p, clos)) -> showPi x p clos
  | VSig (x, (p, clos)) -> Printf.sprintf "Σ %s, %s" (showTele p x) (showClos p x clos)
  | VPair (fst, snd) -> Printf.sprintf "(%s, %s)" (showValue fst) (showValue snd)
  | VFst v -> ppValue true v ^ ".1"
  | VSnd v -> ppValue true v ^ ".2"
  | VApp (f, x) -> Printf.sprintf "%s %s" (showValue f) (ppValue true x)
  | Var (p, _) -> showName p
  | VHole -> "?"
  | VPre n -> "V" ^ showSubscript n
  | VPath (e, a, b) -> Printf.sprintf "Path %s %s %s" (ppValue true e) (ppValue true a) (ppValue true b)
  | VId v -> Printf.sprintf "Id %s" (ppValue true v)
  | VRefl v -> Printf.sprintf "refl %s" (ppValue true v)
  | VJ v -> Printf.sprintf "idJ %s" (ppValue true v)
  | VIdp v -> "idp " ^ ppValue true v
  | VRev p -> ppValue true p ^ "⁻¹"
  | VTrans (p, q) -> ppValue true p ^ " ⬝ " ^ ppValue true q
  | VBoundary (a, b, x) -> Printf.sprintf "∂ %s %s %s" (ppValue true a) (ppValue true b) (ppValue true x)
  | VLeft (a, b) -> Printf.sprintf "left %s %s" (ppValue true a) (ppValue true b)
  | VRight (a, b) -> Printf.sprintf "right %s %s" (ppValue true a) (ppValue true b)
  | VSymm v -> "∂-symm " ^ ppValue true v
  | VComp (a, b) -> Printf.sprintf "∂-comp %s %s" (ppValue true a) (ppValue true b)
  | VBLeft (a, b) -> Printf.sprintf "∂-left %s %s" (ppValue true a) (ppValue true b)
  | VBRight (a, b) -> Printf.sprintf "∂-right %s %s" (ppValue true a) (ppValue true b)
  | VBCong (f, x, v) -> Printf.sprintf "∂-cong %s %s %s" (ppValue true f) (ppValue true x) (ppValue true v)
  | VMeet (p, x, v) -> Printf.sprintf "meet %s %s %s" (ppValue true p) (ppValue true x) (ppValue true v)
  | VCoe (p, x) -> Printf.sprintf "coe %s %s" (ppValue true p) (ppValue true x)
  | VCong (a, b) -> Printf.sprintf "cong %s %s" (ppValue true a) (ppValue true b)
  | VUA e -> Printf.sprintf "ua %s" (ppValue true e)
  in match v with
  | Var _ | VFst _ | VSnd _ | VPre _
  | VKan _ | VHole | VPair _ | VRev _ -> x
  | _ -> parens paren x

and showValue v = ppValue false v
and showClos p t clos = showValue (clos (Var (p, t)))

and showTele p x =
  Printf.sprintf "(%s : %s)" (showName p) (showValue x)

and showTermBind : name * record -> string option = function
  | p, (Local, _, t) -> Some (Printf.sprintf "%s := %s" (showName p) (showTerm t))
  | _, _             -> None

and showPi x p clos = match p with
  | Irrefutable -> Printf.sprintf "%s → %s" (ppValue true x) (showClos p x clos)
  | _           -> Printf.sprintf "Π %s, %s" (showTele p x) (showClos p x clos)

and isRhoVisible = Env.exists (fun _ -> isGlobal)

and showRho ctx : string = Env.bindings ctx |> List.filter_map showTermBind |> String.concat ", "

and showTerm : term -> string = function Exp e -> showExp e | Value v -> showValue v

let showGamma (ctx : ctx) : string =
  Env.bindings ctx
  |> List.filter_map
      (fun (p, x) -> match x with
        | Local, t, _ -> Some (Printf.sprintf "%s : %s" (showName p) (showTerm t))
        | _, _, _ -> None)
  |> String.concat "\n"
