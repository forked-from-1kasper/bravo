open Ident

type exp =
  | EPre of Z.t | EKan of Z.t                                                 (* cosmos *)
  | EVar of name | EHole                                                   (* variables *)
  | EPi of exp * (name * exp) | ELam of exp * (name * exp) | EApp of exp * exp     (* Π *)
  | ESig of exp * (name * exp) | EPair  of exp * exp | EFst of exp | ESnd of exp   (* Σ *)
  | EId of exp | ERefl of exp | EJ of exp                            (* strict equality *)
  | EPath of exp * exp * exp | EIdp of exp | ERev of exp | ETrans of exp * exp  (* path *)
  | EBoundary of exp * exp * exp | ELeft of exp * exp | ERight of exp * exp        (* ∂ *)
  | ESymm of exp | EComp of exp * exp                                              (* ∂ *)
  | EBLeft of exp * exp | EBRight of exp * exp | EBApd of exp * exp * exp * exp    (* ∂ *)
  | EMeet of exp * exp * exp | ECoe of exp * exp | EApd of exp * exp  (* Kan operations *)
  | EUAWeak of exp * exp * exp * exp * exp * exp                          (* univalence *)
  | Equiv of exp * exp | EMkEquiv of exp * exp * exp * exp               (* equivalence *)
  | EN | EZero | ESucc | ENInd of exp                                              (* N *)
  | EZ | EPos | ENeg | EZInd of exp | EZSucc | EZPred                              (* Z *)
  | ES1 | EBase | ELoop | ES1Ind of exp | ES1IndS of exp                          (* S¹ *)
  | ER | Elem | EGlue | ERInd of exp | ERIndS of exp | ERInj                       (* R *)
  | EBot | EBotRec of exp                                                          (* ⊥ *)

type tele = name * exp

type scope = Local | Global

type value =
  | VKan of Z.t | VPre of Z.t
  | Var of name * value | VHole
  | VPi of value * clos | VLam of value * clos | VApp of value * value
  | VSig of value * clos | VPair of value * value | VFst of value | VSnd of value
  | VId of value | VRefl of value | VJ of value
  | VPath of value * value * value | VIdp of value | VRev of value | VTrans of value * value
  | VBoundary of value * value * value | VLeft of value * value | VRight of value * value
  | VSymm of value | VComp of value * value
  | VBLeft of value * value | VBRight of value * value | VBApd of value * value * value * value
  | VMeet of value * value * value | VCoe of value * value | VApd of value * value
  | VUAWeak of value * value * value * value * value * value
  | VEquiv of value * value | VMkEquiv of value * value * value * value
  | VN | VZero | VSucc | VNInd of value
  | VZ | VPos | VNeg | VZInd of value | VZSucc | VZPred
  | VS1 | VBase | VLoop | VS1Ind of value | VS1IndS of value
  | VR | VElem | VGlue | VRInd of value | VRIndS of value | VRInj
  | VBot | VBotRec of value

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

let upLocal ctx p t v : ctx = upVar p (Local, Value t, Value v) ctx
let upGlobal ctx p t v : ctx = upVar p (Global, Value t, Value v) ctx

let rec telescope ctor e : tele list -> exp = function
  | (p, a) :: xs -> ctor p a (telescope ctor e xs)
  | []           -> e

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
  | EBApd (f, p, x, e) -> Printf.sprintf "∂-apd %s %s %s %s" (ppExp true f) (ppExp true p) (ppExp true x) (ppExp true e)
  | EMeet (p, x, e) -> Printf.sprintf "meet %s %s %s" (ppExp true p) (ppExp true x) (ppExp true e)
  | ECoe (p, x) -> Printf.sprintf "coe %s %s" (ppExp true p) (ppExp true x)
  | EApd (a, b) -> Printf.sprintf "apd %s %s" (ppExp true a) (ppExp true b)
  | EUAWeak (a, b, f, g, mu, nu) -> Printf.sprintf "ua-weak %s %s %s %s %s %s" (ppExp true a) (ppExp true b) (ppExp true f) (ppExp true g) (ppExp true mu) (ppExp true nu)
  | Equiv (a, b) -> Printf.sprintf "%s ≃ %s" (ppExp true a) (ppExp true b)
  | EMkEquiv (a, b, f, e) -> Printf.sprintf "mkeqv %s %s %s %s" (ppExp true a) (ppExp true b) (ppExp true f) (ppExp true e)
  | EN -> "N" | EZero -> "zero" | ESucc -> "succ"
  | ENInd e -> Printf.sprintf "N-ind %s" (ppExp true e)
  | EZ -> "Z" | EPos -> "pos" | ENeg -> "neg" | EZSucc -> "Z-succ" | EZPred -> "Z-pred"
  | EZInd e -> Printf.sprintf "Z-ind %s" (ppExp true e)
  | ES1 -> "S¹" | EBase -> "base" | ELoop -> "loop"
  | ES1Ind e -> Printf.sprintf "S¹-ind %s" (ppExp true e)
  | ES1IndS e -> Printf.sprintf "S¹-indˢ %s" (ppExp true e)
  | ER -> "R" | Elem -> "elem" | EGlue -> "glue"
  | ERInd e -> Printf.sprintf "R-ind %s" (ppExp true e)
  | ERIndS e -> Printf.sprintf "R-indˢ %s" (ppExp true e) | ERInj -> "R-inj"
  | EBot -> "⊥" | EBotRec e -> Printf.sprintf "⊥-ind %s" (ppExp true e)
  in match e with
  | EKan _ | EPre _  | EVar _
  | EFst _ | ESnd _  | ERev _
  | EHole  | EPair _ | EBot
  | EN     | EZero   | ESucc
  | EZ     | EPos    | ENeg
  | ES1    | EBase   | ELoop
  | ER     | Elem    | EGlue -> x
  | _ -> parens paren x

and showExp e = ppExp false e
and showTele p x = Printf.sprintf "(%s : %s)" (showName p) (showExp x)

and showPiExp a p b = match p with
  | Irrefutable -> Printf.sprintf "%s → %s" (ppExp true a) (showExp b)
  | _           -> Printf.sprintf "Π %s, %s" (showTele p a) (showExp b)

let rec ppValue paren v = let x = match v with
  | VKan n -> "U" ^ showSubscript n
  | VLam (x, (p, clos)) -> Printf.sprintf "λ %s, %s" (showTele p x) (showClos p x clos)
  | VPi (x, (p, clos)) -> showPiValue x p clos
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
  | VBApd (f, p, x, v) -> Printf.sprintf "∂-apd %s %s %s %s" (ppValue true f) (ppValue true p) (ppValue true x) (ppValue true v)
  | VMeet (p, x, v) -> Printf.sprintf "meet %s %s %s" (ppValue true p) (ppValue true x) (ppValue true v)
  | VCoe (p, x) -> Printf.sprintf "coe %s %s" (ppValue true p) (ppValue true x)
  | VApd (a, b) -> Printf.sprintf "apd %s %s" (ppValue true a) (ppValue true b)
  | VUAWeak (a, b, f, g, mu, nu) -> Printf.sprintf "ua-weak %s %s %s %s %s %s" (ppValue true a) (ppValue true b) (ppValue true f) (ppValue true g) (ppValue true mu) (ppValue true nu)
  | VEquiv (a, b) -> Printf.sprintf "%s ≃ %s" (ppValue true a) (ppValue true b)
  | VMkEquiv (a, b, f, v) -> Printf.sprintf "mkeqv %s %s %s %s" (ppValue true a) (ppValue true b) (ppValue true f) (ppValue true v)
  | VN -> "N" | VZero -> "zero" | VSucc -> "succ"
  | VNInd e -> Printf.sprintf "N-ind %s" (ppValue true e)
  | VZ -> "Z" | VPos -> "pos" | VNeg -> "neg" | VZSucc -> "Z-succ" | VZPred -> "Z-pred"
  | VZInd e -> Printf.sprintf "Z-ind %s" (ppValue true e)
  | VS1 -> "S¹" | VBase -> "base" | VLoop -> "loop"
  | VS1Ind e -> Printf.sprintf "S¹-ind %s" (ppValue true e)
  | VS1IndS e -> Printf.sprintf "S¹-indˢ %s" (ppValue true e)
  | VR -> "R" | VElem -> "elem" | VGlue -> "glue"
  | VRInd e -> Printf.sprintf "R-ind %s" (ppValue true e)
  | VRIndS e -> Printf.sprintf "R-indˢ %s" (ppValue true e) | VRInj -> "R-inj"
  | VBot -> "⊥" | VBotRec e -> Printf.sprintf "⊥-ind %s" (ppValue true e)
  in match v with
  | VKan _ | VPre _  | Var _
  | VFst _ | VSnd _  | VRev _
  | VHole  | VPair _ | VBot
  | VN     | VZero   | VSucc
  | VZ     | VPos    | VNeg
  | VS1    | VBase   | VLoop
  | VR     | VElem   | VGlue -> x
  | _ -> parens paren x

and showValue v = ppValue false v
and showClos p t clos = showValue (clos (Var (p, t)))

and showTele p x = Printf.sprintf "(%s : %s)" (showName p) (showValue x)

and showPiValue x p clos = match p with
  | Irrefutable -> Printf.sprintf "%s → %s" (ppValue true x) (showClos p x clos)
  | _           -> Printf.sprintf "Π %s, %s" (showTele p x) (showClos p x clos)

and showTerm : term -> string = function Exp e -> showExp e | Value v -> showValue v

let showGamma (ctx : ctx) : string =
  Env.bindings ctx
  |> List.filter_map
      (fun (p, x) -> match x with
        | Local, t, _ -> Some (Printf.sprintf "%s : %s" (showName p) (showTerm t))
        | _, _, _     -> None)
  |> String.concat "\n"
