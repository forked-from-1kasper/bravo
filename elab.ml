open Ident
open Error
open Expr

let extPair : value -> value * value = function
  | VPair (u, v) -> (u, v)
  | v            -> raise (ExpectedPair v)

let extPi : value -> value * clos = function
  | VPi (t, g) -> (t, g)
  | u -> raise (ExpectedPi u)

let extSig : value -> value * clos = function
  | VSig (t, g) -> (t, g)
  | u -> raise (ExpectedSig u)

let extEquiv : value -> value * value = function
  | VEquiv (a, b) -> (a, b)
  | u -> raise (ExpectedEquiv u)

let extSet : value -> Z.t = function
  | VPre n | VKan n -> n
  | v               -> raise (ExpectedVSet v)

let extKan : value -> Z.t = function
  | VKan n -> n
  | v      -> raise (ExpectedFibrant v)

let extPath = function
  | VPath (v, a, b) -> (v, a, b)
  | v -> raise (ExpectedPath v)

let extBoundary = function
  | VBoundary (a, b, x) -> (a, b, x)
  | v -> raise (ExpectedBoundary v)

let extVar ctx x = match Env.find_opt x ctx with
  | Some (_, _, Value (Var (y, _))) -> y
  | Some (_, _, Exp (EVar y)) -> y
  | _ -> x

let imax a b = match a, b with
  | VKan u, VKan v -> VKan (max u v)
  | VPre u, VPre v | VPre u, VKan v | VKan u, VPre v -> VPre (max u v)
  | VKan _, _ | VPre _, _ -> raise (ExpectedVSet b)
  | _, _ -> raise (ExpectedVSet a)

let idv t x y = VApp (VApp (VId t, x), y)
let implv a b = VPi (a, (Irrefutable, fun _ -> b))
let prodv a b = VSig (a, (Irrefutable, fun _ -> b))

let succv n = VApp (VSucc, n)
let posv  n = VApp (VPos,  n)
let negv  n = VApp (VNeg,  n)

let elemv z = VApp (VElem, z)

let impl a b = EPi (a, (Irrefutable, b))
let prod a b = ESig (a, (Irrefutable, b))

let freshVar ns n = match Env.find_opt n ns with Some x -> x | None -> n

let rec salt (ns : name Env.t) : exp -> exp = function
  | ELam (a, (p, b))      -> saltTele eLam ns p a b
  | EKan n                -> EKan n
  | EPi (a, (p, b))       -> saltTele ePi ns p a b
  | ESig (a, (p, b))      -> saltTele eSig ns p a b
  | EPair (a, b)          -> EPair (salt ns a, salt ns b)
  | EFst e                -> EFst (salt ns e)
  | ESnd e                -> ESnd (salt ns e)
  | EApp (f, x)           -> EApp (salt ns f, salt ns x)
  | EVar x                -> EVar (freshVar ns x)
  | EHole                 -> EHole
  | EPre n                -> EPre n
  | EId e                 -> EId (salt ns e)
  | ERefl e               -> ERefl (salt ns e)
  | EJ e                  -> EJ (salt ns e)
  | EPath (e, a, b)       -> EPath (salt ns e, salt ns a, salt ns b)
  | EIdp e                -> EIdp (salt ns e)
  | ERev p                -> ERev (salt ns p)
  | ETrans (p, q)         -> ETrans (salt ns p, salt ns q)
  | EBoundary (a, b, x)   -> EBoundary (salt ns a, salt ns b, salt ns x)
  | ELeft (a, b)          -> ELeft (salt ns a, salt ns b)
  | ERight (a, b)         -> ERight (salt ns a, salt ns b)
  | ESymm e               -> ESymm (salt ns e)
  | EBLeft (e, p)         -> EBLeft (salt ns e, salt ns p)
  | EBRight (e, p)        -> EBRight (salt ns e, salt ns p)
  | EBApd (f, p, x, e)    -> EBApd (salt ns f, salt ns p, salt ns x, salt ns e)
  | EComp (a, b)          -> EComp (salt ns a, salt ns b)
  | EMeet (p, x, e)       -> EMeet (salt ns p, salt ns x, salt ns e)
  | ECoe (p, x)           -> ECoe (salt ns p, salt ns x)
  | EApd (a, b)           -> EApd (salt ns a, salt ns b)
  | EUA e                 -> EUA (salt ns e)
  | Equiv (a, b)          -> Equiv (salt ns a, salt ns b)
  | EMkEquiv (a, b, f, e) -> EMkEquiv (salt ns a, salt ns b, salt ns f, salt ns e)
  | EN                    -> EN
  | EZero                 -> EZero
  | ESucc                 -> ESucc
  | ENInd e               -> ENInd (salt ns e)
  | EZ                    -> EZ
  | EPos                  -> EPos
  | ENeg                  -> ENeg
  | EZSucc                -> EZSucc
  | EZPred                -> EZPred
  | EZInd e               -> EZInd (salt ns e)
  | ES1                   -> ES1
  | EBase                 -> EBase
  | ELoop                 -> ELoop
  | ES1Ind e              -> ES1Ind (salt ns e)
  | ES1IndS e             -> ES1IndS (salt ns e)
  | ER                    -> ER
  | Elem                  -> Elem
  | EGlue                 -> EGlue
  | ERInd e               -> ERInd (salt ns e)
  | ERIndS e              -> ERIndS (salt ns e)
  | ERInj                 -> ERInj
  | EBot                  -> EBot
  | EBotRec e             -> EBotRec (salt ns e)

and saltTele ctor ns p a b =
  let x = fresh p in ctor x (salt ns a) (salt (Env.add p x ns) b)

let freshExp = salt Env.empty

let convVar p = function
  | Var (q, _) -> p = q
  | _          -> false

let rho2 x x' y y' = Env.add y y' (Env.add x x' Env.empty)
