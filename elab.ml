open Ident
open Error
open Expr

let extPi : value -> value * clos = function
  | VPi (t, g) -> (t, g)
  | u -> raise (ExpectedPi u)

let extSig : value -> value * clos = function
  | VSig (t, g) -> (t, g)
  | u -> raise (ExpectedSig u)

let extSet : value -> Z.t = function
  | VPre n | VKan n -> n
  | v               -> raise (ExpectedVSet v)

let extKan : value -> Z.t = function
  | VKan n -> n
  | v      -> raise (ExpectedFibrant v)

let extPath = function
  | VPath (v, a, b) -> (v, a, b)
  | v -> raise (ExpectedPath v)

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
  | ELam (a, (p, b))             -> saltTele eLam ns p a b
  | EKan n                       -> EKan n
  | EPi (a, (p, b))              -> saltTele ePi ns p a b
  | ESig (a, (p, b))             -> saltTele eSig ns p a b
  | EPair (a, b)                 -> EPair (salt ns a, salt ns b)
  | ESigMk (g, a, b)             -> ESigMk (salt ns g, salt ns a, salt ns b)
  | EFst e                       -> EFst (salt ns e)
  | ESnd e                       -> ESnd (salt ns e)
  | EApp (f, x)                  -> EApp (salt ns f, salt ns x)
  | EVar x                       -> EVar (freshVar ns x)
  | EHole                        -> EHole
  | EPre n                       -> EPre n
  | EId e                        -> EId (salt ns e)
  | ERefl e                      -> ERefl (salt ns e)
  | EJ e                         -> EJ (salt ns e)
  | EPath (e, a, b)              -> EPath (salt ns e, salt ns a, salt ns b)
  | EIdp e                       -> EIdp (salt ns e)
  | ERev p                       -> ERev (salt ns p)
  | ETrans (p, q)                -> ETrans (salt ns p, salt ns q)
  | ECoe (p, x)                  -> ECoe (salt ns p, salt ns x)
  | EApd (a, b)                  -> EApd (salt ns a, salt ns b)
  | ESigProd (p, b, u, v, q)     -> ESigProd (salt ns p, salt ns b, salt ns u, salt ns v, salt ns q)
  | EUAWeak (a, b, f, g, mu, nu) -> EUAWeak (salt ns a, salt ns b, salt ns f, salt ns g, salt ns mu, salt ns nu)
  | EN                           -> EN
  | EZero                        -> EZero
  | ESucc                        -> ESucc
  | ENInd e                      -> ENInd (salt ns e)
  | EZ                           -> EZ
  | EPos                         -> EPos
  | ENeg                         -> ENeg
  | EZSucc                       -> EZSucc
  | EZPred                       -> EZPred
  | EZInd e                      -> EZInd (salt ns e)
  | ES1                          -> ES1
  | EBase                        -> EBase
  | ELoop                        -> ELoop
  | ES1Ind e                     -> ES1Ind (salt ns e)
  | ER                           -> ER
  | Elem                         -> Elem
  | EGlue                        -> EGlue
  | ERInd e                      -> ERInd (salt ns e)
  | EBot                         -> EBot
  | EBotRec e                    -> EBotRec (salt ns e)

and saltTele ctor ns p a b =
  let x = fresh p in ctor x (salt ns a) (salt (Env.add p x ns) b)

let freshExp = salt Env.empty

let convVar p = function
  | Var (q, _) -> p = q
  | _          -> false

let rho2 x x' y y' = Env.add y y' (Env.add x x' Env.empty)

let isCoeNeut = function
  | VIdp _ | VRev _
  | VTrans _ | VUAWeak _ -> false
  | _ -> true
