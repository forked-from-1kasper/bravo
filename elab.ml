open Ident
open Error
open Expr

let extSigG : value -> value * clos = function
  | VSig (t, g) -> (t, g)
  | u -> raise (ExpectedSig u)

let extSet : value -> int = function
  | VPre n | VKan n -> n
  | v               -> raise (ExpectedVSet v)

let extKan : value -> int = function
  | VKan n -> n
  | v      -> raise (ExpectedFibrant v)

let path v a b = VApp (VApp (VPath v, a), b)
let extPath = function
  | VApp (VApp (VPath v, a), b) -> (v, a, b)
  | v                           -> raise (ExpectedPath v)

let extVar ctx x = match Env.find_opt x ctx with
  | Some (_, _, Value (Var (y, _))) -> y
  | Some (_, _, Exp (EVar y)) -> y
  | _ -> x

let imax a b = match a, b with
  | VKan u, VKan v -> VKan (max u v)
  | VPre u, VPre v | VPre u, VKan v | VKan u, VPre v -> VPre (max u v)
  | VKan _, _ | VPre _, _ -> raise (ExpectedVSet b)
  | _, _ -> raise (ExpectedVSet a)

let univImpl a b = match a, b with
  | VKan u, VKan v | VPre u, VKan v -> VKan (max u v)
  | VPre u, VPre v | VKan u, VPre v -> VPre (max u v)
  | VKan _, _      | VPre _, _      -> raise (ExpectedVSet b)
  | _, _ -> raise (ExpectedVSet a)

let implv a b ctx = VPi (a, (Irrefutable, b, ctx))

let impl a b = EPi (a, (Irrefutable, b))
let prod a b = ESig (a, (Irrefutable, b))

let rec salt (ns : name Env.t) : exp -> exp = function
  | ELam (a, (p, b))   -> saltTele eLam ns p a b
  | EKan n             -> EKan n
  | EPi (a, (p, b))    -> saltTele ePi ns p a b
  | ESig (a, (p, b))   -> saltTele eSig ns p a b
  | EPair (a, b)       -> EPair (salt ns a, salt ns b)
  | EFst e             -> EFst (salt ns e)
  | ESnd e             -> ESnd (salt ns e)
  | EApp (f, x)        -> EApp (salt ns f, salt ns x)
  | EVar x             -> EVar (freshVar ns x)
  | EHole              -> EHole
  | EPre n             -> EPre n
  | EId e              -> EId (salt ns e)
  | ERefl e            -> ERefl (salt ns e)
  | EJ e               -> EJ (salt ns e)
  | EPath e            -> EPath (salt ns e)
  | EIdp e             -> EIdp (salt ns e)
  | EInv p             -> EInv (salt ns p)
  | ETrans (p, q)      -> ETrans (salt ns p, salt ns q)

and saltTele ctor ns p a b =
  let x = fresh p in ctor x (salt ns a) (salt (Env.add p x ns) b)

let freshExp = salt Env.empty
