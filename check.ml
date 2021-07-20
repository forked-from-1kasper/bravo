open Error
open Trace
open Ident
open Elab
open Expr

let ieq u v : bool = !Prefs.girard || u = v
let vfst : value -> value = function
  | VPair (u, _) -> u
  | v            -> VFst v

let vsnd : value -> value = function
  | VPair (_, u) -> u
  | v            -> VSnd v

(* Evaluator *)
let rec eval (e0 : exp) (ctx : ctx) = traceEval e0; match e0 with
  | EPre u             -> VPre u
  | EKan u             -> VKan u
  | EVar x             -> getRho ctx x
  | EHole              -> VHole
  | EPi  (a, (p, b))   -> VPi (eval a ctx, (p, b, ctx))
  | ELam (a, (p, b))   -> VLam (eval a ctx, (p, b, ctx))
  | EApp (f, x)        -> app (eval f ctx, eval x ctx)
  | ESig (a, (p, b))   -> VSig (eval a ctx, (p, b, ctx))
  | EPair (e1, e2)     -> VPair (eval e1 ctx, eval e2 ctx)
  | EFst e             -> vfst (eval e ctx)
  | ESnd e             -> vsnd (eval e ctx)
  | EId e              -> VId (eval e ctx)
  | ERefl e            -> VRefl (eval e ctx)
  | EJ e               -> VJ (eval e ctx)
  | EPath e            -> VPath (eval e ctx)
  | EIdp e             -> VIdp (eval e ctx)
  | ERev p             -> rev (eval p ctx)
  | ETrans (p, q)      -> trans (eval p ctx, eval q ctx)
  | EBoundary e        -> VBoundary (eval e ctx)
  | ELeft e            -> VLeft (eval e ctx)
  | ERight e           -> VRight (eval e ctx)
  | ESymm e            -> VSymm (eval e ctx)
  | EMeet e            -> VMeet (eval e ctx)
  | EJoin e            -> VJoin (eval e ctx)
  | ECoe e             -> VCoe (eval e ctx)
  | ECong (a, b)       -> VCong (eval a ctx, eval b ctx)

and trans : value * value -> value = function
  | VTrans (p, q), r       -> trans (p, trans (q, r))
  | VIdp _, p | p, VIdp _  -> p
  | VRev p, VTrans (q, r)  -> if conv p q then r else VTrans (VRev p, VTrans (q, r))
  | p, VTrans (VRev q, r)  -> if conv p q then r else VTrans (p, VTrans (VRev q, r))
  | VRev p, q              -> if conv p q then let (_, _, v) = extPath (inferV p) in VIdp v else VTrans (VRev p, q)
  | p, VRev q              -> if conv p q then let (_, v, _) = extPath (inferV p) in VIdp v else VTrans (p, VRev q)
  | p, q                   -> VTrans (p, q)

and rev : value -> value = function
  | VRev p        -> p
  | VIdp v        -> VIdp v
  | VTrans (p, q) -> trans (rev q, rev p)
  | v             -> VRev v

and closByVal t x v = let (p, e, ctx) = x in traceClos e p v;
  (* dirty hack to handle free variables introduced by type checker,
     for example, while checking terms like p : Path P a b *)
  let ctx' = match v with
  | Var (x, t) -> if Env.mem x ctx then ctx else upLocal ctx x t v
  | _          -> ctx in
  eval e (upLocal ctx' p t v)

and app : value * value -> value = function
  (* ∂-symm (left a b) ~> right b a *)
  | VApp (VApp (VApp (VSymm _, _), _), _),
    VApp (VApp (VLeft v, a), b) -> VApp (VApp (VRight v, b), a)
  (* ∂-symm (right a b) ~> left b a *)
  | VApp (VApp (VApp (VSymm _, _), _), _),
    VApp (VApp (VRight v, a), b) -> VApp (VApp (VLeft v, b), a)
  (* meet p a left  ~> (a, idp a) *)
  | VApp (VApp (VApp (VApp (VMeet _, a), _), _), _),
    VApp (VApp (VLeft _, _), _) -> VPair (a, VIdp a)
  (* meet p b right ~> (b, p) *)
  | VApp (VApp (VApp (VApp (VMeet _, _), b), p), _),
    VApp (VApp (VRight _, _), _) -> VPair (b, p)
  (* join p a left ~> (b, p) *)
  | VApp (VApp (VApp (VApp (VJoin _, _), b), p), _),
    VApp (VApp (VLeft _, _), _)  -> VPair (b, p)
  (* join p b right ~> (a, idp a) *)
  | VApp (VApp (VApp (VApp (VJoin _, a), _), _), _),
    VApp (VApp (VRight _, _), _) -> VPair (a, VIdp a)
  (* (λ (x : t), f) v ~> f[x/v] *)
  | VLam (t, f), v -> closByVal t f v
  | f, x -> VApp (f, x)

and getRho ctx x = match Env.find_opt x ctx with
  | Some (_, _, Value v) -> v
  | Some (_, _, Exp e)   -> eval e ctx
  | None                 -> raise (VariableNotFound x)

(* This is part of evaluator, not type checker *)
and inferV v = traceInferV v; match v with
  | Var (_, t)               -> t
  | VFst e                   -> fst (extSigG (inferV e))
  | VSnd e                   -> let (t, g) = extSigG (inferV e) in closByVal t g (VFst e)
  | VApp (f, x)              -> begin match inferV f with
    | VPi (t, g) -> closByVal t g x
    | v -> raise (ExpectedPi v)
  end
  | VRefl v                  -> VApp (VApp (VId (inferV v), v), v)
  | VIdp v                   -> VApp (VApp (VPath (inferV v), v), v)
  | VRev p                   -> let (v, a, b) = extPath (inferV p) in pathv v b a
  | VTrans (p, q)            -> let (u, a, _) = extPath (inferV p) in let (_, _, c) = extPath (inferV q) in pathv u a c
  | VPre n                   -> VPre (n + 1)
  | VKan n                   -> VKan (n + 1)
  | v                        -> raise (ExpectedNeutral v)

(* Readback *)
and rbV v : exp = traceRbV v; match v with
  | VLam (t, g)        -> rbVTele eLam t g
  | VPair (u, v)       -> EPair (rbV u, rbV v)
  | VKan u             -> EKan u
  | VPi (t, g)         -> rbVTele ePi t g
  | VSig (t, g)        -> rbVTele eSig t g
  | VPre u             -> EPre u
  | Var (x, _)         -> EVar x
  | VApp (f, x)        -> EApp (rbV f, rbV x)
  | VFst k             -> EFst (rbV k)
  | VSnd k             -> ESnd (rbV k)
  | VHole              -> EHole
  | VId v              -> EId (rbV v)
  | VRefl v            -> ERefl (rbV v)
  | VJ v               -> EJ (rbV v)
  | VPath v            -> EPath (rbV v)
  | VIdp v             -> EIdp (rbV v)
  | VRev p             -> ERev (rbV p)
  | VTrans (p, q)      -> ETrans (rbV p, rbV q)
  | VBoundary v        -> EBoundary (rbV v)
  | VLeft v            -> ELeft (rbV v)
  | VRight v           -> ERight (rbV v)
  | VSymm v            -> ESymm (rbV v)
  | VMeet v            -> EMeet (rbV v)
  | VJoin v            -> EJoin (rbV v)
  | VCoe v             -> ECoe (rbV v)
  | VCong (a, b)       -> ECong (rbV a, rbV b)

and rbVTele ctor t g =
  let (p, _, _) = g in let x = Var (p, t) in
  ctor p (rbV t) (rbV (closByVal t g x))

and prune ctx x = match Env.find_opt x ctx with
  | Some (_, _, Exp e)   -> e
  | Some (_, _, Value v) -> rbV v
  | None                 -> raise (VariableNotFound x)

(* Convertibility *)
and conv v1 v2 : bool = traceConv v1 v2;
  v1 == v2 || begin match v1, v2 with
    | VKan u, VKan v -> ieq u v
    | VPair (a, b), VPair (c, d) -> conv a c && conv b d
    | VPair (a, b), v | v, VPair (a, b) -> conv (vfst v) a && conv (vsnd v) b
    | VPi (a, g), VPi (b, h) | VSig (a, g), VSig (b, h)
    | VLam (a, g), VLam (b, h) ->
      let (p, _, _) = g in let x = Var (p, a) in
      conv a b && conv (closByVal a g x) (closByVal a h x)
    | VLam (a, (p, e, v)), b | b, VLam (a, (p, e, v)) ->
      let x = Var (p, a) in conv (app (b, x)) (closByVal a (p, e, v) x)
    | VApp (f, x), VApp (g, y) -> conv f g && conv x y
    | VPre u, VPre v -> ieq u v
    | Var (u, _), Var (v, _) -> u = v
    | VFst x, VFst y | VSnd x, VSnd y -> conv x y
    | VId u, VId v | VJ u, VJ v | VRefl u, VRefl v -> conv u v
    | VPath a, VPath b -> conv a b
    | VIdp a, VIdp b -> conv a b
    | VRev p, VRev q -> conv p q
    | VTrans (p1, q1), VTrans (p2, q2) -> conv p1 p2 && conv q1 q2
    | VBoundary a, VBoundary b | VSymm a, VSymm b
    | VLeft a, VLeft b | VRight a, VRight b -> conv a b
    | VMeet a, VMeet b | VJoin a, VJoin b -> conv a b
    | VCoe a, VCoe b -> conv a b
    | VCong (a1, b1), VCong (a2, b2) -> conv a1 a2 && conv b1 b2
    | _, _ -> false
  end || convProofIrrel v1 v2

and convProofIrrel v1 v2 =
  (* Id A a b is proof-irrelevant *)
  try match inferV v1, inferV v2 with
    | VApp (VApp (VId t1, a1), b1), VApp (VApp (VId t2, a2), b2) ->
      conv t1 t2 && conv a1 a2 && conv b1 b2
    | VApp (VApp (VApp (VBoundary t1, a1), b1), x1),
      VApp (VApp (VApp (VBoundary t2, a2), b2), x2) ->
      conv t1 t2 && conv a1 a2 && conv b1 b2 && conv x1 x2
    | _, _ -> false
  with ExpectedNeutral _ -> false

and eqNf v1 v2 : unit = traceEqNF v1 v2;
  if conv v1 v2 then () else raise (Ineq (v1, v2))

(* Type checker itself *)
and lookup (x : name) (ctx : ctx) = match Env.find_opt x ctx with
  | Some (_, Value v, _) -> v
  | Some (_, Exp e, _)   -> eval e ctx
  | None                 -> raise (VariableNotFound x)

and check ctx (e0 : exp) (t0 : value) =
  traceCheck e0 t0; try match e0, t0 with
  | ELam (a, (p, b)), VPi (t, g) ->
    ignore (extSet (infer ctx a)); eqNf (eval a ctx) t;
    let x = Var (p, t) in let ctx' = upLocal ctx p t x in
    check ctx' b (closByVal t g x)
  | EPair (e1, e2), VSig (t, g) ->
    ignore (extSet (infer ctx (rbV t)));
    check ctx e1 t; check ctx e2 (closByVal t g (eval e1 ctx))
  | EHole, v -> traceHole v ctx
  | ERefl e, VApp (VApp (VId t, a), b) | EIdp e, VApp (VApp (VPath t, a), b) ->
    check ctx e t; let v = eval e ctx in eqNf v a; eqNf v b
  | ERev p, VApp (VApp (VPath t, a), b) -> check ctx p (pathv t b a)
  | ETrans (p, q), VApp (VApp (VPath t, a), c) ->
    let (u, x, y1) = extPath (infer ctx p) in let (v, y2, z) = extPath (infer ctx q) in
    eqNf u t; eqNf v t; eqNf y1 y2; eqNf x a; eqNf z c
  | e, VPre u -> begin
    match infer ctx e with
    | VKan v | VPre v -> if ieq u v then () else raise (Ineq (VPre u, VPre v))
    | t -> raise (Ineq (VPre u, t))
  end
  | e, t -> eqNf (infer ctx e) t
  with ex -> Printf.printf "When trying to typecheck\n  %s\nAgainst type\n  %s\n" (showExp e0) (showValue t0); raise ex

and infer ctx e : value = traceInfer e; match e with
  | EVar x -> lookup x ctx
  | EKan u -> VKan (u + 1)
  | ESig (a, (p, b)) -> inferTele ctx imax p a b
  | EPi (a, (p, b)) -> inferTele ctx univImpl p a b
  | ELam (a, (p, b)) -> inferLam ctx p a b
  | EApp (f, x) -> begin match infer ctx f with
    | VPi (t, g) -> check ctx x t; closByVal t g (eval x ctx)
    | v -> raise (ExpectedPi v)
  end
  | EFst e -> fst (extSigG (infer ctx e))
  | ESnd e -> let (t, g) = extSigG (infer ctx e) in closByVal t g (vfst (eval e ctx))
  | EPre u -> VPre (u + 1)
  | EPath p -> inferPath ctx p
  | EId e -> let v = eval e ctx in let n = extSet (infer ctx e) in implv v (impl e (EPre n)) ctx
  | ERefl e -> let v = eval e ctx in let t = infer ctx e in VApp (VApp (VId t, v), v)
  | EJ e -> inferJ ctx e
  | EIdp e -> let v = eval e ctx in let t = infer ctx e in VApp (VApp (VPath t, v), v)
  | ERev p -> let (v, a, b) = extPath (infer ctx p) in pathv v b a
  | ETrans (p, q) -> let (u, a, x) = extPath (infer ctx p) in let (v, y, c) = extPath (infer ctx q) in
    eqNf u v; eqNf x y; pathv u a c
  | EBoundary e -> let v = eval e ctx in let n = extSet (infer ctx e) in implv v (impl e (impl e (EPre n))) ctx
  | ELeft e -> inferLeft ctx e
  | ERight e -> inferRight ctx e
  | ESymm e -> inferSymm ctx e
  | EMeet e | EJoin e -> inferMeetJoin ctx e
  | ECoe e -> let n = extKan (infer ctx e) in let beta = fresh (name "β") in
    VPi (VKan n, (beta, impl (EApp (EApp (EPath (EKan n), e), EVar beta)) (impl e (EVar beta)), ctx))
  | ECong (a, b) -> inferCong ctx a b
  | e -> raise (InferError e)

and inferTele ctx binop p a b =
  ignore (extSet (infer ctx a));
  let t = eval a ctx in let x = Var (p, t) in
  let ctx' = upLocal ctx p t x in
  let v = infer ctx' b in binop (infer ctx a) v

and inferLam ctx p a e =
  ignore (extSet (infer ctx a)); let t = eval a ctx in let x = Var (p, t) in
  let ctx' = upLocal ctx p t x in VPi (t, (p, rbV (infer ctx' e), ctx))

and inferJ ctx e =
  let n = extSet (infer ctx e) in let x = fresh (name "x") in let y = fresh (name "y") in
  let pi = fresh (name "P") in let p = fresh (name "p") in let id = EApp (EApp (EId e, EVar x), EVar y) in
  VPi (eval (EPi (e, (x, EPi (e, (y, impl id (EPre n)))))) ctx,
        (pi, EPi (e, (x, impl (EApp (EApp (EApp (EVar pi, EVar x), EVar x), ERefl (EVar x)))
          (EPi (e, (y, EPi (id, (p, EApp (EApp (EApp (EVar pi, EVar x), EVar y), EVar p)))))))), ctx))

and inferPath ctx e =
  let t = infer ctx e in ignore (extSet t);
  implv (eval e ctx) (impl e (rbV t)) ctx

and inferLeft ctx e =
  let t = infer ctx e in ignore (extSet t);
  let a = fresh (name "a") in let b = fresh (name "b") in
  VPi (eval e ctx, (a, EPi (e, (b, boundary e (EVar a) (EVar b) (EVar a))), ctx))

and inferRight ctx e =
  let t = infer ctx e in ignore (extSet t);
  let a = fresh (name "a") in let b = fresh (name "b") in
  VPi (eval e ctx, (a, EPi (e, (b, boundary e (EVar a) (EVar b) (EVar b))), ctx))

and inferSymm ctx e =
  let t = infer ctx e in ignore (extSet t);
  let a = fresh (name "a") in let b = fresh (name "b") in let x = fresh (name "x") in
  VPi (eval e ctx, (a, EPi (e, (b, EPi (e,
    (x, impl (boundary e (EVar a) (EVar b) (EVar x))
            (boundary e (EVar b) (EVar a) (EVar x)))))), ctx))

and singl e a b = ESig (e, (b, EApp (EApp (EPath e, a), EVar b)))
and inferMeetJoin ctx e =
  let t = infer ctx e in ignore (extSet t);
  let a = fresh (name "a") in let b = fresh (name "b") in
  let x = fresh (name "x") in let z = fresh (name "z") in
  VPi (eval e ctx, (a, EPi (e, (b, impl (path e (EVar a) (EVar b))
    (EPi (e, (x, impl (boundary e (EVar a) (EVar b) (EVar x))
                      (singl e (EVar a) z)))))), ctx))

and inferCong ctx alpha beta =
  ignore (extKan (infer ctx alpha)); ignore (extKan (infer ctx alpha));
  let a = fresh (name "a") in let b = fresh (name "b") in let f = fresh (name "f") in
  let x = fresh (name "x") in let func = EPi (alpha, (x, impl (boundary alpha (EVar a) (EVar b) (EVar x)) beta)) in

  let left = EApp (EApp (EVar f, EVar a), EApp (EApp (ELeft alpha, EVar a), EVar b)) in
  let right = EApp (EApp (EVar f, EVar b), EApp (EApp (ERight alpha, EVar a), EVar b)) in

  VPi (eval alpha ctx, (a, EPi (alpha, (b, EPi (func,
    (f, impl (path alpha (EVar a) (EVar b)) (path beta left right))))), ctx))
