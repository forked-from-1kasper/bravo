open Error
open Trace
open Ident
open Elab
open Expr

let ieq u v : bool = !Prefs.girard || u = v
let vfst : value -> value = function
  | VPair (u, _) -> u
  (* (meet p x H).1 ~> x *)
  | VMeet (_, x, _) -> x
  | v            -> VFst v

let vsnd : value -> value = function
  | VPair (_, u) -> u
  | v            -> VSnd v

(* Evaluator *)
let rec eval (e0 : exp) (ctx : ctx) = traceEval e0; match e0 with
  | EPre u              -> VPre u
  | EKan u              -> VKan u
  | EVar x              -> getRho ctx x
  | EHole               -> VHole
  | EPi  (a, (p, b))    -> let t = eval a ctx in VPi (t, (p, closByVal ctx p t b))
  | ESig (a, (p, b))    -> let t = eval a ctx in VSig (t, (p, closByVal ctx p t b))
  | ELam (a, (p, b))    -> let t = eval a ctx in VLam (t, (p, closByVal ctx p t b))
  | EApp (f, x)         -> app (eval f ctx, eval x ctx)
  | EPair (e1, e2)      -> VPair (eval e1 ctx, eval e2 ctx)
  | EFst e              -> vfst (eval e ctx)
  | ESnd e              -> vsnd (eval e ctx)
  | EId e               -> VId (eval e ctx)
  | ERefl e             -> VRefl (eval e ctx)
  | EJ e                -> VJ (eval e ctx)
  | EPath (e, a, b)     -> VPath (eval e ctx, eval a ctx, eval b ctx)
  | EIdp e              -> VIdp (eval e ctx)
  | ERev p              -> rev (eval p ctx)
  | ETrans (p, q)       -> trans (eval p ctx, eval q ctx)
  | EBoundary (a, b, x) -> VBoundary (eval a ctx, eval b ctx, eval x ctx)
  | ELeft (a, b)        -> VLeft (eval a ctx, eval b ctx)
  | ERight (a, b)       -> VRight (eval a ctx, eval b ctx)
  | ESymm e             -> symm (eval e ctx)
  | EComp (a, b)        -> bcomp (eval a ctx) (eval b ctx)
  | EBLeft (e, p)       -> bleft (eval e ctx) (eval p ctx)
  | EBRight (e, p)      -> bright (eval e ctx) (eval p ctx)
  | EBCong (f, x, e)    -> bcong (eval f ctx) (eval x ctx) (eval e ctx)
  | EMeet (p, x, e)     -> meet (eval p ctx) (eval x ctx) (eval e ctx)
  | ECoe (p, x)         -> coe (eval p ctx) (eval x ctx)
  | ECong (f, p)        -> cong (eval f ctx) (eval p ctx)

and bcomp a b = reduceBoundary (VComp (a, b))
and bleft v p = reduceBoundary (VBLeft (v, p))
and bright v p = reduceBoundary (VBRight (v, p))

and trans = function
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

and symm = function
  (* ∂-symm (left a b) ~> right b a *)
  | VLeft (a, b) -> VRight (b, a)
  (* ∂-symm (right a b) ~> left b a *)
  | VRight (a, b) -> VLeft (b, a)
  (* ∂-symm (∂-symm H) ~> H *)
  | VSymm v -> v
  | v -> VSymm v

and bcong f x = function
  (* ∂-cong f a (left a b) ~> left (f a (left a b)) (f b (right a b)) *)
  | VLeft (a, b) -> VLeft (app (app (f, a), VLeft (a, b)), app (app (f, b), VRight (a, b)))
  (* ∂-cong f b (right a b) ~> right (f a (left a b)) (f b (right a b)) *)
  | VRight (a, b) -> VRight (app (app (f, a), VLeft (a, b)), app (app (f, b), VRight (a, b)))
  | v -> VBCong (f, x, v)

and reduceBoundary v =
  let (a, b, x) = extBoundary (inferV v) in
  if conv a x then VLeft (a, b)
  else if conv b x then VRight (a, b) else v

and apd t a b k f p =
  let x = freshName "x" in
  let y = freshName "y" in
  let h1 = freshName "σ" in
  let h2 = freshName "σ′" in
  cong (VLam (t, (x, fun x ->
    VLam (VBoundary (a, b, x), (h1, fun h1 ->
      coe (cong
        (VLam (t, (y, fun y ->
          VLam (VBoundary (x, b, y), (h2, fun h2 -> k y (bcomp h1 h2))))))
        (rev (vsnd (meet (rev p) x (symm h1))))) (f x h1)))))) p

and ap t f a b p =
  let x = freshName "x" in
  let h = freshName "σ" in
  cong (VLam (t, (x, fun x ->
    VLam (VBoundary (a, b, x), (h, fun _ -> f x))))) p

and coe p x = match p, x with
  (* coe (idp α) x ~> x *)
  | VIdp _, _ -> x
  (* coe p (coe q y) ~> coe (q ⬝ p) y *)
  | _, VCoe (q, y) -> coe (trans (q, p)) y
  | VCong (VLam (t, (x, f)), r), v ->
    let g = f (Var (x, t)) in let (k, _) = extPi (inferV g) in
    let y = freshName "σ" in let y' = Var (y, k) in
    begin match app (g, y') with
      | VPath _ ->
        let (t, a, b) = extPath (inferV r) in
        let t' x h = let (v, _, _) = extPath (app (f x, h)) in v in
        let f' x h = let (_, v, _) = extPath (app (f x, h)) in v in
        let g' x h = let (_, _, v) = extPath (app (f x, h)) in v in

        let p1 = apd t a b t' f' r in
        let p3 = apd t a b t' g' r in

        let x = freshName "x" in let h = freshName "σ" in
        let p2 = ap (t' a (VLeft (a, b)))
          (coe (cong (VLam (t, (x, fun x ->
            VLam (VBoundary (a, b, x), (h, fun h -> t' x h))))) r))
          (f' a (VLeft (a, b))) (g' a (VLeft (a, b))) v in

        trans (rev p1, trans (p2, p3))

      | VPi _ ->
        let (t, a, b) = extPath (inferV r) in
        let t' x h = let (v, _) = extPi (app (f x, h)) in v in
        let f' x h = let (_, (_, v)) = extPi (app (f x, h)) in v in

        let x = freshName "x" in
        let y1 = freshName "y" in let y2 = freshName "y′" in
        let h1 = freshName "σ" in let h2 = freshName "σ′" in

        let phi x =
          coe (cong (VLam (t, (y1, fun y1 ->
            VLam (VBoundary (a, b, y1), (h1, fun h1 ->
              f' y1 h1 (coe (cong (VLam (t, (y2, fun y2 ->
                VLam (VBoundary (b, y1, y2), (h2, fun h2 ->
                  t' y2 (bcomp h1 (symm h2)))))))
                (vsnd (meet (rev r) y1 (symm h1)))) x)))))) r)
            (app (v, coe (cong
              (VLam (t, (y1, fun y ->
                VLam (VBoundary (b, a, y), (h1, fun h ->
                  t' y (symm h)))))) (rev r)) x)) in
        VLam (t' b (VRight (a, b)), (x, phi))

      | VSig _ ->
        let (t, a, b) = extPath (inferV r) in
        let t' x h = let (v, _) = extSig (app (f x, h)) in v in
        let f' x h = let (_, (_, v)) = extSig (app (f x, h)) in v in

        let y1 = freshName "y" in let y2 = freshName "y′" in
        let h1 = freshName "σ" in let h2 = freshName "σ′" in

        let fst = coe (cong (VLam (t, (y1, fun y1 ->
          VLam (VBoundary (a, b, y1), (h1, fun h1 ->
            t' y1 h1))))) r) (vfst v) in

        let snd = coe (cong (VLam (t, (y1, fun y1 ->
        VLam (VBoundary (a, b, y1), (h1, fun h1 ->
          f' y1 h1 (coe (cong (VLam (t, (y2, fun y2 ->
            VLam (VBoundary (a, y1, y2), (h2, fun h2 ->
              t' y2 (symm (bcomp (symm h1) (symm h2))))))))
              (vsnd (meet r y1 h1))) (vfst v))))))) r) (vsnd v) in

         VPair (fst, snd)
      | _ -> VCoe (p, v)
    end
  | _, _ -> VCoe (p, x)

and closByVal ctx p t e v =
  (* dirty hack to handle free variables introduced by type checker *)
  let ctx' = match v with
  | Var (x, t) -> if Env.mem x ctx then ctx else upLocal ctx x t v
  | _          -> ctx in
  eval e (upLocal ctx' p t v)

and meet p x v =
  (* “∂ A a b x” is proof-irrelevant,
     so each element of “∂ a b a” is definitionally equal to “left a b”,
     each element of “∂ a b b” — to “right a b” *)
  let (a, b, y) = extBoundary (inferV v) in
  (* meet p a left  ~> (a, idp a) *)
  if conv a y then VPair (x, VIdp x)
  (* meet p b right ~> (b, p) *)
  else if conv b y then VPair (x, p)
  else VMeet (p, x, v)

and extCongLam t =
  let (dom, (x, f)) = extPi t in
  let (n, (y, g)) = extPi (f (Var (x, dom))) in
  let cod = g (Var (y, n)) in
  (dom, cod, x, y, extBoundary n)

and cong f p = match f, p with
  (* cong f (idp x) ~> idp (f x) *)
  | _, VIdp x -> VIdp (app (f, x))
  (* cong f p⁻¹ ~> (cong f p)⁻¹ *)
  | _, VRev p ->
    let t = inferV f in let (dom, _, _, _, _) = extCongLam t in
    let (_, b, a) = extPath (inferV p) in

    let x = freshName "x" in let y = freshName "σ" in
    let g = VLam (dom, (x, fun x ->
      VLam (VBoundary (b, a, x), (y, fun y ->
        app (app (f, x), symm y))))) in
    rev (cong g p)
  (* cong f (p ⬝ q) ~> cong f p ⬝ cong f q *)
  | _, VTrans (p, q) ->
    let t = inferV f in
    let (dom, _, _, _, _) = extCongLam t in
    let (_, a1, b1) = extPath (inferV p) in
    let (_, a2, b2) = extPath (inferV q) in

    let x = freshName "x" in let y = freshName "σ" in
    let g a b k =
    VLam (dom, (x, fun x ->
      VLam (VBoundary (a, b, x), (y, fun y ->
        app (app (f, x), k y))))) in

    trans (cong (g a1 b1 (fun y -> bright y q)) p,
           cong (g a2 b2 (fun y -> bleft y (rev q))) q)
  (* cong f (cong g p) ~> cong (f ∘ g) p *)
  | _, VCong (g, p) ->
    let t2 = inferV g in let (dom, _, _, _, _) = extCongLam t2 in

    let (_, a, b) = extPath (inferV p) in
    let x = freshName "x" in let sigma = freshName "σ" in

    let h = VLam (dom, (x, fun x ->
      VLam (VBoundary (a, b, x), (sigma, fun y ->
        app (app (f, app (app (g, x), y)), bcong g x y))))) in
    cong h p
  | _, _ ->
    let (t, _) = extPi (inferV f) in
    let x = freshName "x" in let x' = Var (x, t) in
    let g = app (f, x') in let (k, _) = extPi (inferV g) in
    let y = freshName "σ" in let y' = Var (y, k) in let v = app (g, y') in
    (* cong id p ~> p *)
    if x' = v then p
    (* cong (λ _, x) p ~> idp x *)
    else if not (mem x v || mem y v) then VIdp v
    else VCong (f, p)

and app (f, x) = match f, x with
  (* (λ (x : t), f) v ~> f[x/v] *)
  | VLam (_, (_, f)), v -> f v
  | _, _ -> VApp (f, x)

and getRho ctx x = match Env.find_opt x ctx with
  | Some (_, _, Value v) -> v
  | Some (_, _, Exp e)   -> eval e ctx
  | None                 -> raise (VariableNotFound x)

(* This is part of evaluator, not type checker *)
and inferV v = traceInferV v; match v with
  | Var (_, t) -> t
  | VLam (t, (x, f)) -> VPi (t, (x, fun x -> inferV (f x)))
  | VPi (t, (x, f)) | VSig (t, (x, f)) -> imax (inferV t) (inferV (f (Var (x, t))))
  | VFst e -> fst (extSig (inferV e))
  | VSnd e -> let (_, (_, g)) = extSig (inferV e) in g (vfst e)
  | VCoe (p, _) -> let (_, t, _) = extPath (inferV p) in t
  | VMeet (p, _, _) -> let (t, a, _) = extPath (inferV p) in singl t a
  | VLeft (a, b) -> VBoundary (a, b, a)
  | VRight (a, b) -> VBoundary (a, b, b)
  | VCong (f, p) ->
    let (t, (x, g)) = extPi (inferV f) in
    let (t', (y, h)) = extPi (g (Var (x, t))) in
    let k = h (Var (y, t')) in

    let (a, b, _) = extPath (inferV p) in
    let fa = app (app (f, a), VLeft (a, b)) in
    let fb = app (app (f, b), VRight (a, b)) in
    VPath (k, fa, fb)
  | VSymm v -> let (a, b, x) = extBoundary (inferV v) in VBoundary (b, a, x)
  | VBLeft (v, p) -> let (_, b, x) = extBoundary (inferV v) in let (_, _, a) = extPath (inferV p) in VBoundary (a, b, x)
  | VBRight (v, p) -> let (a, _, x) = extBoundary (inferV v) in let (_, _, b) = extPath (inferV p) in VBoundary (a, b, x)
  | VBCong (f, x, v) -> let (a, b, _) = extBoundary (inferV v) in
    VBoundary (app (app (f, a), VLeft (a, b)), app (app (f, b), VRight (a, b)), app (app (f, x), v))
  | VComp (u, v) -> let (a, b, _) = extBoundary (inferV u) in
    let (_, _, y) = extBoundary (inferV v) in VBoundary (a, b, y)
  | VApp (f, x) -> let (_, (_, g)) = extPi (inferV f) in g x
  | VRefl v  -> VApp (VApp (VId (inferV v), v), v)
  | VIdp v -> VPath (inferV v, v, v)
  | VRev p -> let (v, a, b) = extPath (inferV p) in VPath (v, b, a)
  | VTrans (p, q) -> let (u, a, _) = extPath (inferV p) in let (_, _, c) = extPath (inferV q) in VPath (u, a, c)
  | VPre n -> VPre (n + 1)
  | VKan n -> VKan (n + 1)
  | VPath (v, _, _) -> inferV v
  | VBoundary (v, _, _) -> let n = extSet (inferV (inferV v)) in VPre n
  | v -> raise (ExpectedNeutral v)

(* Readback *)
and rbV v : exp = traceRbV v; match v with
  | VLam (t, g)         -> rbVTele eLam t g
  | VPair (u, v)        -> EPair (rbV u, rbV v)
  | VKan u              -> EKan u
  | VPi (t, g)          -> rbVTele ePi t g
  | VSig (t, g)         -> rbVTele eSig t g
  | VPre u              -> EPre u
  | Var (x, _)          -> EVar x
  | VApp (f, x)         -> EApp (rbV f, rbV x)
  | VFst k              -> EFst (rbV k)
  | VSnd k              -> ESnd (rbV k)
  | VHole               -> EHole
  | VId v               -> EId (rbV v)
  | VRefl v             -> ERefl (rbV v)
  | VJ v                -> EJ (rbV v)
  | VPath (v, a, b)     -> EPath (rbV v, rbV a, rbV b)
  | VIdp v              -> EIdp (rbV v)
  | VRev p              -> ERev (rbV p)
  | VTrans (p, q)       -> ETrans (rbV p, rbV q)
  | VBoundary (a, b, x) -> EBoundary (rbV a, rbV b, rbV x)
  | VLeft (a, b)        -> ELeft (rbV a, rbV b)
  | VRight (a, b)       -> ERight (rbV a, rbV b)
  | VSymm v             -> ESymm (rbV v)
  | VBLeft (v, p)       -> EBLeft (rbV v, rbV p)
  | VBRight (v, p)      -> EBRight (rbV v, rbV p)
  | VBCong (p, x, v)    -> EBCong (rbV p, rbV x, rbV v)
  | VComp (u, v)        -> EComp (rbV u, rbV v)
  | VMeet (p, x, v)     -> EMeet (rbV p, rbV x, rbV v)
  | VCoe (p, x)         -> ECoe (rbV p, rbV x)
  | VCong (f, p)        -> ECong (rbV f, rbV p)

and rbVTele ctor t (p, g) =
  let x = Var (p, t) in ctor p (rbV t) (rbV (g x))

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
    | VPi  (a, (p, f)), VPi  (b, (_, g))
    | VSig (a, (p, f)), VSig (b, (_, g))
    | VLam (a, (p, f)), VLam (b, (_, g)) ->
      let x = Var (p, a) in conv a b && conv (f x) (g x)
    | VLam (a, (p, f)), b | b, VLam (a, (p, f)) ->
      let x = Var (p, a) in conv (app (b, x)) (f x)
    | VApp (f, x), VApp (g, y) -> conv f g && conv x y
    | VPre u, VPre v -> ieq u v
    | Var (u, _), Var (v, _) -> u = v
    | VFst x, VFst y | VSnd x, VSnd y -> conv x y
    | VId u, VId v | VJ u, VJ v | VRefl u, VRefl v -> conv u v
    | VPath (t1, a1, b1), VPath (t2, a2, b2) -> conv t1 t2 && conv a1 a2 && conv b1 b2
    | VIdp a, VIdp b -> conv a b
    | VRev p, VRev q -> conv p q
    | VTrans (p1, q1), VTrans (p2, q2) -> conv p1 p2 && conv q1 q2
    | VBoundary (a1, b1, x1), VBoundary (a2, b2, x2) -> conv a1 a2 && conv b1 b2 && conv x1 x2
    | VSymm a, VSymm b -> conv a b
    | VLeft (a1, b1), VLeft (a2, b2) | VRight (a1, b1), VRight (a2, b2) -> conv a1 a2 && conv b1 b2
    | VBLeft (a1, b1), VBLeft (a2, b2) | VBRight (a1, b1), VBRight (a2, b2)
    | VComp (a1, b1), VComp (a2, b2) -> conv a1 a2 && conv b1 b2
    | VBCong (f1, x1, v1), VBCong (f2, x2, v2) -> conv f1 f2 && conv x1 x2 && conv v1 v2
    | VMeet (p1, x1, v1), VMeet (p2, x2, v2) -> conv p1 p2 && conv x1 x2 && conv v1 v2
    | VCoe (p1, x1), VCoe (p2, x2) -> conv p1 p2 && conv x1 x2
    | VCong (f1, p1), VCong (f2, p2) -> conv f1 f2 && conv p1 p2
    | _, _ -> false
  end || convProofIrrel v1 v2

and convProofIrrel v1 v2 =
  (* Id A a b is proof-irrelevant *)
  try match inferV v1, inferV v2 with
    | VApp (VApp (VId t1, a1), b1), VApp (VApp (VId t2, a2), b2) ->
      conv t1 t2 && conv a1 a2 && conv b1 b2
    | VBoundary (a1, b1, x1), VBoundary (a2, b2, x2) ->
      conv a1 a2 && conv b1 b2 && conv x1 x2
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
  | ELam (a, (p, b)), VPi (t, (_, g)) ->
    ignore (extSet (infer ctx a)); eqNf (eval a ctx) t;
    let x = Var (p, t) in let ctx' = upLocal ctx p t x in
    check ctx' b (g x)
  | EPair (e1, e2), VSig (t, (_, g)) ->
    ignore (extSet (infer ctx (rbV t)));
    check ctx e1 t; check ctx e2 (g (eval e1 ctx))
  | EHole, v -> traceHole v ctx
  | ERefl e, VApp (VApp (VId t, a), b) | EIdp e, VPath (t, a, b) ->
    check ctx e t; let v = eval e ctx in eqNf v a; eqNf v b
  | ERev p, VPath (t, a, b) -> check ctx p (VPath (t, b, a))
  | ETrans (p, q), VPath (t, a, c) ->
    let (u, x, y1) = extPath (infer ctx p) in let (v, y2, z) = extPath (infer ctx q) in
    eqNf u t; eqNf v t; eqNf y1 y2; eqNf x a; eqNf z c
  | e, VPre u -> begin
    match infer ctx e with
    | VKan v | VPre v -> if ieq u v then () else raise (Ineq (VPre u, VPre v))
    | t -> raise (Ineq (VPre u, t))
  end
  | e, t -> eqNf (infer ctx e) t
  with ex -> Printf.printf "When trying to typecheck\n  %s\nAgainst type\n  %s\n" (showExp e0) (showValue t0); raise ex

and infer ctx e : value = traceInfer e; try match e with
  | EVar x -> lookup x ctx
  | EKan u -> VKan (u + 1)
  | ESig (a, (p, b)) | EPi (a, (p, b)) -> inferTele ctx p a b
  | ELam (a, (p, b)) -> inferLam ctx p a b
  | EApp (f, x) -> begin match infer ctx f with
    | VPi (t, (_, g)) -> check ctx x t; g (eval x ctx)
    | v -> raise (ExpectedPi v)
  end
  | EFst e -> fst (extSig (infer ctx e))
  | ESnd e -> let (_, (_, g)) = extSig (infer ctx e) in g (vfst (eval e ctx))
  | EPre u -> VPre (u + 1)
  | EPath (e, a, b) -> let t = eval e ctx in check ctx a t; check ctx b t; infer ctx e
  | EId e -> let v = eval e ctx in let n = extSet (infer ctx e) in implv v (implv v (VPre n))
  | ERefl e -> let v = eval e ctx in let t = infer ctx e in VApp (VApp (VId t, v), v)
  | EJ e -> inferJ ctx e
  | EIdp e -> let v = eval e ctx in let t = infer ctx e in VPath (t, v, v)
  | ERev p -> let (v, a, b) = extPath (infer ctx p) in VPath (v, b, a)
  | ETrans (p, q) -> let (u, a, x) = extPath (infer ctx p) in let (v, y, c) = extPath (infer ctx q) in
    eqNf u v; eqNf x y; VPath (u, a, c)
  | EBoundary (a, b, x) -> let t = infer ctx a in check ctx b t; check ctx x t; let n = extSet (inferV t) in VPre n
  | ELeft (a, b) -> let t = infer ctx a in check ctx b t; let x = eval a ctx in let y = eval b ctx in VBoundary (x, y, x)
  | ERight (a, b) -> let t = infer ctx a in check ctx b t; let x = eval a ctx in let y = eval b ctx in VBoundary (x, y, y)
  | ESymm e -> inferSymm ctx e
  | EBLeft (e, p) -> let (a, b, x) = extBoundary (infer ctx e) in
    let (_, a', c) = extPath (infer ctx p) in eqNf a a'; VBoundary (c, b, x)
  | EBRight (e, p) -> let (a, b, x) = extBoundary (infer ctx e) in
    let (_, b', c) = extPath (infer ctx p) in eqNf b b'; VBoundary (a, c, x)
  | EBCong (f, x, e) -> let (a, b, x') = extBoundary (infer ctx e) in
    let y = eval x ctx in let (t, k, p, q, (a', b', _)) = extCongLam (infer ctx f) in
    eqNf a a'; eqNf b b'; eqNf y x'; check ctx x t;
    if mem p k || mem q k then raise (ExpectedNonDependent k); let g = eval f ctx in
    VBoundary (app (app (g, a), VLeft (a, b)), app (app (g, b), VRight (a, b)), app (app (g, y), eval e ctx))
  | EComp (a, b) -> inferComp ctx a b
  | EMeet (p, x, e) -> inferMeet ctx p x e
  | ECoe (p, x) -> let (e, a, b) = extPath (infer ctx p) in ignore (extKan e); check ctx x a; b
  | ECong (f, p) -> inferCong ctx f p
  | e -> raise (InferError e)
  with ex -> Printf.printf "When trying to infer type of\n  %s\n" (showExp e); raise ex

and inferTele ctx p a b =
  ignore (extSet (infer ctx a));
  let t = eval a ctx in let x = Var (p, t) in
  let ctx' = upLocal ctx p t x in
  let v = infer ctx' b in imax (infer ctx a) v

and inferLam ctx p a e =
  ignore (extSet (infer ctx a)); let t = eval a ctx in
  ignore (infer (upLocal ctx p t (Var (p, t))) e);
  VPi (t, (p, fun x -> infer (upLocal ctx p t x) e))

and inferJ ctx e =
  let n = extSet (infer ctx e) in let x = freshName "x" in let y = freshName "y" in
  let pi = freshName "P" in let p = freshName "p" in

  let v = eval e ctx in let t = VPi (v, (x, fun x ->
    VPi (v, (y, fun y -> implv (idv v x y) (VPre n))))) in

  VPi (t, (pi, fun pi ->
    VPi (v, (x, fun x ->
      implv (app (app (app (pi, x), x), VRefl x))
            (VPi (v, (y, fun y ->
              VPi (idv v x y, (p, fun p ->
                app (app (app (pi, x), y), p))))))))))

and inferSymm ctx e =
  let (a, b, x) = extBoundary (infer ctx e) in VBoundary (b, a, x)

and inferComp ctx a b =
  let (a1, b1, x1) = extBoundary (infer ctx a) in
  let (a2, b2, x2) = extBoundary (infer ctx b) in
  eqNf b1 b2; eqNf x1 a2; VBoundary (a1, b1, x2)

and singl t x = let y = freshName "y" in VSig (t, (y, fun y -> VPath (t, x, y)))

and inferMeet ctx p x e =
  let (t, a, b) = extPath (infer ctx p) in
  let (a', b', x') = extBoundary (infer ctx e) in
  check ctx x t; eqNf a a'; eqNf b b'; eqNf (eval x ctx) x'; singl t a

and inferCong ctx f p =
  let (t, a, b) = extPath (infer ctx p) in
  let (t', k, x, y, (a', b', x')) = extCongLam (infer ctx f) in

  ignore (extKan (inferV t')); ignore (extKan (inferV k));
  eqNf t t'; eqNf (Var (x, t')) x'; eqNf a a'; eqNf b b';
  if mem x k || mem y k then raise (ExpectedNonDependent k);

  let f' = eval f ctx in
  let fa = app (app (f', a), VLeft (a, b)) in
  let fb = app (app (f', b), VRight (a, b)) in
  VPath (k, fa, fb)

and mem x = function
  | Var (y, _) -> x = y
  | VSig (t, (p, f)) | VPi (t, (p, f)) | VLam (t, (p, f)) ->
    mem x t || mem x (f (Var (p, t)))
  | VKan _ | VPre _ | VHole -> false

  | VFst e  | VSnd e  | VId e   | VRefl e
  | VJ e    | VIdp e  | VRev e  | VSymm e -> mem x e

  | VPair (a, b)  | VComp (a, b) | VApp (a, b)
  | VCoe (a, b)   | VCong (a, b) | VTrans (a, b)
  | VLeft (a, b)  | VRight (a, b)
  | VBLeft (a, b) | VBRight (a, b) -> mem x a || mem x b

  | VBCong (a, b, c)    | VPath (a, b, c)
  | VBoundary (a, b, c) | VMeet (a, b, c) -> mem x a || mem x b || mem x c
