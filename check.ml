open Prelude
open Error
open Trace
open Ident
open Elab
open Expr

let ieq u v : bool = !Prefs.girard || u = v

let isProofIrrel = function
  | VApp (VApp (VId _, _), _) -> true
  | _                         -> false

let vfst : value -> value = function
  | VSigMk (_, u, _) -> u
  | v                -> VFst v

let vsnd : value -> value = function
  | VSigMk (_, _, u) -> u
  | v                -> VSnd v

(* Evaluator *)
let rec eval (e0 : exp) (ctx : ctx) = traceEval e0; match e0 with
  | EPre u                       -> VPre u
  | EKan u                       -> VKan u
  | EVar x                       -> getRho ctx x
  | EHole                        -> VHole
  | EPi  (a, (p, b))             -> let t = eval a ctx in VPi (t, (fresh p, closByVal ctx p t b))
  | ESig (a, (p, b))             -> let t = eval a ctx in VSig (t, (fresh p, closByVal ctx p t b))
  | ELam (a, (p, b))             -> let t = eval a ctx in VLam (t, (fresh p, closByVal ctx p t b))
  | EApp (f, x)                  -> app (eval f ctx, eval x ctx)
  | EPair (a, b)                 -> let u = eval a ctx in let v = eval b ctx in
    VSigMk (VLam (inferV u, (Irrefutable, fun _ -> inferV v)), u, v)
  | ESigMk (g, a, b)             -> VSigMk (eval g ctx, eval a ctx, eval b ctx)
  | EFst e                       -> vfst (eval e ctx)
  | ESnd e                       -> vsnd (eval e ctx)
  | EId e                        -> VId (eval e ctx)
  | ERefl e                      -> VRefl (eval e ctx)
  | EJ e                         -> VJ (eval e ctx)
  | EPath (e, a, b)              -> VPath (eval e ctx, eval a ctx, eval b ctx)
  | EIdp e                       -> VIdp (eval e ctx)
  | ERev p                       -> rev (eval p ctx)
  | ETrans (p, q)                -> trans (eval p ctx, eval q ctx)
  | ECoe (p, x)                  -> coe (eval p ctx) (eval x ctx)
  | EApd (f, p)                  -> apd (eval f ctx) (eval p ctx)
  | ESigProd (p, b, u, v, q)     -> sigProd (eval p ctx) (eval b ctx) (eval u ctx) (eval v ctx) (eval q ctx)
  | EUAWeak (a, b, f, g, mu, nu) -> uaweak (eval a ctx) (eval b ctx) (eval f ctx) (eval g ctx) (eval mu ctx) (eval nu ctx)
  | EN                           -> VN
  | EZero                        -> VZero
  | ESucc                        -> VSucc
  | ENInd e                      -> VNInd (eval e ctx)
  | EZ                           -> VZ
  | EPos                         -> VPos
  | ENeg                         -> VNeg
  | EZSucc                       -> VZSucc
  | EZPred                       -> VZPred
  | EZInd e                      -> VZInd (eval e ctx)
  | ES1                          -> VS1
  | EBase                        -> VBase
  | ELoop                        -> VLoop
  | ES1Ind e                     -> VS1Ind (eval e ctx)
  | ER                           -> VR
  | Elem                         -> VElem
  | EGlue                        -> VGlue
  | ERInd e                      -> VRInd (eval e ctx)
  | EBot                         -> VBot
  | EBotRec e                    -> VBotRec (eval e ctx)

and trans = function
  | VTrans (p, q), r       -> trans (p, trans (q, r))
  | VIdp _, p | p, VIdp _  -> p
  | VRev p, VTrans (q, r)  -> if conv p q then r else VTrans (VRev p, VTrans (q, r))
  | p, VTrans (VRev q, r)  -> if conv p q then r else VTrans (p, VTrans (VRev q, r))
  | VRev p, q              -> if conv p q then let (_, _, v) = extPath (inferV p) in VIdp v else VTrans (VRev p, q)
  | p, VRev q              -> if conv p q then let (_, v, _) = extPath (inferV p) in VIdp v else VTrans (p, VRev q)
  | VUAWeak (a, b, f1, g1, mu1, nu1), VUAWeak (_, c, f2, g2, mu2, nu2) ->

    let f = VLam (a, (freshName "x", fun x -> app (f2, app (f1, x)))) in
    let g = VLam (c, (freshName "x", fun x -> app (g1, app (g2, x)))) in

    let mu = VLam (a, (freshName "x", fun x ->
      trans (ap b (fun y -> app (g1, y))
        (app (g2, app (f2, app (f1, x)))) (app (f1, x))
        (app (mu2, app (f1, x))), app (mu1, x)))) in

    let nu = VLam (c, (freshName "x", fun x ->
      trans (ap b (fun y -> app (f2, y))
          (app (f1, (app (g1, (app (g2, x)))))) (app (g2, x))
          (app (nu1, app (g2, x))), app (nu2, x)))) in

    VUAWeak (a, c, f, g, mu, nu)
  | VSigProd (p1, g, u, _, q1), VSigProd (p2, _, _, w, q2) ->
    let (t, x, y) = extPath (inferV q1) in let i = freshName "x" in
    let q = trans (congr t x y i (coe (apd g p2) (Var (i, t))) q1, q2) in

    sigProd (trans (p1, p2)) g u w q
  | p, q -> VTrans (p, q)

and rev : value -> value = function
  | VUAWeak (a, b, f, g, mu, nu) -> VUAWeak (b, a, g, f, nu, mu)
(*  | VSigProd (p, g, u, v, q) ->
    let (t1, a, b) = extPath (inferV p) in
    let (t2, x, y) = extPath (inferV q) in

    let w1 = freshName "ω" in let w2 = freshName "ω" in let ts' = singl t1 a in
    let ts = VLam (t1, (freshName "x", fun x -> VPath (t1, a, x))) in
    let w2' = Var (w2, ts') in let p' = rev p in

    let q1 = congr t2 x y w1 (coe (rev (apd g p)) (Var (w1, t2))) q in
    let q2 = congr ts' (VSigMk (ts, a, VIdp a)) (VSigMk (ts, b, p)) w2
      (coe (apd g (VRev (VSnd w2'))) (coe (apd g (VSnd w2')) u)) (meet t1 a p) in

    sigProd p' g v u (trans (rev q1, rev q2))*)

  | VRev p        -> p
  | VIdp v        -> VIdp v
  | VTrans (p, q) -> trans (rev q, rev p)
  | v             -> VRev v

and coe p x = match p, x with
  (* coe (idp α) x ~> x *)
  | VIdp _, _ -> x
  (* coe (p ⬝ q) x ~> coe q (coe p x) *)
  | VTrans (q, p), _ -> coe p (coe q x)
  (* coe (ua-weak a b f g α β) x ~> f x *)
  | VUAWeak (_, _, f, _, _, _), _ -> app (f, x)
  | VRev (VApd (VLam (t, (x, f)), q)), v ->
    let g = f (Var (x, t)) in
    let (_, a, b) = extPath (inferV q) in
    begin match g with
      | VPath _ | VPi _ | VSig _ ->
        transport (rev q) t b a x g v
      | _ -> VCoe (p, v)
    end
  | VApd (VLam (t, (x, f)), q), v ->
    let (_, a, b) = extPath (inferV q) in
    transport q t a b x (f (Var (x, t))) v
  | _, _ -> VCoe (p, x)

and meet t a p = sigProd p (VLam (t, (freshName "x", fun x -> VPath (t, a, x)))) (VIdp a) p (VIdp p)

and transport p t a b x g v = match p, g with
  | VIdp _, _ -> v
  | _, VPath (k, f, g) ->
    let k' x' = subst (Env.add x x' Env.empty) k in
    let f' x' = subst (Env.add x x' Env.empty) f in
    let g' x' = subst (Env.add x x' Env.empty) g in

    let p1 = congr t a b x f p in let p3 = congr t a b x g p in
    let p2 = ap (k' a) (transport p t a b x k) (f' a) (g' a) v in
    trans (rev p1, trans (p2, p3))

  | _, VPi (k, (_, f)) ->
    let k' x' = subst (Env.add x x' Env.empty) k in
    let f' x' = subst (Env.add x x' Env.empty) << f in

    let ts' = singl t b in let ts = VLam (t, (freshName "x", fun x -> VPath (t, b, x))) in
    let y1 = freshName "y" in let y2 = freshName "y′" in let y3 = freshName "y″" in
    let y1' = Var (y1, ts') in let y2' = Var (y2, t) in let y3' = Var (y3, t) in

    VLam (k' b, (freshName "x", fun x ->
      transport (rev (meet t b (rev p))) ts'
        (VSigMk (ts, a, rev p)) (VSigMk (ts, b, VIdp b)) y1
        (f' (vfst y1') (transport (vsnd y1') t b y1' y2 (k' y2') x))
        (app (v, transport (rev p) t b a y3 (k' y3') x))))

  | _, VSig (k, (_, f)) ->
    let k' x' = subst (Env.add x x' Env.empty) k in
    let f' x' = subst (Env.add x x' Env.empty) << f in

    let ts' = singl t a in let ts = VLam (t, (freshName "x", fun x -> VPath (t, a, x))) in
    let y1 = freshName "y" in let y2 = freshName "y′" in
    let y1' = Var (y1, ts') in let y2' = Var (y2, t) in

    let fst = transport p t a b x k (vfst v) in

    let snd = transport (meet t a p) ts' (VSigMk (ts, a, VIdp a)) (VSigMk (ts, b, p)) y1
      (f' (vfst y1') (transport (vsnd y1') t a y1' y2 (k' y2') (vfst v))) (vsnd v) in

    VSigMk (VLam (k' b, (freshName "x", f' b)), fst, snd)
  | _, _ -> let r = congr t a b x g p in
    if isCoeNeut r then VCoe (r, v) else coe r v

and closByVal ctx p t e v = traceClos e p v;
  (* dirty hack to handle free variables introduced by type checker *)
  let ctx' = match v with
  | Var (x, t) -> if Env.mem x ctx then ctx else upLocal ctx x t v
  | _          -> ctx in
  eval e (upLocal ctx' p t v)

and congr t a b x g p =
(* apd id p ~> p *)
  if convVar x g then p
  (* apd (λ _, x) p ~> idp x *)
  else if not (mem x g) then VIdp g
  else match g, p with
  (* apd f (idp x) ~> idp (f x) *)
  | _, VIdp x' -> VIdp (subst (Env.add x x' Env.empty) g)

  (* apd f p⁻¹ ~> (apd f p)⁻¹ *)
  | _, VRev p -> let k x' = inferV (subst (Env.add x x' Env.empty) g) in
    let x1 = freshName "y" in let x2 = freshName "y′" in

    let ts' = singl t b in let ts = VLam (t, (freshName "x", fun x -> VPath (t, b, x))) in

    let x1' = Var (x1, ts') in let x2' = Var (x2, t) in

    rev (congr ts' (VSigMk (ts, b, VIdp b)) (VSigMk (ts, a, p)) x1
      (transport (rev (vsnd x1')) t (vfst x1') b x2 (k x2')
        (subst (Env.add x (vfst x1') Env.empty) g)) (meet t b p))

  (* apd f (p ⬝ q) ~> apd f p ⬝ apd f q *)
  | _, VTrans (p, q) ->
    let (_, a, b) = extPath (inferV p) in let (_, _, c) = extPath (inferV q) in
    let g' x' = subst (Env.add x x' Env.empty) g in let k = inferV << g' in

    let x1 = freshName "y" in let x2 = freshName "y′" in let x3 = freshName "y″" in let x4 = freshName "y‴" in
    let x1' = Var (x1, t) in let x2' = Var (x2, t) in let x3' = Var (x3, t) in let x4' = Var (x4, t) in

    let p1 = congr t a b x1 (g' x1') p in
    let p2 = congr (k b) (transport p t a b x2 (k x2') (g' a)) (g' b) x1
      (transport q t b c x3 (k x3') x1') p1 in
    let p3 = congr t b c x4 (g' x4') q in

    trans (p2, p3)

  (* apd f (apd g p) ~> apd (f ∘ g) p *)
  | _, VApd (h, p) ->
    let g' x' = subst (Env.add x x' Env.empty) g in
    let (_, (_, k)) = extPi (inferV h) in
    let (t, a, b) = extPath (inferV p) in

    let ts' = singl t b in let ts = VLam (t, (freshName "x", fun x -> VPath (t, b, x))) in
    let w = freshName "ω" in let w' = Var (w, ts') in
    let y = freshName "y" in let y' = Var (y, t) in

    congr ts' (VSigMk (ts, a, rev p)) (VSigMk (ts, b, VIdp b)) w
      (g' (transport (rev (vsnd w')) t (vfst w') b y (k y') (app (h, vfst w'))))
      (rev (meet t b (rev p)))

  | VApp (VApp (VApp (VS1Ind k, b), l), z), VLoop ->
    if convVar x z && not (mem x k || mem x b || mem x l) then l
    else VApd (VLam (t, (x, fun x' -> subst (Env.add x x' Env.empty) g)), p)

  | VApp (VApp (VApp (VRInd k, cz), sz), z), VApp (VGlue, z') ->
    if convVar x z && not (mem x k || mem x cz || mem x sz) then app (sz, z')
    else VApd (VLam (t, (x, fun x' -> subst (Env.add x x' Env.empty) g)), p)

  | _, VSigProd (r, _, _, _, _) when checkDecom x g ->
    let (t, a, b) = extPath (inferV r) in congr t a b x (decom x g) r

  | _, _ -> VApd (VLam (t, (x, fun x' -> subst (Env.add x x' Env.empty) g)), p)

and ap t f a b p = let x = freshName "x" in
  congr t a b x (f (Var (x, t))) p

and apd f p = let (t, a, b) = extPath (inferV p) in
  let x = freshName "x" in congr t a b x (app (f, Var (x, t))) p

and sigProd p g u v q = match p with
  | VIdp x -> apd (VLam (app (g, x), (freshName "η", fun y -> VSigMk (g, x, y)))) q
  | _      -> VSigProd (p, g, u, v, q)

and uaweak a b f g mu nu =
  match f, g, mu, nu with
  | VLam (_, (x, f')), VLam (_, (y, g')),
    VLam (_, (n, mu')), VLam (_, (m, nu')) ->
    let v = Var (n, a) in let w = Var (m, b) in

    (* ua-weak (idfun A) (idfun A) idp idp ~> idp A *)
    if convVar x (f' (Var (x, a))) &&
       convVar y (g' (Var (y, b))) &&
       conv (VIdp v) (mu' v) && conv (VIdp w) (nu' w)
    then VIdp a else VUAWeak (a, b, f, g, mu, nu)
  | _ -> VUAWeak (a, b, f, g, mu, nu)

and app (f, x) = match f, x with
  (* (λ (x : t), f) v ~> f[x/v] *)
  | VLam (_, (_, f)), v -> f v
  (* N-ind A z s zero ~> z *)
  | VApp (VApp (VNInd _, z), _), VZero -> z

  (* N-ind A z s (succ n) ~> s (N-ind A z s n) *)
  | VApp (VApp (VNInd _, _), s), VApp (VSucc, n) -> app (app (s, n), app (f, n))
  (* Z-ind A p n (pos x) ~> p x *)
  | VApp (VApp (VZInd _, p), _), VApp (VPos, x) -> app (p, x)
  (* Z-ind A p n (neg x) ~> n x *)
  | VApp (VApp (VZInd _, _), n), VApp (VNeg, x) -> app (n, x)

  (* Z-succ (neg (succ n)) ~> neg n *)
  | VZSucc, VApp (VNeg, VApp (VSucc, n)) -> negv n
  (* Z-succ (neg zero) ~> pos zero *)
  | VZSucc, VApp (VNeg, VZero) -> posv VZero
  (* Z-succ (pos n) ~> pos (succ n) *)
  | VZSucc, VApp (VPos, n) -> posv (succv n)
  (* Z-pred (neg n) ~> neg (succ n) *)
  | VZPred, VApp (VNeg, n) -> negv (succv n)
  (* Z-pred (pos zero) ~> neg zero *)
  | VZPred, VApp (VPos, VZero) -> negv VZero
  (* Z-pred (pos (succ n)) ~> pos n *)
  | VZPred, VApp (VPos, VApp (VSucc, n)) -> posv n
  (* Z-succ (Z-pred z) ~> z *)
  | VZSucc, VApp (VZPred, z) -> z
  (* Z-pred (Z-succ z) ~> z *)
  | VZPred, VApp (VZSucc, z) -> z

  (* S¹-ind β b ℓ base ~> b *)
  | VApp (VApp (VS1Ind _, b), _), VBase -> b

  (* R-ind β cz sz (elem z) ~> cz z *)
  | VApp (VApp (VRInd _, cz), _), VApp (VElem, z) -> app (cz, z)

  | _, _ -> VApp (f, x)

and app2 f x y = app (app (f, x), y)

and getRho ctx x = match Env.find_opt x ctx with
  | Some (_, _, Value v) -> v
  | Some (_, _, Exp e)   -> eval e ctx
  | None                 -> raise (VariableNotFound x)

(* This is part of evaluator, not type checker *)
and inferV v = traceInferV v; match v with
  | Var (_, t) -> t
  | VLam (t, (x, f)) -> VPi (t, (x, fun x -> inferV (f x)))
  | VPi (t, (x, f)) | VSig (t, (x, f)) -> imax (inferV t) (inferV (f (Var (x, t))))
  | VFst e -> inferFst (inferV e)
  | VSnd e -> inferSnd (vfst e) (inferV e)
  | VCoe (p, _) -> let (_, _, t) = extPath (inferV p) in t
  | VApd (f, p) -> inferVApd f p (inferV p) (inferV f)
  | VSigMk (g, _, _) -> let (t, (x, _)) = extPi (inferV g) in VSig (t, (x, fun x -> app (g, x)))
  | VSigProd (p, g, u, v, _) -> let (t, a, b) = extPath (inferV p) in inferSigProd t g a b u v
  | VId t -> let n = extSet (inferV t) in implv t (implv t (VPre n))
  | VJ t -> inferJ (inferV t)
  | VApp (f, x) -> let (_, (_, g)) = extPi (inferV f) in g x
  | VRefl v -> idv (inferV v) v v
  | VIdp v -> VPath (inferV v, v, v)
  | VRev p -> let (v, a, b) = extPath (inferV p) in VPath (v, b, a)
  | VTrans (p, q) -> let (t, a, _) = extPath (inferV p) in let (_, _, c) = extPath (inferV q) in VPath (t, a, c)
  | VPre n -> VPre (Z.succ n)
  | VKan n -> VKan (Z.succ n)
  | VPath (v, _, _) -> inferV v
  | VUAWeak (a, b, _, _, _, _) -> VPath (inferV a, a, b)
  | VN -> VKan Z.zero | VZero -> VN | VSucc -> implv VN VN
  | VNInd v -> inferNInd v
  | VZ -> VKan Z.zero | VPos -> implv VN VZ | VNeg -> implv VN VZ
  | VZSucc -> implv VZ VZ | VZPred -> implv VZ VZ | VZInd v -> inferZInd v
  | VS1 -> VKan Z.zero | VBase -> VS1 | VLoop -> VPath (VS1, VBase, VBase) | VS1Ind v -> inferS1Ind v
  | VR -> VKan Z.zero | VElem -> implv VZ VR | VGlue -> inferGlue () | VRInd v -> inferRInd v
  | VBot -> VKan Z.zero | VBotRec v -> implv VBot v
  | VHole -> raise (InferVError v)

and inferSigProd t g a b u v = let x = freshName "x" in
  VPath (VSig (t, (x, fun x -> app (g, x))), VSigMk (g, a, u), VSigMk (g, b, v))

and inferJ v = let n = extSet v in
  let x = freshName "x" in let y = freshName "y" in
  let pi = freshName "P" in let p = freshName "p" in

  let t = VPi (v, (x, fun x ->
    VPi (v, (y, fun y -> implv (idv v x y) (VPre n))))) in

  VPi (t, (pi, fun pi ->
    VPi (v, (x, fun x ->
      implv (app (app (app (pi, x), x), VRefl x))
            (VPi (v, (y, fun y ->
              VPi (idv v x y, (p, fun p ->
                app (app (app (pi, x), y), p))))))))))

and inferVApd f p t1 t2 =
  let (t, a, b) = extPath t1 in let (_, (_, g)) = extPi t2 in
  VPath (g b, coe (apd (VLam (t, (freshName "x", g))) p) (app (f, a)), app (f, b))

and inferNInd v =
  let e = fun x -> app (v, x) in
  implv (e VZero)
    (implv (VPi (VN, (freshName "n", fun n -> implv (e n) (e (succv n)))))
           (VPi (VN, (freshName "n", e))))

and inferZInd v =
  let e = fun x -> app (v, x) in
  implv (VPi (VN, (freshName "n", e << posv)))
    (implv (VPi (VN, (freshName "n", e << negv)))
      (VPi (VZ, (freshName "z", e))))

and inferS1Ind v =
  let e = fun x -> app (v, x) in
  VPi (e VBase, (freshName "b", fun b ->
    implv (VPath (e VBase, coe (ap VS1 e VBase VBase VLoop) b, b))
          (VPi (VS1, (freshName "x", e)))))

and zsuccv z = app (VZSucc, z)

and inferGlue () =
  let z = freshName "z" in
  VPi (VZ, (z, fun z -> VPath (VR, elemv z, elemv (zsuccv z))))

and inferRInd v =
  let e = fun x -> app (v, x) in
  let cz = freshName "cz" in
  VPi (VPi (VZ, (freshName "z", e << elemv)), (cz, fun cz ->
    implv (VPi (VZ, (freshName "z", fun z ->
      VPath (e (elemv (zsuccv z)), coe (apd (VLam (VR, (freshName "x", e))) (VApp (VGlue, z)))
                                       (app (cz, z)), app (cz, zsuccv z)))))
      (VPi (VR, (freshName "z", e)))))

and inferFst = function
  | VSig (t, _) -> t
  | v           -> raise (ExpectedSig v)

and inferSnd v = function
  | VSig (_, (_, g)) -> g v
  | u                -> raise (ExpectedSig u)

(* Convertibility *)
and conv v1 v2 : bool = traceConv v1 v2;
  v1 == v2 || begin match v1, v2 with
    | VKan u, VKan v -> ieq u v
    | VSigMk (g1, a1, b1), VSigMk (g2, a2, b2) -> conv g1 g2 && conv a1 a2 && conv b1 b2
    | VSigMk (_, a, b), v | v, VSigMk (_, a, b) -> conv (vfst v) a && conv (vsnd v) b
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
    | VCoe (p1, x1), VCoe (p2, x2) -> conv p1 p2 && conv x1 x2
    | VApd (f1, p1), VApd (f2, p2) -> conv f1 f2 && conv p1 p2
    | VSigProd (p1, b1, u1, v1, q1), VSigProd (p2, b2, u2, v2, q2) ->
      conv p1 p2 && conv b1 b2 && conv u1 u2 && conv v1 v2 && conv q1 q2
    | VUAWeak (a1, b1, f1, g1, mu1, nu1), VUAWeak (a2, b2, f2, g2, mu2, nu2) ->
      conv a1 a2 && conv b1 b2 && conv f1 f2 && conv g1 g2 && conv mu1 mu2 && conv nu1 nu2
    | VN, VN -> true
    | VZero, VZero -> true
    | VSucc, VSucc -> true
    | VNInd u, VNInd v -> conv u v
    | VZ, VZ -> true
    | VPos, VPos -> true
    | VNeg, VNeg -> true
    | VZSucc, VZSucc -> true
    | VZPred, VZPred -> true
    | VZInd u, VZInd v -> conv u v
    | VS1, VS1 -> true
    | VBase, VBase -> true
    | VLoop, VLoop -> true
    | VS1Ind u, VS1Ind v -> conv u v
    | VR, VR -> true
    | VElem, VElem -> true
    | VGlue, VGlue -> true
    | VRInd u, VRInd v -> conv u v
    | VBot, VBot -> true
    | VBotRec u, VBotRec v -> conv u v
    | _, _ -> false
  end || convProofIrrel v1 v2

and convProofIrrel v1 v2 =
  (* Id A a b is proof-irrelevant *)
  try let t1 = inferV v1 in let t2 = inferV v2 in
    if isProofIrrel t1 && isProofIrrel t2
    then conv t1 t2 else false
  with InferVError _ -> false

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
    let x = Var (p, t) in let ctx' = upLocal ctx p t x in check ctx' b (g x)
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
  | ECoe (p, x), t2 ->
    let t1 = infer ctx x in let u1 = inferV t1 in let u2 = inferV t2 in
    eqNf u1 u2; ignore (extKan (inferV t1));
    check ctx p (VPath (u1, t1, t2))
  | e, t -> eqNf (infer ctx e) t
  with ex -> Printf.printf "When trying to typecheck\n  %s\nAgainst type\n  %s\n" (showExp e0) (showValue t0); raise ex

and infer ctx e : value = traceInfer e; try match e with
  | EVar x -> lookup x ctx
  | EKan u -> VKan (Z.succ u)
  | ESig (a, (p, b)) | EPi (a, (p, b)) -> inferTele ctx p a b
  | ELam (a, (p, b)) -> inferLam ctx p a b
  | EPair (a, b) -> let t1 = infer ctx a in let t2 = infer ctx b in
    VSig (t1, (Irrefutable, fun _ -> t2))
  | ESigMk (g, a, b) -> let (t, (x, f)) = extPi (infer ctx g) in
    ignore (extSet (f (Var (x, t)))); check ctx a t; let g' = eval g ctx in
    check ctx b (app (g', eval a ctx)); VSig (t, (fresh x, fun x -> app (g', x)))
  | EApp (f, x) -> begin match infer ctx f with
    | VPi (t, (_, g)) -> check ctx x t; g (eval x ctx)
    | v -> raise (ExpectedPi v)
  end
  | EFst e -> inferFst (infer ctx e)
  | ESnd e -> inferSnd (vfst (eval e ctx)) (infer ctx e)
  | EPre u -> VPre (Z.succ u)
  | EPath (e, a, b) -> let t = eval e ctx in check ctx a t; check ctx b t; infer ctx e
  | EId e -> let v = eval e ctx in let n = extSet (infer ctx e) in implv v (implv v (VPre n))
  | ERefl e -> let v = eval e ctx in idv (infer ctx e) v v
  | EJ e -> inferJ (infer ctx e)
  | EIdp e -> let v = eval e ctx in let t = infer ctx e in VPath (t, v, v)
  | ERev p -> let (v, a, b) = extPath (infer ctx p) in VPath (v, b, a)
  | ETrans (p, q) ->
    let (u, a, x) = extPath (infer ctx p) in
    let (v, y, c) = extPath (infer ctx q) in
    eqNf u v; eqNf x y; VPath (u, a, c)
  | ECoe (p, x) -> let (e, a, b) = extPath (infer ctx p) in ignore (extKan e); check ctx x a; b
  | EApd (f, p) -> inferApd ctx f p
  | ESigProd (p, g, u, v, q) -> let (t, a, b) = extPath (infer ctx p) in
    let (t', (x, f)) = extPi (infer ctx g) in
    eqNf t t'; ignore (extKan (f (Var (x, t))));
    let u' = eval u ctx in let v' = eval v ctx in let g' = eval g ctx in
    let t1 = app (g', a) in let t2 = app (g', b) in
    check ctx u t1; check ctx v t2;
    check ctx q (VPath (t2, coe (apd g' (eval p ctx)) u', v'));
    inferSigProd t g' a b u' v'
  | EUAWeak (a, b, f, g, mu, nu) -> inferUAWeak ctx a b f g mu nu
  | EN -> VKan Z.zero | EZero -> VN | ESucc -> implv VN VN
  | ENInd e -> inferInd false ctx VN e inferNInd
  | EZ -> VKan Z.zero | EPos -> implv VN VZ | ENeg -> implv VN VZ
  | EZSucc -> implv VZ VZ | EZPred -> implv VZ VZ
  | EZInd e -> inferInd false ctx VZ e inferZInd
  | ES1 -> VKan Z.zero | EBase -> VS1 | ELoop -> VPath (VS1, VBase, VBase)
  | ES1Ind e -> inferInd true ctx VS1 e inferS1Ind
  | ER -> VKan Z.zero | Elem -> implv VZ VR | EGlue -> inferGlue ()
  | ERInd e -> inferInd true ctx VR e inferRInd
  | EBot -> VKan Z.zero | EBotRec e -> ignore (extSet (infer ctx e)); implv VBot (eval e ctx)
  | EHole -> raise (InferError e)
  with ex -> Printf.printf "When trying to infer type of\n  %s\n" (showExp e); raise ex

and inferInd fibrant ctx t e f =
  let (t', (p, g)) = extPi (infer ctx e) in eqNf t t'; let k = g (Var (p, t)) in
  ignore (if fibrant then extKan k else extSet k); f (eval e ctx)

and inferTele ctx p a b =
  ignore (extSet (infer ctx a));
  let t = eval a ctx in let x = Var (p, t) in
  let ctx' = upLocal ctx p t x in
  let v = infer ctx' b in imax (infer ctx a) v

and inferLam ctx p a e =
  ignore (extSet (infer ctx a)); let t = eval a ctx in
  ignore (infer (upLocal ctx p t (Var (p, t))) e);
  VPi (t, (p, fun x -> infer (upLocal ctx p t x) e))

and inferApd ctx f p =
  let t1 = infer ctx p in let t2 = infer ctx f in
  let (t, _, _) = extPath t1 in let (t', (x, g')) = extPi t2 in

  eqNf t t'; ignore (extKan (inferV (g' (Var (x, t')))));
  inferVApd (eval f ctx) (eval p ctx) t1 t2

and inferUAWeak ctx a b f g mu nu =
  let t = infer ctx a in let t' = infer ctx b in eqNf t t';
  let a' = eval a ctx in let b' = eval b ctx in
  check ctx f (implv a' b'); check ctx g (implv b' a');

  let f' = eval f ctx in let g' = eval g ctx in

  check ctx mu (VPi (a', (freshName "x", fun x ->
    VPath (a', app (g', app (f', x)), x))));
  check ctx nu (VPi (b', (freshName "x", fun x ->
    VPath (b', app (f', app (g', x)), x))));

  VPath (t, a', b')

and mem x = function
  | Var (y, _) -> x = y
  | VSig (t, (p, f)) | VPi (t, (p, f)) | VLam (t, (p, f)) ->
    mem x t || mem x (f (Var (p, t)))
  | VBot   | VKan _ | VPre _
  | VS1    | VBase  | VLoop
  | VR     | VElem  | VGlue
  | VN     | VZero  | VSucc
  | VZ     | VPos   | VNeg
  | VZSucc | VZPred | VHole -> false

  | VFst e    | VSnd e    | VId e   | VRefl e
  | VJ e      | VIdp e    | VRev e  | VNInd e
  | VZInd e   | VS1Ind e  | VRInd e | VBotRec e -> mem x e

  | VApp (a, b) | VCoe (a, b) | VApd (a, b) | VTrans (a, b) -> mem x a || mem x b

  | VSigMk (a, b, c) | VPath (a, b, c) -> mem x a || mem x b || mem x c
  | VSigProd (a, b, c, d, e) -> mem x a || mem x b || mem x c || mem x d || mem x e
  | VUAWeak (a, b, f, g, mu, nu) -> mem x a || mem x b || mem x f || mem x g || mem x mu || mem x nu

and mem2 x y v = mem x v || mem y v

and subst rho = function
  | VPre n                       -> VPre n
  | VKan n                       -> VKan n
  | VHole                        -> VHole
  | VApp (f, x)                  -> app (subst rho f, subst rho x)
  | VPi (t, (p, f))              -> VPi (subst rho t, (p, fun x -> subst rho (f x)))
  | VSig (t, (p, f))             -> VSig (subst rho t, (p, fun x -> subst rho (f x)))
  | VLam (t, (p, f))             -> VLam (subst rho t, (p, fun x -> subst rho (f x)))
  | VSigMk (g, a, b)             -> VSigMk (subst rho g, subst rho a, subst rho b)
  | VFst v                       -> vfst (subst rho v)
  | VSnd v                       -> vsnd (subst rho v)
  | VId v                        -> VId (subst rho v)
  | VRefl v                      -> VRefl (subst rho v)
  | VJ v                         -> VJ (subst rho v)
  | VPath (e, a, b)              -> VPath (subst rho e, subst rho a, subst rho b)
  | VIdp e                       -> VIdp (subst rho e)
  | VRev p                       -> rev (subst rho p)
  | VTrans (p, q)                -> trans (subst rho p, subst rho q)
  | VCoe (p, x)                  -> coe (subst rho p) (subst rho x)
  | VApd (f, p)                  -> apd (subst rho f) (subst rho p)
  | VSigProd (p, b, u, v, q)     -> sigProd (subst rho p) (subst rho b) (subst rho u) (subst rho v) (subst rho q)
  | VUAWeak (a, b, f, g, mu, nu) -> uaweak (subst rho a) (subst rho b) (subst rho f) (subst rho g) (subst rho mu) (subst rho nu)
  | VN                           -> VN
  | VZero                        -> VZero
  | VSucc                        -> VSucc
  | VNInd v                      -> VNInd (subst rho v)
  | VZ                           -> VZ
  | VPos                         -> VPos
  | VNeg                         -> VNeg
  | VZSucc                       -> VZSucc
  | VZPred                       -> VZPred
  | VZInd v                      -> VZInd (subst rho v)
  | VS1                          -> VS1
  | VBase                        -> VBase
  | VLoop                        -> VLoop
  | VS1Ind v                     -> VS1Ind (subst rho v)
  | VR                           -> VR
  | VElem                        -> VElem
  | VGlue                        -> VGlue
  | VRInd v                      -> VRInd (subst rho v)
  | VBot                         -> VBot
  | VBotRec v                    -> VBotRec (subst rho v)
  | Var (x, t)                   -> begin match Env.find_opt x rho with
    | Some v -> v
    | None   -> Var (x, t)
  end

and checkDecom x = function
  | VSnd (Var (y, _)) when x = y -> false
  | VPi (t, (p, f)) | VSig (t, (p, f)) | VLam (t, (p, f)) -> checkDecom x t && checkDecom x (f (Var (p, t)))
  | VId a   | VRefl a  | VJ a    | VIdp a  | VRev a | VNInd a
  | VZInd a | VS1Ind a | VRInd a | VFst a  | VSnd a -> checkDecom x a
  | VApp (a, b) | VTrans (a, b) | VCoe (a, b) | VApd (a, b) -> checkDecom x a && checkDecom x b
  | VSigMk (a, b, c) | VPath (a, b, c) -> checkDecom x a && checkDecom x b && checkDecom x c
  | VSigProd (a, b, c, d, e) -> checkDecom x a && checkDecom x b && checkDecom x c && checkDecom x d && checkDecom x e
  | VUAWeak (a, b, c, d, e, f) -> checkDecom x a && checkDecom x b && checkDecom x c && checkDecom x d && checkDecom x e && checkDecom x f
  | _ -> true

and decom x = function
  | VFst (Var (y, VSig (t, _))) when x = y -> Var (y, t)
  | VSnd (Var (y, _)) when x = y -> raise (Failure "decom failed")
  | VApp (f, y)                  -> VApp (decom x f, decom x y)
  | VPi (t, (p, f))              -> VPi (decom x t, (p, decom x << f))
  | VSig (t, (p, f))             -> VSig (decom x t, (p, decom x << f))
  | VLam (t, (p, f))             -> VLam (decom x t, (p, decom x << f))
  | VSigMk (g, a, b)             -> VSigMk (decom x g, decom x a, decom x b)
  | VFst v                       -> VFst (decom x v)
  | VSnd v                       -> VSnd (decom x v)
  | VId v                        -> VId (decom x v)
  | VRefl v                      -> VRefl (decom x v)
  | VJ v                         -> VJ (decom x v)
  | VPath (e, a, b)              -> VPath (decom x e, decom x a, decom x b)
  | VIdp e                       -> VIdp (decom x e)
  | VRev p                       -> VRev (decom x p)
  | VTrans (p, q)                -> VTrans (decom x p, decom x q)
  | VCoe (p, y)                  -> VCoe (decom x p, decom x y)
  | VApd (f, p)                  -> VApd (decom x f, decom x p)
  | VSigProd (p, b, u, v, q)     -> VSigProd (decom x p, decom x b, decom x u, decom x v, decom x q)
  | VUAWeak (a, b, f, g, mu, nu) -> VUAWeak (decom x a, decom x b, decom x f, decom x g, decom x mu, decom x nu)
  | VNInd v                      -> VNInd (decom x v)
  | VZInd v                      -> VZInd (decom x v)
  | VS1Ind v                     -> VS1Ind (decom x v)
  | VRInd v                      -> VRInd (decom x v)
  | v                            -> v

and singl t x = let y = freshName "y" in VSig (t, (y, fun y -> VPath (t, x, y)))
