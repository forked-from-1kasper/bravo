Castle Bravo
===============

[![Actions](https://github.com/groupoid/castle.bravo/workflows/OCaml/badge.svg)](https://github.com/groupoid/castle.bravo/actions)

Experimental Implementation of HoTT-∂ Type System.

```OCaml
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
```

