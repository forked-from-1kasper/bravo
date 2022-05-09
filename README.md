Castle Bravo
===============

[![Actions](https://github.com/forked-from-1kasper/bravo/workflows/OCaml/badge.svg)](https://github.com/forked-from-1kasper/bravo/actions)

```OCaml
type exp =
  | EPre of Z.t | EKan of Z.t                                                 (* cosmos *)
  | EVar of name | EHole                                                   (* variables *)
  | EPi of exp * (name * exp) | ELam of exp * (name * exp) | EApp of exp * exp     (* Π *)
  | ESig of exp * (name * exp) | EPair of exp * exp | ESigMk of exp * exp * exp    (* Σ *)
  | EFst of exp | ESnd of exp | ESigProd of exp * exp * exp * exp * exp            (* Σ *)
  | EPath of exp * exp * exp | EIdp of exp | ERev of exp | ETrans of exp * exp  (* path *)
  | ECoe of exp * exp | EApd of exp * exp                             (* Kan operations *)
  | EUAWeak of exp * exp * exp * exp * exp * exp                          (* univalence *)
  | EN | EZero | ESucc | ENInd of exp                                              (* N *)
  | EZ | EPos | ENeg | EZInd of exp | EZSucc | EZPred                              (* Z *)
  | ES1 | EBase | ELoop | ES1Ind of exp                                           (* S¹ *)
  | ER | Elem | EGlue | ERInd of exp                                               (* R *)
  | EBot | EBotRec of exp                                                          (* ⊥ *)
  | EId of exp | ERefl of exp | EJ of exp                            (* strict equality *)
```
