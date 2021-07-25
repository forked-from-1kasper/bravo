open Ident
open Expr

exception Restart
exception InferError of exp
exception ExpectedPi of value
exception ExpectedESet of exp
exception InferVError of value
exception ExpectedSig of value
exception ExpectedPath of value
exception ExpectedVSet of value
exception Ineq of value * value
exception ExpectedPair of value
exception ExpectedEquiv of value
exception Parser of int * string
exception UnknownOption of string
exception ExpectedFibrant of value
exception UnknownCommand of string
exception VariableNotFound of name
exception ExpectedBoundary of value
exception AlreadyDeclared of string
exception ExpectedNonDependent of value
exception InvalidModuleName of string * string
exception UnknownOptionValue of string * string

let prettyPrintError : exn -> unit = function
  | Ineq (u, v) -> Printf.printf "Type mismatch:\n  %s\nis not equal to\n  %s\n" (showValue u) (showValue v)
  | ExpectedNonDependent v -> Printf.printf "“%s” expected to be a non-dependent type.\n" (showValue v)
  | ExpectedBoundary v -> Printf.printf "“%s” expected to be a boundary.\n" (showValue v)
  | ExpectedPath v -> Printf.printf "“%s” expected to be a path.\n" (showValue v)
  | AlreadyDeclared p -> Printf.printf "“%s” is already declared.\n" p
  | InferVError v -> Printf.printf "Cannot infer type of\n  %s\n" (showValue v)
  | InferError e -> Printf.printf "Cannot infer type of\n  %s\n" (showExp e)
  | VariableNotFound p -> Printf.printf "Variable %s was not found\n" (showName p)
  | InvalidModuleName (name, filename) -> Printf.printf "Module “%s” does not match name of its file: %s\n" name filename
  | ExpectedESet x -> Printf.printf "  %s\nexpected to be universe\n" (showExp x)
  | ExpectedVSet x -> Printf.printf "  %s\nexpected to be universe\n" (showValue x)
  | ExpectedFibrant x -> Printf.printf "  %s\nexpected to be fibrant universe\n" (showValue x)
  | ExpectedPi x -> Printf.printf "  %s\nexpected to be Pi-type\n" (showValue x)
  | ExpectedSig x -> Printf.printf "  %s\nexpected to be Sigma-type\n" (showValue x)
  | ExpectedEquiv x -> Printf.printf "  %s\nexpected to be an equivalence\n" (showValue x)
  | ExpectedPair x -> Printf.printf "  %s\nexpected to be a pair\n" (showValue x)
  | UnknownCommand s -> Printf.printf "Unknown command “%s”\n" s
  | UnknownOption opt -> Printf.printf "Unknown option “%s”\n" opt
  | UnknownOptionValue (opt, value) -> Printf.printf "Unknown value “%s” of option “%s”\n" value opt
  | Parser (x, buf) -> Printf.printf "Parsing error at line %d: “%s”\n" x buf
  | Sys_error s -> print_endline s
  | Restart -> raise Restart
  | ex -> Printf.printf "Uncaught exception: %s\n" (Printexc.to_string ex)

let handleErrors (f : 'a -> 'b) (x : 'a) (default : 'b) : 'b =
  try f x with ex -> prettyPrintError ex; default