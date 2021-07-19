%{ open Module
   open Ident
   open Elab
   open Expr

  let remSuffix suffix x =
    let n = String.length x in let m = String.length suffix in
    if m > n then None else begin
      let b = ref true in
      for i = 1 to m do
        b := !b && (suffix.[m - i] = x.[n - i])
      done;
      if !b then Some (String.sub x 0 (n - m)) else None
    end

  let rec getVar x =
    match remSuffix "⁻¹" x with
    | Some y -> ERev (getVar y)
    | None -> decl x

%}

%token <string> IDENT
%token <int> KAN
%token <int> PRE
%token LPARENS RPARENS
%token COMMA COLON IRREF EOF HOLE
%token DEFEQ PROD ARROW FST SND LAM DEF
%token MODULE WHERE IMPORT AXIOM
%token SIGMA PI OPTION
%token ID REFL IDJ
%token PATH IDP REV TRANS
%token BOUNDARY LEFT RIGHT SYMM

%right ARROW PROD
%left TRANS

%start <Module.file> file
%start <Module.command> repl

%%

ident : IRREF { Irrefutable } | IDENT { name $1 }
vars : ident+ { $1 }
lense : LPARENS vars COLON exp2 RPARENS { List.map (fun x -> (x, $4)) $2 }
telescope : lense telescope { List.append $1 $2 } | lense { $1 }
params : telescope { $1 } | { [] }
path : IDENT { getPath $1 }

file : MODULE IDENT WHERE line* EOF { ($2, $4) }
line : IMPORT path+ { Import $2 } | OPTION IDENT IDENT { Option ($2, $3) } | declarations { Decl $1 }
repl : COLON IDENT exp2 EOF { Command ($2, $3) } | COLON IDENT EOF { Action $2 } | exp2 EOF { Eval $1 } | EOF { Nope }

exp1 : exp2 COMMA exp1 { EPair ($1, $3) } | exp2 { $1 }

exp2:
  | LAM telescope COMMA exp2 { telescope eLam $4 $2 }
  | PI telescope COMMA exp2 { telescope ePi $4 $2 }
  | SIGMA telescope COMMA exp2 { telescope eSig $4 $2 }
  | exp3 { $1 }

exp3:
  | exp3 ARROW exp3 { impl $1 $3 }
  | exp3 PROD exp3 { prod $1 $3 }
  | exp4 { $1 }

exp4 :
  | exp4 exp6 { EApp ($1, $2) }
  | ID exp6 { EId $2 }
  | REFL exp6 { ERefl $2 }
  | IDJ exp6 { EJ $2 }
  | PATH exp6 { EPath $2 }
  | BOUNDARY exp6 { EBoundary $2 }
  | LEFT exp6 { ELeft $2 }
  | RIGHT exp6 { ERight $2 }
  | SYMM exp6 { ESymm $2 }
  | exp5 { $1 }

exp5:
  | IDP exp6 { EIdp $2 }
  | exp6 REV { ERev $1 }
  | exp5 TRANS exp5 { ETrans ($1, $3) }
  | exp6 { $1 }

exp6:
  | HOLE { EHole }
  | PRE { EPre $1 }
  | KAN { EKan $1 }
  | exp6 FST { EFst $1 }
  | exp6 SND { ESnd $1 }
  | LPARENS exp1 RPARENS { $2 }
  | IDENT { getVar $1 }

declarations:
  | DEF IDENT params COLON exp2 DEFEQ exp2 { Def ($2, Some (telescope ePi $5 $3), telescope eLam $7 $3) }
  | DEF IDENT params DEFEQ exp2 { Def ($2, None, telescope eLam $5 $3) }
  | AXIOM IDENT params COLON exp2 { Axiom ($2, telescope ePi $5 $3) }
