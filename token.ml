open Parser

let tokenToString : token -> string = function
  | IDENT s    -> Printf.sprintf "IDENT %s" s
  | PRE u      -> Printf.sprintf "PRE %d" u
  | KAN u      -> Printf.sprintf "KAN %d" u
  | DEF        -> "DEF"         | SIGMA      -> "SIGMA"
  | PI         -> "PI"          | HOLE       -> "HOLE"
  | RPARENS    -> "RPARENS"     | LPARENS    -> "LPARENS"
  | LAM        -> "LAM"         | PROD       -> "PROD"
  | OPTION     -> "OPTION"      | AXIOM      -> "AXIOM"
  | IRREF      -> "IRREF"       | EOF        -> "EOF"
  | FST        -> "FST"         | SND        -> "SND"
  | DEFEQ      -> "DEFEQ"       | COMMA      -> "COMMA"
  | COLON      -> "COLON"       | ARROW      -> "ARROW"
  | WHERE      -> "WHERE"       | MODULE     -> "MODULE"
  | PATH       -> "PATH"        | IDP        -> "IDP"
  | REV        -> "REV"         | TRANS      -> "TRANS"
  | LEFT       -> "LEFT"        | RIGHT      -> "RIGHT"
  | BOUNDARY   -> "BOUNDARY"    | SYMM       -> "SYMM"
  | BLEFT      -> "BLEFT"       | BRIGHT     -> "BRIGHT"
  | COMP       -> "COMP"        | BCONG      -> "BCONG"
  | MEET       -> "MEET"        | COE        -> "COE"
  | CONG       -> "CONG"        | ID         -> "ID"
  | REFL       -> "REFL"        | IDJ        -> "IDJ"
  | IMPORT     -> "IMPORT"