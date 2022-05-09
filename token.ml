open Parser

let tokenToString : token -> string = function
  | IDENT s    -> Printf.sprintf "IDENT %s" s
  | PRE u      -> Printf.sprintf "PRE %s" (Z.to_string u)
  | KAN u      -> Printf.sprintf "KAN %s" (Z.to_string u)
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
  | COE        -> "COE"         | APD        -> "APD"
  | REFL       -> "REFL"        | IDJ        -> "IDJ"
  | IMPORT     -> "IMPORT"      | UAWEAK     -> "UAWEAK"
  | NIND       -> "NIND"        | ZIND       -> "ZIND"
  | S1IND      -> "S1IND"       | RIND       -> "RIND"
  | BOTREC     -> "BOTREC"      | ID         -> "ID"
  | SIGMK      -> "SIGMK"       | SIGPROD    -> "SIGPROD"