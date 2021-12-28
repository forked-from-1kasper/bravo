{
  open Parser
  open Lexing

  let nextLine lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = pos.pos_cnum;
                 pos_lnum = pos.pos_lnum + 1 }

  let ten = Z.of_int 10

  let getLevel s =
    let res = ref Z.zero in let queue = Queue.of_seq (String.to_seq s) in
    let sym = Queue.take queue in if (sym <> 'U' && sym <> 'V') then
      failwith "invalid universe";

    while not (Queue.is_empty queue) do
      if (Queue.take queue <> '\xE2' ||
          Queue.take queue <> '\x82')
      then failwith "invalid universe level while lexing";

      let value = Char.code (Queue.take queue) - 0x80 in
      res := Z.add (Z.mul !res ten) (Z.of_int value)
    done; !res
}

let lat1   = [^ '\t' ' ' '\r' '\n' '(' ')' ':' '.' ',']
let beg    = lat1 # '-'
let bytes2 = ['\192'-'\223']['\128'-'\191']
let bytes3 = ['\224'-'\239']['\128'-'\191']['\128'-'\191']
let bytes4 = ['\240'-'\247']['\128'-'\191']['\128'-'\191']['\128'-'\191']

let nl               = "\r\n"|"\r"|"\n"
let inlineComment    = "--" [^ '\n' '\r']* (nl|eof)
let multilineComment = "{-" [^ '-']* '-' ([^ '-' '}'][^ '-']* '-' | '-')* '}'
let comment          = inlineComment | multilineComment

let utf8    = lat1|bytes2|bytes3|bytes4
let ident   = beg utf8*
let ws      = ['\t' ' ']
let colon   = ':'
let defeq   = ":="     | "\xE2\x89\x94" | "\xE2\x89\x9C" | "\xE2\x89\x9D" (* ≔ | ≜ | ≝ *)
let arrow   = "->"     | "\xE2\x86\x92" (* → *)
let prod    = "*"      | "\xC3\x97"     (* × *)
let lam     = "\\"     | "\xCE\xBB"     (* λ *)
let pi      = "forall" | "\xCE\xA0"     (* Π *)
let sigma   = "sigma"  | "\xCE\xA3"     (* Σ *)
let def     = "definition" | "def" | "theorem" | "lemma" | "corollary" | "proposition"
let axiom   = "axiom"|"postulate"

let rev      = "\xE2\x81\xBB\xC2\xB9" (*  ⁻¹ *)
let trans    = "\xE2\xAC\x9D"         (*  ⬝  *)

let equiv    = "\xE2\x89\x83"         (*  ≃  *)

let boundary = "\xE2\x88\x82"         (*  ∂  *)
let symm     = boundary "-symm"
let comp     = boundary "-comp"
let bleft    = boundary "-left"
let bright   = boundary "-right"
let bapd     = boundary "-apd"

let subscript = '\xE2' '\x82' ['\x80'-'\x89']
let kan       = 'U' subscript*
let pre       = 'V' subscript*

let nind  = "N-ind"
let zind  = "Z-ind"
let s1ind = "S\xC2\xB9-ind"
let rind  = "R-ind"

let strict = "^s" | "\xCB\xA2" (* ˢ *)
let s1inds = s1ind strict
let rinds  = rind strict

let bot    = "_|_" | "\xE2\x8A\xA5" (* ⊥ *)
let botrec = bot "-rec"

rule main = parse
| nl         { nextLine lexbuf; main lexbuf }
| comment    { nextLine lexbuf; main lexbuf }
| ws+        { main lexbuf }
| "module"   { MODULE }      | "where"    { WHERE }
| "import"   { IMPORT }      | "option"   { OPTION }
| def        { DEF }         | colon      { COLON }
| ','        { COMMA }       | '_'        { IRREF }
| '('        { LPARENS }     | ')'        { RPARENS }
| ".1"       { FST }         | ".2"       { SND }
| pi         { PI }          | sigma      { SIGMA }
| axiom      { AXIOM }       | defeq      { DEFEQ }
| lam        { LAM }         | arrow      { ARROW }
| prod       { PROD }        | kan as s   { KAN (getLevel s) }
| "Path"     { PATH }        | "Id"       { ID }
| "refl"     { REFL }        | "idJ"      { IDJ }
| rev        { REV }         | trans      { TRANS }
| "idp"      { IDP }         | pre as s   { PRE (getLevel s) }
| "?"        { HOLE }        | boundary   { BOUNDARY }
| "left"     { LEFT }        | "right"    { RIGHT }
| "meet"     { MEET }        | "coe"      { COE }
| "apd"      { APD }         | symm       { SYMM }
| bleft      { BLEFT }       | bright     { BRIGHT }
| bapd       { BAPD }        | comp       { COMP }
| "ua"       { UA }          | equiv      { EQUIV }
| nind       { NIND }        | zind       { ZIND }
| s1ind      { S1IND }       | s1inds     { S1INDS }
| rind       { RIND }        | rinds      { RINDS }
| botrec     { BOTREC }      | "mkeqv"    { MKEQV }
| ident as s { IDENT s }     | eof        { EOF }
