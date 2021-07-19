FLAGS = -use-menhir -yaccflag "--explain" -ocamlc "ocamlc -w +a-4-29"
OPTFLAGS = -classic-display -ocamlopt "ocamlopt -O3"

default: native

clean:
	ocamlbuild -clean

native:
	ocamlbuild $(FLAGS) castle_bravo.native

release:
	ocamlbuild $(FLAGS) castle_bravo.native $(OPTFLAGS)

byte:
	ocamlbuild $(FLAGS) castle_bravo.byte -tag 'debug'
