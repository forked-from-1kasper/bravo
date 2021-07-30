FLAGS = -use-menhir -yaccflag "--explain" -ocamlc "ocamlc -w +a-4-29"
OPTFLAGS = -classic-display -ocamlopt "ocamlopt -O3"

default: native

clean:
	ocamlbuild -clean

native:
	ocamlbuild $(FLAGS) bravo.native

release:
	ocamlbuild $(FLAGS) bravo.native $(OPTFLAGS)

byte:
	ocamlbuild $(FLAGS) bravo.byte -tag 'debug'
