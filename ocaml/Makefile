LIBS := -libs str,unix
OCAMLOPT := -ocamlopt "ocamlopt -unsafe -inline 100"
#LFLAGS := -lflags -ccopt,-static

all: leancop

leancop: *ml *mll *mly
	ocamlbuild $(OCAMLOPT) $(LFLAGS) $(LIBS) leancop.native
	@mv leancop.native leancop

top: *ml *mll *mly
	ocamlbuild $(LIBS) leancop.top
	@mv leancop.top top

clean:
	@ocamlbuild -clean
	@rm -f *~
