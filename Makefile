LIBS := -libs str,unix
OCAMLOPT := -ocamlopt "ocamlopt -unsafe -inline 100"
#LFLAGS := -lflags -ccopt,-static

all: leancop hasher

leancop: *ml *mll *mly
	ocamlbuild $(OCAMLOPT) $(LFLAGS) $(LIBS) leancop.native
	@mv leancop.native leancop

hasher: *ml *mll *mly
	ocamlbuild $(OCAMLOPT) $(LFLAGS) $(LIBS) hasher.native
	@mv hasher.native hasher

top: *ml *mll *mly
	ocamlbuild $(LIBS) leancop.top
	@mv leancop.top top

clean:
	@ocamlbuild -clean
	@rm -f *~
