
OBJ=bintree.cmo common.cmo xprint.cmo iterator.cmo myseq.cmo mymap.cmo mdl.cmo find_merge.cmo intmap.cmo
SRC=madil_common.cmo task.cmo kind.cmo data.cmo path.cmo expr.cmo model.cmo task_model.cmo refining.cmo learning.cmo madil.cmo batch.cmo
SRC_FABLIS=focus.cmo syntax.cmo lis.cmo jsutils.cmo webapp.cmo html.cmo widget_focus.cmo widget_suggestions.cmo widget_table.cmo widget_commandline.cmo

FLAGS= -g -principal -I ../../lib -package unix,str,num,csv,yojson,ppx_deriving_yojson
FLAGS_FABLIS = -package js_of_ocaml,js_of_ocaml-lwt,js_of_ocaml-ppx -I ../../fablis/core -I ../../fablis/core/webapp
#JSOO_FLAGS = -pretty -no-inline -debug-info # for dev
JSOO_FLAGS = --opt 3 # for prod

all: $(SRC:.cmo=.cmx)

lis: $(SRC) arc_lis.ml
	ocamlfind ocamlc -c $(FLAGS) $(FLAGS_FABLIS) arc_lis.ml

clean:
	rm -f *.cm[ioax]

.SUFFIXES: .ml .mli .cmo .cmi

%.cmo: %.ml
	ocamlfind ocamlc -c $(FLAGS) $<

%.cmx: %.ml
	ocamlfind ocamlopt -c $(FLAGS) $<
