OCAMLC = ocamlc
OCAMLCFLAGS = -c
OCAMLCINCL = -I Logics

OCAMLYACC = ocamlyacc
OCAMLYACCFLAGS =
OCAMLLEX = ocamllex
OCAMLLEXFLAGS =

OCAMLDOC = ocamldoc
OCAMLDOCFLAGS = -html -d docs -sort -v -keep-code -colorize-code

PARSER = smtbench

%.cmo : %.ml
	$(OCAMLC) $(OCAMLCFLAGS) $(OCAMLCINCL) $<
%.cmi : %.mli
	$(OCAMLC) $(OCAMLCFLAGS) $(OCAMLCINCL) $<
%.ml %.mli : %.mly
	$(OCAMLYACC) $(OCAMLYACCFLAGS) $<
%.ml : %.mll
	$(OCAMLLEX) $(OCAMLLEXFLAGS) $<

all: benchmark

benchmark: types.cmo tables.cmo eval.cmo printing.cmo support.cmo \
           Logics/.logics signature.cmo smt_lexer.cmo smt_parser.cmo \
           readbench.ml
	rm -f $(PARSER)
	$(OCAMLC) types.cmo tables.cmo eval.cmo printing.cmo support.cmo \
Logics/logic_smt.cmo Logics/logic_qf_a.cmo Logics/logic_qf_??.cmo \
Logics/logic_qf_???.cmo Logics/logic_*.cmo \
signature.cmo smt_lexer.cmo smt_parser.cmo readbench.ml -o $(PARSER)


htdocs: benchmark 
	mkdir docs ; $(OCAMLDOC) *.ml *.mli Logics/*.ml $(OCAMLDOCFLAGS) $(OCAMLCINCL)

htdocs-all: benchmark 
	mkdir docs ; $(OCAMLDOC) *.ml Logics/*.ml $(OCAMLDOCFLAGS) $(OCAMLCINCL)

clean:
	rm -rf Logics/.logics Logics/*.cm* *.cm* smt_lexer.ml smt_parser.ml smt_parser.mli \
smtbench docs

types.cmo: types.ml
tables.cmi: types.cmo tables.mli 
tables.cmo: types.cmo tables.cmi tables.ml
eval.cmi: types.cmo eval.mli
eval.cmo: types.cmo eval.cmi eval.ml
printing.cmi: types.cmo tables.cmo eval.cmo printing.mli
printing.cmo: types.cmo tables.cmo eval.cmo printing.cmi printing.ml 
support.cmi: types.cmo tables.cmo eval.cmo printing.cmo support.mli
support.cmo: types.cmo tables.cmo eval.cmo printing.cmo support.cmi \
             support.ml
Logics/.logics: types.cmo Logics/logic_*.ml
	$(MAKE) -C Logics
signature.cmi: types.cmo tables.cmo eval.cmo printing.cmo support.cmo \
               Logics/.logics signature.mli
signature.cmo: types.cmo tables.cmo eval.cmo printing.cmo support.cmo \
               Logics/.logics signature.cmi signature.ml

smt_parser.ml smt_parser.mli: smt_parser.mly
smt_lexer.ml: smt_lexer.mll
smt_parser.cmi: types.cmo tables.cmo eval.cmo printing.cmo support.cmo \
                Logics/.logics signature.cmo smt_parser.mli
smt_parser.cmo: types.cmo tables.cmo eval.cmo printing.cmo support.cmo \
                Logics/.logics signature.cmo smt_parser.cmi smt_parser.ml
smt_lexer.cmo: types.cmo tables.cmo eval.cmo printing.cmo support.cmo \
               Logics/.logics signature.cmo smt_parser.cmo smt_lexer.ml
