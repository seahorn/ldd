OCAMLC = ocamlc
OCAMLCFLAGS = -c
OCAMLCINCL = -I ../ types.cmo

%.cmo : %.ml
	$(OCAMLC) $(OCAMLCFLAGS) $(OCAMLCINCL) $< && touch .logics
%.cmi : %.mli
	$(OCAMLC) $(OCAMLCFLAGS) $(OCAMLCINCL) $< && touch .logics

all: logic_smt.cmo logic_qf_a.cmo logic_qf_ax.cmo logic_qf_bv.cmo logic_qf_idl.cmo \
     logic_qf_lia.cmo logic_qf_lra.cmo logic_qf_rdl.cmo \
     logic_auflia.cmo logic_auflira.cmo logic_aufnira.cmo logic_qf_aufbv.cmo \
     logic_qf_auflia.cmo logic_qf_ufbv32.cmo logic_qf_ufbv.cmo logic_qf_ufidl.cmo \
     logic_qf_uflia.cmo logic_qf_uflra.cmo logic_qf_uf.cmo

logic_smt.cmo: logic_smt.ml
logic_qf_a.cmo: logic_smt.cmo logic_qf_a.ml
logic_qf_ax.cmo: logic_smt.cmo logic_qf_ax.ml
logic_qf_bv.cmo: logic_smt.cmo logic_qf_bv.ml
logic_qf_idl.cmo: logic_smt.cmo logic_qf_idl.ml
logic_qf_lia.cmo: logic_smt.cmo logic_qf_lia.ml
logic_qf_lra.cmo: logic_smt.cmo logic_qf_lra.ml
logic_qf_rdl.cmo: logic_smt.cmo logic_qf_rdl.ml
logic_auflia.cmo: logic_smt.cmo logic_qf_ax.cmo logic_qf_lia.cmo logic_auflia.ml
logic_auflira.cmo: logic_smt.cmo logic_qf_ax.cmo logic_qf_idl.cmo logic_qf_rdl.cmo logic_auflira.ml
logic_aufnira.cmo: logic_smt.cmo logic_qf_ax.cmo logic_qf_lia.cmo logic_qf_lra.cmo logic_aufnira.ml
logic_qf_auflia.cmo: logic_smt.cmo logic_qf_ax.cmo logic_qf_lia.cmo logic_qf_auflia.ml
logic_qf_aufbv.cmo: logic_smt.cmo logic_qf_ax.cmo logic_qf_bv.cmo logic_qf_aufbv.ml

logic_qf_ufbv32.cmo: logic_smt.cmo logic_qf_bv.cmo logic_qf_ufbv32.ml
logic_qf_ufbv.cmo: logic_smt.cmo logic_qf_bv.cmo logic_qf_ufbv.ml
logic_qf_ufidl.cmo: logic_smt.cmo logic_qf_idl.cmo logic_qf_ufidl.ml
logic_qf_uflia.cmo: logic_smt.cmo logic_qf_lia.cmo logic_qf_uflia.ml
logic_qf_uflra.cmo: logic_smt.cmo logic_qf_lra.cmo logic_qf_uflra.ml
logic_qf_uf.cmo: logic_smt.cmo logic_qf_uf.ml
