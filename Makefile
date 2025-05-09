# We are not really tracking dependencies because everything is small
# enough to recompile at will.

# change to a different ocamlc if you prefer (e.g., ocamlopt)
COMPILER=ocamlc
 
all: clean riscv cish cfg scish mlish

riscv:
	$(COMPILER) -c word32.ml
	$(COMPILER) -c riscv.ml

cish:
	$(COMPILER) -c cish_ast.ml

cfg:
	$(COMPILER) -c cfg_ast.ml
	$(COMPILER) -c spill.ml
	$(COMPILER) -c graph.ml
	$(COMPILER) -c cfg.ml
	$(COMPILER) -c cfg_compile.ml
	$(COMPILER) -c cish_compile.ml

scish:
	$(COMPILER) -c scish_ast.ml
	$(COMPILER) -c scish_compile.ml

mlish: 
	$(COMPILER) -c cish_ast.ml
	$(COMPILER) -c cish_compile.ml
	$(COMPILER) -c scish_ast.ml
	$(COMPILER) -c scish_compile.ml
	$(COMPILER) -c mlish_ast.ml
	ocamlyacc ml_parse.mly
	$(COMPILER) -c ml_parse.mli
	$(COMPILER) -c ml_parse.ml
	ocamllex ml_lex.mll
	$(COMPILER) -c ml_lex.ml
	$(COMPILER) -c mlish_type_check.ml
	$(COMPILER) -c mlish_compile.ml
	$(COMPILER) -c main.ml
	$(COMPILER) -o final_mlish cish_ast.cmo word32.cmo riscv.cmo cfg_ast.cmo graph.cmo spill.cmo cfg.cmo cfg_compile.ml cish_compile.cmo scish_ast.cmo scish_compile.cmo mlish_ast.cmo ml_parse.cmo ml_lex.cmo mlish_type_check.cmo mlish_compile.cmo main.cmo

clean:
	-rm *.cmo *.cmi final_mlish ml_parse.ml ml_parse.mli ml_lex.ml

