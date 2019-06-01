%.vo : %.v
	coqc $*.v

#coq files compilation
Cand.vo : Cand.v
Keys.vo : Keys.v
CryptoAxioms.vo : Cand.vo Keys.vo CryptoAxioms.v
ListLemma.vo : ListLemma.v
ValidityExist.vo : ListLemma.vo ValidityExist.v
Schulze.vo : Cand.vo ListLemma.vo ValidityExist.vo Schulze.v
Encryptionschulze.vo : ListLemma.vo ValidityExist.vo Schulze.vo CryptoAxioms.vo Cand.vo Keys.vo Encryptionschulze.v



#java compilation
%.class : schulze/%.java
	javac -cp ".:jarfiles/unicrypt-2.3.jar:jarfiles/jnagmp-2.0.0.jar:jarfiles/jna-4.5.0.jar" schulze/$*.java

CryptoWrapper.class : schulze/CryptoWrapper.java 

#Test if Main prints Hello World
CryptoWrapper : schulze/CryptoWrapper.class
		java -cp ".:jarfiles/unicrypt-2.3.jar:jarfiles/jnagmp-2.0.0.jar:jarfiles/jna-4.5.0.jar" schulze.CryptoWrapper

#Create a jar file
jarfile : schulze/CryptoWrapper.class
		jar cvf schulze/schulze.jar schulze/CryptoWrapper.class


Main : main.ml
	ocamlfind ocamlopt -O3 -o a.out -linkpkg -package str,num,menhirLib -I ocaml-java/bin/camljava camljava.cmxa -ppx ocaml-java/bin/ocaml-java-ppx parser.mli parser.ml big.ml lexer.ml \
		Sumbool.mli Sumbool.ml Cand.mli Cand.ml Keys.mli Keys.mli Specif.ml Datatypes.mli Datatypes.ml BinPos.mli BinPos.ml BinInt.mli BinInt.ml CryptoAxioms.mli CryptoAxioms.ml List0.mli List0.ml  \
		PeanoNat.mli PeanoNat.ml ZArith_dec.mli ZArith_dec.ml Zbool.mli Zbool.ml ListLemma.mli ListLemma.ml ValidityExist.ml  ZArith_dec.mli ZArith_dec.ml cryptobinding.ml Schulze.mli \
		Schulze.ml Encryptionschulze.mli Encryptionschulze.ml Top.ml main.ml


#clean 
clean:
	rm -rf _build *.vo *.glob *.class *.cmi *.cmx *.o *.out BinInt.* BinNums.* BinPos.* Cand.ml Cand.mli  CryptoAxioms.ml CryptoAxioms.mli \
		Datatypes.ml Datatypes.mli Encryptionschulze.ml Encryptionschulze.mli Keys.ml Keys.mli ListLemma.ml ListLemma.mli List0.ml \
		List0.mli PeanoNat.ml PeanoNat.mli Schulze.ml Schulze.mli Specif.ml Specif.mli  Sumbool.ml  Sumbool.mli Top.ml Top.mli \
		ValidityExist.ml ValidityExist.mli ZArith_dec.ml ZArith_dec.mli Zbool.ml Zbool.mli lib.ml lib.mli main.native main.byte schulze/*.class schulze/*.jar 2>/dev/null || true
