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

#clean 
clean:
	rm -rf _build *.vo *.glob *.class *.cmi *.cmx *.o *.out lib.ml lib.mli main.native main.byte schulze/*.class schulze/*.jar 2>/dev/null || true
