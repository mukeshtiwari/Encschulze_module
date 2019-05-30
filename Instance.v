Require Import Coq.Lists.List. 
Import ListNotations.
Require Export Cand.
Require Export Keys.
Require Export CryptoAxioms.
Require Export Encryptionschulze.

(* Create a Cand Instance *)
Module CndInstance <: Cand.
  
  Inductive Cand := A | B | C.

  Definition cand := Cand.

  Definition cand_all := [A; B; C].

  Lemma cand_fin : forall c, In c cand_all.
  Proof.
    unfold cand_all; intro a; repeat induction a || (unfold In; tauto).
  Qed.

  Lemma dec_cand : forall c d : cand, {c = d} + {c <> d}.
  Proof.
    intros a b;
      repeat induction a; 
      repeat (induction b) || (right; discriminate) ||(left; trivial).
  Defined.

  Lemma cand_not_nil : cand_all <> nil.
  Proof. unfold cand_all. intros H. inversion H.
  Qed.

End CndInstance.



Module M := Encschulze CndInstance.

Extraction Language Ocaml.
Extraction "lib.ml" Encshulze.pschulze_winners.
