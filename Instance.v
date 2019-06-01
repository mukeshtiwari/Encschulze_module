Require Import Coq.Lists.List.  
Import ListNotations.
Require Export Cand.
Require Export Keys.
Require Export CryptoAxioms.
Require Export Encryptionschulze.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Logic.FinFun.
Require Export Coq.Program.Basics.
Require Import Coq.extraction.ExtrOcamlZBigInt.
Open Scope Z.

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

Module KeyInstance <: Keys.

  Parameter Prime : Type.
  Parameter prime : Prime. 
  Extract Constant Prime => "Big.big_int". 
  Extract Constant prime => "170141183460469231731687303715884114527".

  Parameter Generator : Type.
  Parameter gen : Generator.
  Extract Constant Generator => "Big.big_int".
  Extract Constant gen => "4".

  Parameter Pubkey : Type.
  Parameter publickey : Pubkey.
  Extract Constant Pubkey => "Big.big_int".
  Extract Constant publickey => "49228593607874990954666071614777776087".

  Parameter Prikey : Type.
  Parameter privatekey : Prikey.
  Extract Constant Prikey => "Big.big_int".
  Extract Constant privatekey => "60245260967214266009141128892124363925".

End KeyInstance.

Module AbsInstance.

  Parameter ciphertext : Type.
  Extract Constant ciphertext => "'ciphertext".

  Parameter Commitment : Type.
  Extract Constant Commitment => "'commitment".

  (* Permutation Zero Knowledge Proof. *)
  Parameter PermZkp : Type.
  Extract Constant PermZkp => "'permZkp".

  (* Randomeness added during the commitment computation *)
  Parameter S : Type.
  Extract Constant S => "'s".

  (* Randomeness needed for shuffling the row/column *)
  Parameter R : Type.
  Extract Constant R => "'r".
  
  (* Zero knowledge proof of Shuffle *)
  Parameter ShuffleZkp : Type.
  Extract Constant ShuffleZkp => "'shuffleZkp".

  (* Honest Decryption Zero knowledge Proof *) 
  Parameter DecZkp : Type.
  Extract Constant DecZkp => "'decZkp".

End AbsInstance. 

Module CrpInstance <: CryptoAxioms.Crypto CndInstance KeyInstance AbsInstance.
  Import CndInstance KeyInstance AbsInstance.
  
  Definition plaintext := Z.

 
    
  Definition pballot := cand -> cand -> plaintext.
  
  Definition eballot := cand -> cand -> ciphertext.

  Definition Group := (Prime * Generator * Pubkey)%type.
  
  (*
  Inductive Group : Type :=
    group : Prime -> Generator -> Pubkey -> Group. *)
  
  (* Construct a instance of group *)
  Let grp := (prime, gen, publickey).

  (* permutation is Bijective function *)
  Definition Permutation := existsT (pi : cand -> cand), (Bijective pi).

 
  
  Parameter encrypt_message :
    Group -> plaintext -> ciphertext.
  Extract Constant encrypt_message => "Cryptobinding.encrypt_message".

  Parameter decrypt_message :
    Group -> Prikey -> ciphertext -> plaintext.
  Extract Constant decrypt_message => "Cryptobinding.decrypt_message".

  (* This function returns zero knowledge proof of encrypted message (c1, c2) *)
  Parameter construct_zero_knowledge_decryption_proof :
    Group -> Prikey -> ciphertext -> DecZkp.
  Extract Constant construct_zero_knowledge_decryption_proof =>
  "Cryptobinding.construct_zero_knowledge_decryption_proof".
  
  (* Unfortunately, this function would not be extract in code, because 
     it's appears as sort of assertion *)
  Parameter verify_zero_knowledge_decryption_proof :
    Group -> plaintext -> ciphertext -> DecZkp -> bool.
  Extract Constant verify_zero_knowledge_decryption_proof =>
  "Cryptobinding.verify_zero_knowledge_decryption_proof".
 
  
  Parameter generatePermutation :
    Group -> (* group *)
    nat -> (* length  *)
    list cand -> (* cand_all *) 
    Permutation.
  
  Extract Constant generatePermutation => 
  "Cryptobinding.generatePermutation".


  Parameter generateS : Group -> nat -> S.
  Extract Constant generateS => "Cryptobinding.generateS".
  
  Parameter generatePermutationCommitment :
    Group -> (* group *)
    nat -> (* length *)
    list cand -> (* cand_all *)
    Permutation -> (* pi *)
    S -> (*randomness *)
    Commitment. (* cpi *)
  Extract Constant generatePermutationCommitment =>
  "Cryptobinding.generatePermutationCommitment".
  

  (* This function takes Permutation Commitment and S and returns ZKP *)
  Parameter zkpPermutationCommitment :
    Group -> (* group *)
    nat -> (* length *)
    list cand -> (* cand_all *)
    Permutation -> (* pi *)
    Commitment -> (* cpi *)
    S -> (* randomness *)
    PermZkp.
  Extract Constant zkpPermutationCommitment =>
  "Cryptobinding.zkpPermutationCommitment".
  
  Parameter verify_permutation_commitment :
    Group -> (* group *)
    nat -> (* length *)
    Commitment -> (* cpi *)
    PermZkp -> (* zero knowledge proof *)
    bool. (* pcps.verify offlineProof offlinePublicInpu *)
  Extract Constant verify_permutation_commitment =>
  "Cryptobinding.verify_permutation_commitment".
    
  Parameter homomorphic_addition :
    Group -> ciphertext -> ciphertext -> ciphertext.
  Extract Constant homomorphic_addition => "Cryptobinding.homomorphic_addition".
  
  Parameter generateR : Group -> nat -> R.
  Extract Constant generateR => "Cryptobinding.generateR".
  
  Parameter shuffle :
    Group -> (* group *)
    nat -> (* Length of list cand *)
    list cand -> (* cand_all because we need to convert function into list *)
    (forall n m : cand, {n = m} + {n <> m}) -> (* This is need because we want to construct the ballot *)
    (cand -> ciphertext) -> (* ciphertext *)
    Permutation -> (* pi *)
    R -> (* Randomness R *)
    (cand -> ciphertext).
  Extract Constant shuffle => "Cryptobinding.shuffle".

  
  Parameter shuffle_zkp :
    Group -> (* group *)
    nat -> (* length *)
    list cand -> (* cand_all *)
    (cand -> ciphertext) -> (* cipertext *)
    (cand -> ciphertext) -> (* shuffle cipertext *)
    Permutation -> (* pi *)
    Commitment -> (* cpi *)
    S -> (* s, permutation commitment randomness *)
    R -> (* r, shuffle randomness *)
    ShuffleZkp. (* zero knowledge proof of shuffle *)
  Extract Constant shuffle_zkp => "Cryptobinding.shuffle_zkp".
  
  Parameter verify_shuffle:
    Group -> (* group *)
    nat -> (* length *)
    list cand ->
    (cand -> ciphertext) -> (* cipertext *)
    (cand -> ciphertext) -> (* shuffled cipertext *)
    Commitment -> (* permutation commitment *)
    ShuffleZkp -> (* zero knowledge proof of shuffle *)
    bool. (* true or false *)
  Extract Constant verify_shuffle => "Cryptobinding.verify_shuffle".

End CrpInstance.
 
Module M := Encschulze CndInstance KeyInstance AbsInstance CrpInstance.

Extraction Language OCaml.
(* Avoid name clash with modules *)
Extraction Blacklist List String Int.
Separate Extraction M.pschulze_winners.

