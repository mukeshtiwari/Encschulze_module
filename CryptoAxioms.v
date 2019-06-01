Require Import Notations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FinFun.
Require Import Coq.Program.Basics.
Require Import Cand.
Require Import Keys.
Import ListNotations.
Open Scope Z.

Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.

(* https://stackoverflow.com/questions/8869678/polymorphic-type-inside-a-module-ocaml *)
(* The reason for moving these abstract types is precisly the reason explaned in above link *)
Module Type Abstype.

  (* Ciphertext is abstract type *)
  Parameter ciphertext : Type.

  (* Pedersan's commitment for a given permutation *) 
  Parameter Commitment : Type.

  (* Permutation Zero Knowledge Proof. *)
  Parameter PermZkp : Type.

  (* Randomeness added during the commitment computation *)
  Parameter S : Type.

  (* Randomeness needed for shuffling the row/column *)
  Parameter R : Type.

  (* Zero knowledge proof of Shuffle *)
  Parameter ShuffleZkp : Type. 

  (* Honest Decryption Zero knowledge Proof *)
  Parameter DecZkp : Type.

End Abstype.

(* This module type is interface for all the data, and functions. The axioms about 
   these functions are assumed in CAxioms module *)
Module Type Crypto (Import C : Cand) (Import K : Keys) (Import Abst : Abstype).

  (* Plain text is integer. *)
  Definition plaintext := Z.

  
  (* ballot is plain text value *)
  Definition pballot := cand -> cand -> plaintext.
  
  (* eballot is encrypted value *)
  Definition eballot := cand -> cand -> ciphertext.

 
  Definition Group := (Prime * Generator * Pubkey)%type.

  (* Construct a instance of group *)
  Let grp := (prime, gen, publickey).
  
  
  (* This function encrypts the message. It will be instantiated 
     by Crypto library function. In our case, Unicrypt library functions *)
  Parameter encrypt_message :
    Group ->  plaintext -> ciphertext.
  
  (* This function decrypts the message *)
  Parameter decrypt_message :
    Group -> Prikey -> ciphertext -> plaintext.

  (* This function returns zero knowledge proof of encrypted message (c1, c2) *)
  Parameter construct_zero_knowledge_decryption_proof :
    Group -> Prikey -> ciphertext -> DecZkp.
                                                                           
  (* This function verifies the zero knowledge proof of plaintext, m, is honest decryption 
     of ciphertext *)
  Parameter verify_zero_knowledge_decryption_proof :
    Group -> plaintext -> ciphertext -> DecZkp -> bool.
  
  (* permutation is Bijective function *)
  Definition Permutation := existsT (pi : cand -> cand), (Bijective pi).

   
  (* The idea is for each ballot u, we are going to count 
       we generate pi, cpi, and zkpcpi. We call row permute function 
       u and pi and it returns v. Then We call column permutation 
       on v and pi and it returns w. We decryp w as b with zero knowledge
       proof. *)
  
  (* We call a java function which returns permutation. Basically java function returns 
       array which is converted back to function in OCaml land *)
  Parameter generatePermutation :
    Group -> (* group *)
    nat -> (* length  *)
    list cand -> (* cand_all *) 
    Permutation.   
  

  (* Generate randomness used in permutation commitment. 
       Tuple s = pcs.getRandomizeSpace().getrandomElement() *)
  Parameter generateS : Group -> nat -> S.
  
  (* Pass the permutation and randomness, it returns commitment. The S used here 
     will be used in zero knowledge proof *)
  Parameter generatePermutationCommitment :
    Group -> (* group *)
    nat -> (* length *)
    list cand -> (* cand_all *)
    Permutation -> (* pi *)
    S -> (*randomness *)
    Commitment. (* cpi *)

  (* This function takes Permutation Commitment and S and returns ZKP *)
  Parameter zkpPermutationCommitment :
    Group -> (* group *)
    nat -> (* length *)
    list cand -> (* cand_all *)
    Permutation -> (* pi *)
    Commitment -> (* cpi *)
    S -> (* randomness *)
    PermZkp.
      
  Parameter verify_permutation_commitment :
    Group -> (* group *)
    nat -> (* length *)
    Commitment -> (* cpi *)
    PermZkp -> (* zero knowledge proof *)
    bool. (* pcps.verify offlineProof offlinePublicInpu *)
  
    
  Parameter homomorphic_addition :
    Group -> ciphertext -> ciphertext -> ciphertext.
  
  
  (* Start of Shuffle code *)
  (* Generate Randomness R by passing group and length of candidate list*)
  Parameter generateR : Group -> nat -> R.
  
  (* We need List.length cand_all because mixer object is created using 
     elGamal, publickey and n *)
  Parameter shuffle :
    Group -> (* group *)
    nat -> (* Length of list cand *)
    list cand -> (* cand_all because we need to convert function into list *)
    (forall n m : cand, {n = m} + {n <> m}) -> (* This is need because we want to construct the ballot *)
    (cand -> ciphertext) -> (* ciphertext *)
    Permutation -> (* pi *)
    R -> (* Randomness R *)
    (cand -> ciphertext).
  
  (* Construct zero knowledge proof from original and shuffled ballot *)   
  (* Each row of ballot is represented by function *)
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
  
  (* verify shuffle. This function checks the claim about a shuffled ciphertext is 
       shuffling of a given ciphertext by a permutation whose commitment is given *)
  Parameter verify_shuffle:
    Group -> (* group *)
    nat -> (* length *)
    list cand ->
    (cand -> ciphertext) -> (* cipertext *)
    (cand -> ciphertext) -> (* shuffled cipertext *)
    Commitment -> (* permutation commitment *)
    ShuffleZkp -> (* zero knowledge proof of shuffle *)
    bool. (* true or false *)
 
End Crypto.

(* The reason for separating the Axioms from functions is that these axioms
   no longer need to instantiate for extraction *)
Module CAxioms  (Import C : Cand) (Import K : Keys) (Import Abst : Abstype)
       (Import Crp : Crypto C K Abst).
  
  (* Relation between Public and Private key. This axiom enforces that 
       publickey and privatekey are generated in pair according to 
       key generation protocol.  *)
  Axiom Keypair : Pubkey -> Prikey -> Prop.
  
  (* Coherence Axiom that states that publickey and privatekey are related *)
  Axiom keypair : Keypair publickey privatekey.
  
  (* Coherence axiom about honest decryption zero knowledge proof *)
  Axiom verify_honest_decryption_zkp :
    forall (pt : plaintext) (ct : ciphertext)
      (H : pt = decrypt_message Crp.grp privatekey ct),
      verify_zero_knowledge_decryption_proof
        Crp.grp pt ct
        (construct_zero_knowledge_decryption_proof Crp.grp privatekey ct) = true.


  
  (* Decryption is left inverse, and we can only decrypt when the keys are 
     related  *)
  Axiom decryption_deterministic :
    forall (pt : plaintext),
      decrypt_message Crp.grp privatekey (encrypt_message Crp.grp pt) = pt.


    
  Axiom permutation_commitment_axiom :
    forall (pi : Permutation) (cpi : Commitment) (s : S) (zkppermcommit : PermZkp)
      (H1 : cpi = generatePermutationCommitment Crp.grp (List.length cand_all) cand_all pi s)
      (H2 : zkppermcommit = zkpPermutationCommitment
                              Crp.grp (List.length cand_all) cand_all pi cpi s),
      verify_permutation_commitment Crp.grp (List.length cand_all)
                                    cpi zkppermcommit = true.

  (* Property of Homomorphic addition *)
  Axiom homomorphic_addition_axiom :
    forall (c d : ciphertext),
      decrypt_message Crp.grp privatekey (homomorphic_addition Crp.grp c d) =
      decrypt_message Crp.grp privatekey c + decrypt_message Crp.grp privatekey d.    


   (* Coherence Axiom about shuffle. If every thing is 
       followed according to protocol then verify_shuffle function 
       returns true *)
  Axiom verify_shuffle_axiom :
    forall (pi : Permutation) (cpi : Commitment) (s : S)
      (cp shuffledcp : cand -> ciphertext)
      (r : R) (zkprowshuffle : ShuffleZkp)
      (H1 : cpi = generatePermutationCommitment Crp.grp (List.length cand_all) cand_all pi s)
      (H2 : shuffledcp = shuffle Crp.grp (List.length cand_all) cand_all dec_cand cp pi r)
      (H3 : zkprowshuffle = shuffle_zkp Crp.grp (List.length cand_all)
                                        cand_all cp shuffledcp pi cpi s r),
      verify_shuffle Crp.grp (List.length cand_all)
                     cand_all cp shuffledcp cpi zkprowshuffle = true. 

  
  (* Coherence about shuffle introducing reencryption *)
  Axiom shuffle_perm :
    forall n f pi r g, 
      shuffle Crp.grp n cand_all dec_cand (f : cand -> ciphertext) (pi : Permutation) r = g ->
      forall c, decrypt_message Crp.grp privatekey (g c) =
           decrypt_message Crp.grp privatekey (compose f (projT1 pi) c).
  (* end of axioms about shuffle. *)    
  
  
  (* This axiom states that 
       if verify_zero_knowledge_decryption_proof grp d c zkp = true then 
       d is honest decryption of c *)
  Axiom decryption_from_zkp_proof :
    forall c d zkp, 
      verify_zero_knowledge_decryption_proof Crp.grp d c zkp = true -> 
      d = decrypt_message Crp.grp privatekey c.
  
  (* Coherence axiom about Permutation *)
  Axiom perm_axiom :
    forall cpi zkpcpi, 
      verify_permutation_commitment Crp.grp (Datatypes.length cand_all) cpi zkpcpi = true ->
      existsT (pi : Permutation), forall (f g : cand -> ciphertext) (zkppf : ShuffleZkp), 
    verify_shuffle Crp.grp (Datatypes.length cand_all) cand_all f g cpi zkppf = true ->
    forall c, decrypt_message Crp.grp privatekey (g c) =
         decrypt_message Crp.grp privatekey (compose f (projT1 pi) c).

  (* End of Axioms *)
End CAxioms.
