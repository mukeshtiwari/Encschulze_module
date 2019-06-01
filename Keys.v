
(* Crypto Infrastrucutre *)
Module Type Keys.

  (* Group Definition in Elgamal *) 
  Parameter Prime : Type. (* Large prime number *)
  Parameter Generator : Type. (* Group generator *)
  Parameter Pubkey : Type. (* Public key *)
  Parameter Prikey : Type. (* Private key *)
 
    
  (* Group infrastrucutre. large prime, generator, private and public key *)
  Parameter prime : Prime.
  Parameter gen : Generator.
  Parameter privatekey : Prikey.
  Parameter publickey : Pubkey.

End Keys.
