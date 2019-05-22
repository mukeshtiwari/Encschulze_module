Require Import Notations.
Require Import Coq.Lists.List. 
Require Import Coq.Arith.Le.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Bool.Sumbool.
Require Import Bool.Bool.
Require Import Coq.Logic.ConstructiveEpsilon.
Require Import Coq.ZArith.ZArith.
Require Import ListLemma.
Require Import ValidityExist.
Require Import Coq.Logic.FinFun.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Psatz.
Require Export CryptoAxioms.
Require Export Cand.
Import ListNotations.
Open Scope Z. 


Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.

Module Encschulze (Import C : Cand).
  
    (* Decidability of pair of cand *)
    Lemma pair_cand_dec : forall (c d : cand * cand), {c = d} + {c <> d}.
    Proof.
      intros c d. destruct c, d.
      pose proof (dec_cand c c1).
      pose proof (dec_cand c0 c2).
      destruct H, H0. left.
      subst. reflexivity.
      right. unfold not. intros. inversion H. pose proof (n H2). inversion H0.
      right. unfold not. intros. inversion H. pose proof (n H1). inversion H0.
      right. unfold not. intros. inversion H. pose proof (n H1). inversion H0.
    Qed.

    (* all candidate pair is (all_pairs cand_all) *)      
    Lemma every_cand_t : forall (c d : cand), In (c, d) (all_pairs cand_all).
    Proof.
      intros c d. apply  all_pairsin;
                    apply cand_fin.
    Qed.

    Lemma non_empty_l_pair : forall (l : list cand), l <> [] -> all_pairs l <> [].
    Proof.
      destruct l.
      + cbn. auto.
      + cbn. intros Hc Hd.
        inversion Hd.
    Qed.

    Lemma non_empty_cand_pair : all_pairs cand_all <> [].
      apply non_empty_l_pair.
      apply cand_not_nil.
    Qed.
                                                                        Qed.
                                                                        

