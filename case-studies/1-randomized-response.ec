(*
This file is a part of the masters thesis by Mads Buch.
For licensing refer to www.madsbuch.com/thesis
*)

require import Bool Real. (* base types *)
require import Distr DBool. (* distribution stuff *)

(* This is an implementation of the proof for the randomized response protocol
   as laid out in "The Algorithmic Foundations of Differential Privacy" by
   Dwork and Roth.
*)

(* The true implementation of the protocol *)
module RR = {
  proc sample (sec : bool) : bool = {
    var t, t', returnValue : bool;
    t <$ {0,1};
    if (t) {
      returnValue = sec;
    }
    else {
      t' <$ {0,1};
      returnValue = t';
    }
    return returnValue;
  }
}.

(* An aux implementation which is easier to work with as all
   random assignments are isolated *)
module RR' = {
  proc sample (sec : bool) : bool = {
    var t, t', returnValue : bool;
    t  <$ {0,1};
    t' <$ {0,1};
    
    if (t) {
      returnValue = sec;
    }
    else {
      returnValue = t';
    }
    return returnValue;
  }
}.

(* Lossless proofs: We want to make sure that our distributions are well behaved *)
lemma rr_is_lossless :
  islossless RR.sample.
proof.
  proc.
  seq 1 : true => //. (* "=> //" ? *)
  * by rnd; skip; smt.
  * by if; auto; smt.
qed.

lemma rr'_is_lossless :
  islossless RR'.sample.
proof.
  proc.
  seq 1 : true => //.
  * rnd; skip; smt.
  * seq 1 : true => //.
    + rnd; skip; smt.
    + auto.
qed.

(* We prove that we indee can use the simpler distribution *)
lemma rr_and_rr'_are_equiv :
  equiv[RR.sample ~ RR'.sample : ={sec} ==> ={res}].
proof.  
  proc.
  seq 1 1 : (={sec, t}) => //.
    + by rnd; skip; smt.
  if{1}.
  + by auto; smt.
  + seq 1 1 : (={sec, t, t'} /\ t{2} = false) => //.
    * auto; smt().   
    * auto.
qed.

(* Some aux lemmas on RR', as it is equivalent and easier to reason about *)
lemma rr_true_is_3_4th_aux &m:
  phoare[RR'.sample : sec ==> res] = (3%r/4%r).
proof.  
  proc.
  wp.
  seq 1: t (1%r/2%r) 1%r (1%r/2%r) (1%r/2%r) sec => //;
    1..5 : (rnd; skip => //; smt).
qed.

lemma rr_false_is_1_4th_aux &m:
  phoare[RR'.sample : !sec ==> res] = (1%r/4%r).
proof.  
  proc.
  wp.
  seq 1: t (1%r/2%r) 0%r  (1%r/2%r) (1%r/2%r) (!sec) => //;
    1..4: (rnd; skip => //; smt).
qed.

(* Derive the probabilities *)
lemma rr_true_is_3_4th &m:
  Pr[RR.sample(true) @ &m : res] = (3%r/4%r).
proof.
  have ->:
      Pr[RR.sample(true) @ &m: res]
    = Pr[RR'.sample(true) @ &m: res].
  * by byequiv rr_and_rr'_are_equiv.
  byphoare (_:sec ==> res) => //.
  apply rr_true_is_3_4th_aux.
qed.

lemma rr_false_is_1_4th &m:
  Pr[RR.sample(false) @ &m : res] = (1%r/4%r).
proof.
  have ->:
      Pr[RR.sample(false) @ &m: res]
    = Pr[RR'.sample(false) @ &m: res] by byequiv rr_and_rr'_are_equiv.
  byphoare (_: (!sec) ==> res) => //.
  apply rr_false_is_1_4th_aux.
qed.

(* Proof for the randomized response *)
lemma RRIsEpsilonLg3DP &m (x, y : bool):
  Pr[RR.sample(x) @ &m: res] 
    <= 3%r * Pr[RR.sample(y) @ &m: res] by smt.

