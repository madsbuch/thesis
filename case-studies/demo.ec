(*
This file is a part of the masters thesis by Mads Buch.
For licensing refer to www.madsbuch.com/thesis
*)

require import Bool DBool Real Int.

(* Some language examples *)

(* Type aliasing *)
type probability = real. 
(* Polymorphic types *)
type 'a Maybe = [
    Something of 'a 
  | Nothing].
type 'a List = [
    (* Note, the difference between "&" and "*" *)
    Cons of 'a & 'a List 
  | Nil ].

(* Operator *)
op num : int.
(* Bound operator *) 
op fortytwo : int = 42.
(* Unbound function *)
op filter : ('a -> bool) -> ('a List) -> ('a List).
(* Bound function *)
op head ['a] (xs : 'a List) : 'a Maybe = 
  with xs = (Nil)       => Nothing
  with xs = (Cons y ys) => Something y.
(* Restricted operato *)
op prob : {probability | 0%r <= prob}  as prob_gt0.


module type A = {
  proc consume(x : int) : unit
}.

module M (A' : A) = {
  var x : int
  var n : int

  proc step() : unit = {
    var b;
    b <$ {0,1};
    n <- n+1;
    if(b){
      x <- x+1;
    } else {
      x <- x-1;
    }
  }
  
  proc nSteps() : int = {
    return n;
  }

  proc walk() : int = {
    var t, ret;
    t <$ {0,1};
    while(t){
      t <$ {0,1};
      step();
      A'.consume(x);
      ret <@ nSteps();
    }
    return ret;
  }
}.

axiom a1 : 
  forall (a b : bool), a = b => b = a.
axiom a2 (a b : bool) :
  a = b => b = a.
axiom a3 : 
  forall (a : bool) (b : bool), a = b => b = a.
axiom a4 (a : bool) (b : bool) :
  a = b => b = a.
axiom a5 : 
  forall (a b : bool), a = b => 
    forall (c : bool), b = c => a = c.

lemma l1 : 
  forall (a b : bool), a = b => b = a.
proof.
  auto.
qed.
lemma l2 : 
  forall (a b : bool), a = b => 
    forall (c : bool), b = c => a = c by auto.

(* The jdugment examples based on coins *)

op p : real.
op q : real.

axiom p_q : q > p.
axiom pInt : p < 1%r /\ p > 0%r.
axiom qInt : q < 1%r /\ q > 0%r.

(* Access biased coin *)
(*clone import Biased.*)

module Coins = {
  proc unbiased() : bool = {
    var sample;
    sample <$ {0,1};
    return sample;
  }

  proc biased(p : real) : bool = {
    var sample;
    sample <$ Biased.dbiased p;
    return sample;
  }

  proc flip(b : bool) : bool = {
    return !b;
  }

  (* A procedure that never terminates *)
  proc flipNT(b : bool) : bool = {
    while(true){}
    return !b;
  }
}.

lemma ambientDemo (a : bool) (b : bool) :
    (a /\ b) => (b /\ a).
proof.
  smt.
qed.

(* Simple proof for a hoare judgment *)
lemma hlDemo (a : bool):
    hoare[Coins.flip : b = a ==> res = !a]
by proc; auto.

(* Proof of a hoare judgment for a procedure that never terminates *)
lemma hlDemoNT (a : bool):
    hoare[Coins.flipNT : b = a ==> res = !a].
proof.
  proc; auto.
  while (true); skip => //.
qed.

lemma phlDemoEq :
    phoare[Coins.biased : 
      p = (1%r/2%r) ==> res] = (1%r/2%r)
by proc;rnd;skip;smt.

lemma phlDemoUb :
    phoare[Coins.biased : 
      p = (1%r/3%r) ==> res] <= (1%r/2%r)
by proc;rnd;skip;smt.

lemma phlDemoLb :
    phoare[Coins.biased : 
      p = (2%r/3%r) ==> res] >= (1%r/2%r)
by proc;rnd;skip;smt.

lemma prhlDemo :
    equiv[Coins.unbiased ~ Coins.unbiased : true ==> ={res}].
proof.
  proc; rnd; progress.
qed.

(* Simple Aprhl demo *)
op eps : {real | 0%r < eps}  as eps_gt0.
op delt : {real | 0%r < delt} as delt_gt0.

lemma eps_ge0 : 0%r <= eps by smt.
lemma delt_ge0 : 0%r <= delt by smt.

lemma aprhlDemo :
    aequiv[[eps & delt] 
      Coins.unbiased ~ Coins.unbiased : true ==> true].
proof.
  toequiv.
  smt (eps_ge0).
  smt (delt_ge0).
  proc; rnd; progress.
qed.