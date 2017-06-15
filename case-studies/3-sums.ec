(*
This file is a part of the masters thesis by Mads Buch.
For licensing refer to www.madsbuch.com/thesis
*)

require import Int IntExtra StdBigop Bigalg.
require import Bool DBool List Option.
require import Aprhl.


(* Ambient properties *)

(* Number of elements in the list, N = size a is in precondition *)
op N : { int | 0 < N } as gt0_N.

(* total amount of privacy it consumes *)
op eps : {real | 0%r < eps} as gt0_eps.
(* privacy each iteration of the while loop consumes *)
op eps_i : real = (eps/(N+1)%r).

(* Number of elements in the list *)
op Ns : { int | 0 < Ns } as gt0_Ns.

(* Size of q *)
op Qs : { int | 0 < Qs < Ns } as ax_Qs.
(* Ms = floor ( Qs*Ms ), number of q-sized sections that fits in N-sized list *)
op Ms : { int | (Ms-1)*Qs <= Ns <= Ms*Qs } as ax_Ms.

(* privacy consumes for smartsum *)
op eps_s : {real | 0%r < eps_s} as gt0_eps_s.
(* amoun of privacy each iteration consumes *)
op eps_i_s : real = (eps_s/(Ms+1)%r).

(***********************************************************************)

clone import BigZModule as BigInt with
  type t <- int,
  op ZM.zeror <- 0,
  op ZM.( + ) <- Int.(+),
  op ZM.([-]) <- Int.([-])
  proof * by smt. 
abbrev sum = BigInt.big predT idfun.

print BigInt.big.

lemma sum_sanity_1 :
  sum [1 ; 2 ; 3] = 6 by smt ().

lemma sum_sanity_2 :
  sum [] = 0 by progress. 


lemma sum_concat (l1 l2 : int list) :
    sum (l1 ++ l2) = sum (l1) + sum (l2) by smt.

lemma sum_add (l : int list) (i : int) :
  (sum l) + i = sum (i :: l) by smt().

(* removes element with index n from the list *)
op remv ['a] (n : int) (xs : 'a list) = take n xs ++ drop (n+1) xs.

(* We need to quantify the type variable for the sake of EasyCryp *)
lemma remv_empty (l : 'a list) (i : int) :
  l = [] => remv i l = [] by smt.

lemma remv_concat (xs : int list) (n : int) :
  0 <= n < size xs => 
    xs = take n xs ++ [nth 0 xs n] ++ drop (n+1) xs by smt.

lemma remv_size (l : 'a list) (n : int) :
  0 <= n < size l => size (remv n l) = (size l) - 1 by move => @/remv; smt.

lemma remv_other (l : 'a list) (n : int):
  size l < n => remv n l = l by smt.

lemma remv_behead (l : int list):
  remv 0 l = behead l by smt.

lemma remv_sanity_1 :
    remv 1 [1 ; 2 ; 3] = [1 ; 3] by smt ().

lemma remv_sum_sanity_1 :
  sum [1 ; 2] = sum (remv 1 [1;2]) + nth 0 [1;2] 1 by smt ().

lemma remv_sum_sanity_2 :
  sum [] = sum (remv 0 []) + nth 0 [] 0.
proof.
  move => @/remv. move => @/sum.
  progress.
qed.

lemma remv_sum_1 (l : int list) (x : int) :
    sum (x :: l) = x + (sum (remv 0 (x :: l))) by smt().

lemma remv_sum (l : int list) (t : int) :
  0 <= t < size l => 
    sum l = (sum (remv t l)) + (nth 0 l t) by smt (remv_concat BigInt.big_cat sum_add).

(***********************************************************************)

(* Offset Copy as used in the smartsum algorithm *)
op offsetCopy (s : int list, x : int list
  , c : int, i : int, q : int) : int list =
     take i s 
  ++ map ( (+)  c) (take q x) 
  ++ drop (i+q) s.

(* Sanity lemmas for offsetcopy *)
lemma offsetcopy_sanity_1:
      size [1 ; 2 ; 3 ; 4 ;5 ; 6 ; 7 ; 8 ; 9] 
    = size (offsetCopy 
             [1 ; 2 ; 3 ; 4 ;5 ; 6 ; 7 ; 8 ; 9]
             [9 ; 8 ; 7 ; 6 ;5 ; 4 ; 3 ; 2 ; 1] 1 2 4)  by move => @/offsetCopy; progress.

lemma offsetcopy_sanity_2:
       [(9+1) ; (8+1) ; 3 ; 4 ; 5; 6 ; 7 ; 8 ; 9] 
    =  (offsetCopy 
             [1 ; 2 ; 3 ; 4 ;5 ; 6 ; 7 ; 8 ; 9]
             [9 ; 8 ; 7 ; 6 ;5 ; 4 ; 3 ; 2 ; 1] 1 0 2) by move => @/offsetCopy; progress.


(***********************************************************************)
(* The Adjencency Relation *)

(* Note: The empty lists are not adjacent *)
pred adj (l1 l2 : int list)  = 
       (size l1 = size l2
    /\ (exists t, 0 <= t < size l1 /\ 
           remv t l1 = remv t l2)
    /\ (forall i, 0 <= i < size l1 => 
         `|(nth 0 l1 i) - (nth 0 l2 i)| <= 1)).

(* This proposition should be derivable from the sensitivity_one lemma *)
lemma sensitivity_sum_1 l1 l2 :
  adj l1 l2 =>
    `|sum l1 - sum l2| <= 1 by smt (remv_sum).

lemma adj_sanity1 : 
    adj [1 ; 2 ; 3] [1 ; 2 ; 3].
proof.
  move => @/adj.
  split.  
  + trivial.
  split.
  + progress. smt().
  move => i. auto.
qed.

lemma adj_sanity2 : 
    adj [1 ; 3 ; 3] [1 ; 2 ; 3].
proof.
  move => @/adj.
  split.  
  + trivial.
  split.
  + exists 1. progress.
  move => i Hi. smt ().
qed.

op aggr (l : int list) (acc : int) : int list =
  with l = []        => []
  with l = (x :: xs) => (acc + x) :: aggr xs (acc + x).

lemma aggr_s1 : 
    aggr [1 ; 2 ; 3] 0 = [1 ; 3 ; 6] by progress.

lemma aggr_s2 : 
    aggr [0 ; 0 ; 3] 0 = [0 ; 0 ; 3] by progress.

lemma aggr_s3 : 
    aggr [] 0 = [] by progress.

(***********************************************************************)

module Sums = {
  (* Sums a list and adds noise *)
  proc partialsum_sum(a : int list) : int = {
    var s, out;
    s <- sum a;
    out <$ lap eps s;
    return out;
  }

  (* Adds noise to all elements, and sums the list *)
  proc partialsum'(a : int list) : int list = {
    var rs, i, x, s;
    i <- 1;rs <- [];
    while(i < N){
      x <- nth 0 a i;
      s <$ lap eps_i x;
      rs <- s :: rs;
      i <- i+1;
    }
    return aggr rs 0;
  }
  
  proc smartsum(a : int list) : int list = {
    var i, c, b, s, x, qList;

    i <- 0; c <- 0;
    b <- witness; x <- witness;
    s <- witness; 

    while(i < Ms){
      (* q-list *)
      qList <- take Qs a ;
      a <- drop Qs a;

      b <@ partialsum_sum(qList);
      x <@ partialsum'(qList);
      
      s <- offsetCopy s x c (i*Qs) Qs;
      
      c <- c+b;
      i <- i+1;
    }
    return s;
  }
}.

(***********************************************************************)

lemma partialsum_sum_dp :
    aequiv[[eps & 0%r] 
      Sums.partialsum_sum ~ Sums.partialsum_sum :
      adj a{1} a{2}  ==> ={res}]. 
proof.
  proc => /=.
  seq 1 1 : (`|s{1} - s{2}| <= 1).
    * toequiv; auto ; smt.
  lap 0 1.
qed.

(***********************************************************************)

lemma partialsum'_dp :
    aequiv[[eps & 0%r] Sums.partialsum' ~ Sums.partialsum' :
      adj a{1} a{2} /\ (size a{1}) = N ==> ={res}]. 
proof.
  proc => //=.
  seq 2 2 : (adj a{1} a{2} /\ (size a{1}) = N /\ ={i, rs} /\ i{1} = 1 /\ rs{1} = []).
  + toequiv. auto.

  conseq <[(((N+1)%r)*eps_i) & 0%r]>.
  + smt.

  awhile      [(fun k => (eps_i)) & (fun _ => 0%r)]
              (N+1)
              [N - i] 
              (    ={i, rs}
                /\ 0 <= i{1}
                /\  adj a{1} a{2});
    1..4: smt (gt0_eps gt0_N).
  + by rewrite sumr_const; smt.
  + by smt.
  move => k0.
  
  seq 1 1 : (={i, rs} 
                /\ 0 <= i{1}
                /\ i{1} < N
                /\ i{2} < N 
                /\ k0 = N - i{1} 
                /\ N - i{1} <= N + 1
                /\ adj a{1} a{2}
                /\ `|x{1} - x{2}| <= 1).
  + toequiv; auto; smt.
 
  seq 1 1 : (={i, rs} /\ 0 <= i{1}
                /\ i{1} < N 
                /\ i{2} < N 
                /\ k0 = N - i{1} 
                /\ N - i{1} <= N + 1
                /\ adj a{1} a{2}
                /\ `|x{1} - x{2}| <= 1
                /\ s{1} = s{2}) <[eps_i & 0%r]>.
  + lap 0 1.

  toequiv; auto; smt.
qed.

(***********************************************************************)

lemma smartsum_dp :
    aequiv[[eps_s & 0%r] Sums.smartsum ~ Sums.smartsum :
      adj a{1} a{2} /\ (size a{1}) = Ns ==> ={res}].
proof.
  proc => //=.
  
  (* Initialization *)
  seq 5 5 : (={i, c, b, x, s} /\ adj a{1} a{2} /\ size a{1} = Ns /\ i{1} = 0).
  + by toequiv; auto.

  conseq <[(((Ms+1)%r)*eps_i_s) & 0%r]>.
  + smt.

  awhile      [(fun k => (eps_i_s)) & (fun _ => 0%r)]
              (Ms+1)
              [Ms - i] 
              (    ={b, x, i, s}
                /\ 0 <= i{1}
                /\  adj a{1} a{2});
    1..4: smt (gt0_eps_s gt0_Ns ax_Qs ax_Ms).
  + by rewrite sumr_const; smt.
  + by smt.
  move => k0.

  seq 2 2 : (    ={b, x, i, s}
                /\ 0 <= i{1}
                /\  adj a{1} a{2}).
  + toequiv. auto. admit.
 (* Should indeed be provable when the drop-adj lemma is in order. we
    we might need more preconditions *)


  seq 1 1 : (={i, s} /\
  0 <= i{1} /\
  adj a{1} a{2} /\
  adj qList{1} qList{2} /\
  i{1} < Ms /\ i{2} < Ms /\ k0 = Ms - i{1} /\ Ms - i{1} <= Ms + 1) <[(eps_i_s/(2%r)) & 0%r]>.

  (* Here we need a tactic for doing calls in apRHL *)
  admit. (* First call *)

  conseq <[(eps_i_s/(2%r)) & 0%r]> .
  * by smt.

  admit. (* Second call *)
qed.
