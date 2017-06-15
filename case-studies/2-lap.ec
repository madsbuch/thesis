(*
This file is a part of the masters thesis by Mads Buch.
For licensing refer to www.madsbuch.com/thesis
*)

require import Int IntExtra Bool List.
require import DBool.
require import Aprhl.

(* Ambient parameters *)
op N : { int | 0 < N } as gt0_N.
op eps : {real | 0%r < eps} as gt0_eps.
op eps_i : real = (eps/(N+1)%r).

module Lap = {
  (* Release numeric value *)
  proc val(x : int) : int = {
    var s;
    s <$ lap eps x;
    return s;
  }

  (* release value based on branching *)
  proc th_coupling(x : int, t : int) : bool = {
    var s;
    s <$ lap eps x;
    return (s < t);
  }
  
  (* Sequential composition *)
  proc seq_comp(x : int, y : int) : (int * int) = {
    var s1, s2;
    s1 <$ lap (eps/2%r) x;
    s2 <$ lap (eps/2%r) y;
    return (s1, s2);
  }

  (* Procedure that allows to release a list of integer values *)
  proc list(a : int list) : int list = {
    var rs, i, x, s;
    i <- 0;rs <- [];
    while(i < N){
      x <- nth 0 a i;
      s <$ lap eps_i x;
      rs <- rs ++ [s];
      i <- i+1;
    }
    return rs;
  }

  (* Procedure that releses first integer greater than t *)
  proc th_list(a : int list, t : int) : int = {
    var r, i, x, s;
    i <- 0; r <- -1;
    while(i < N){
      x <- nth 0 a i;
      s <$ lap eps_i x;
      if(t < s /\ r = -1){
        r <- i;
      }
      i <- i+1;
    }
    return r;
  }
}.

(* Adjacency of values *)
pred adjV (v1 v2 : int) = `|v1 - v2| <= 1.

(* Adjacency of lists *)
pred adjL (l1 l2 : int list) = 
        size l1 = size l2
    /\  forall i, 0 <= i < size l1 =>
          `|(nth 0 l1 i) - (nth 0 l2 i)| <= 1.

(* Proof for numeric value release *)
lemma lap_value_dp :
  aequiv[[eps & 0%r]
    Lap.val ~ Lap.val : adjV x{1} x{2} ==> ={res}] 
by proc; lap 0 1.

(* Proof for branching release *)
lemma lap_th :
  aequiv[[eps & 0%r]
    Lap.th_coupling ~ Lap.th_coupling : adjV x{1} x{2} /\ ={t} ==> ={res}].
proof.
  proc.
  conseq (_ : _ ==> s{1} = s{2});1: smt.
  lap 0 1.
qed.

(* Proof for sequential composition *)
lemma lap_seq_comp :
  aequiv[[eps & 0%r]
    Lap.seq_comp ~ Lap.seq_comp : adjV x{1} x{2} /\ adjV y{1} y{2}  ==> ={res}].
proof.
  proc => //=.
  
  (* We propagate the relation on the y's and half the privacy budget *)
  seq 1 1 : (adjV y{1} y{2} /\ ={s1}) <[(eps/2%r) & 0%r]>.
  * lap 0 1.
  * lap 0 1.
  smt.
qed.

(* Proof of differential privacy for lists *)
lemma lap_list :
  aequiv[[eps & 0%r]
    Lap.list ~ Lap.list : adjL a{1} a{2} /\ (size a{1}) = N ==> ={res}].
proof.
  proc => //=.
  (* Handle initialization *)
  seq 2 2 : (adjL a{1} a{2} /\ ={i, rs} /\ i{1} = 0).
  + by toequiv; auto; smt.

  (* Rewrite the eps parameter *)
  conseq <[(((N+1)%r)*eps_i) & 0%r]>.
  + smt.

  (* Prove the while loop *)
  awhile      [(fun _ => eps_i) & (fun _ => 0%r)]
              (N+1)
              [N - i] 
              (    ={i, rs}
                /\ 0 <= i{1}
                /\  adjL a{1} a{2});
    1..4:smt (gt0_eps gt0_N).
  + by rewrite sumr_const; smt. 
  + by smt.
  move => k0.
  
  (* Handle initialization of while loop *)
  seq 1 1 : (={i, rs} /\ 0 <= i{1}
                /\ i{1} < N /\ i{2} < N /\ k0 = N - i{1} /\ N - i{1} <= N + 1
                /\ adjL a{1} a{2}
                /\ `|x{1} - x{2}| <= 1).
  + by toequiv; auto; smt.
  
  (* Handle Laplace statement in the while loop *) 
  seq 1 1 : (={i, rs} /\ 0 <= i{1}
                /\ i{1} < N /\ i{2} < N /\ k0 = N - i{1} /\ N - i{1} <= N + 1
                /\ adjL a{1} a{2}
                /\ `|x{1} - x{2}| <= 1
                /\ s{1} = s{2}) <[eps_i & 0%r]>.
  + lap 0 1.

  (* Handle the last deterministic part and wrap up the proof *)
  toequiv; auto; smt.
qed.

(* This could seem to be the shortcut for the aboveT protocol. But note that we apply
   an equal amount of privacy to all elements. So the privacy budget is spread out
   over all elements, not just the the element that is released. *)
lemma lap_list_th :
  aequiv[[eps & 0%r]
    Lap.th_list ~ Lap.th_list : adjL a{1} a{2} /\ (size a{1}) = N /\ ={t} ==> ={res}].
proof.
  proc => //=.

  seq 2 2 : (adjL a{1} a{2} /\ ={i, r, t} /\ i{1} = 0 /\ r{1} = -1).
  + by toequiv; auto; smt.

  conseq <[(((N+1)%r)*eps_i) & 0%r]>.
  + smt.

  awhile      [(fun k => (eps_i)) & (fun _ => 0%r)]
              (N+1)
              [N - i] 
              (    ={i, r, t}
                /\ 0 <= i{1}
                /\  adjL a{1} a{2}).
  + smt (gt0_eps gt0_N).
  + smt (gt0_eps gt0_N).
  + smt (gt0_eps gt0_N).
  + smt (gt0_eps gt0_N).
  + by rewrite sumr_const; smt.
  + by smt.

  move => k0.
  
  seq 1 1 : (={i, r, t} /\ 0 <= i{1}
                /\ i{1} < N /\ i{2} < N /\ k0 = N - i{1} /\ N - i{1} <= N + 1
                /\ adjL a{1} a{2}
                /\ `|x{1} - x{2}| <= 1).
  + by toequiv; auto; smt.
 
  seq 1 1 : (={i, r, t} /\ 0 <= i{1}
                /\ i{1} < N /\ i{2} < N /\ k0 = N - i{1} /\ N - i{1} <= N + 1
                /\ adjL a{1} a{2}
                /\ `|x{1} - x{2}| <= 1
                /\ s{1} = s{2}) <[eps_i & 0%r]>.

  + lap 0 1.
  toequiv; auto; smt.
qed.
