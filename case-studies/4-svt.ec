(*
This file is a part of the masters thesis by Mads Buch.
For licensing refer to www.madsbuch.com/thesis
*)

require import Int IntExtra Real RealExtra Bool List.
require import DBool.
require import Aprhl.
require import Option. (* For the witness *)

(*******************************************************************************)

(* Query and database types *)
type query.
type db.

(* value level query and database construction *)
op evalQ : db -> query -> int.
op nullQ : query.

(* Adjacency relation *)
pred adj : db & db.
axiom one_sens d1 d2 q: adj d1 d2 => 
  `|evalQ d1 q - evalQ d2 q| <= 1.

(*******************************************************************************)

(* Properties for the innerLoop algorithm *)
op N : {int | 0 < N} as N_gt0.
op eps : {real | 0%r < eps} as eps_gt0.
op eps_i : real = eps/(4%r).
op eps_t : real = eps/(2%r).

(* Properties of the outerLoop algorithm *)
op C : {int | 0 < C} as C_gt0.
op eps_o_i = eps/((C+1)%r).

(*******************************************************************************)

(* An alias for improving readability *)
op r_init = N+1.

(*******************************************************************************)

(* The adversary provides a query upon request *)
module type Adv = {
  proc getQuery() : query
}.

(*******************************************************************************)

(* Adaptive variations *)
module Svt_a(A : Adv) = {
  proc adaptive_above_t (d : db, tHold : int) : int = {
    var i, q, s, r, t;
    
    i <- 0;
    r <- r_init; 
    t <$ lap eps_t tHold;

    (* Assume that N = size qs *)
    while (i < N){
      if (r = r_init){ 
        q <@ A.getQuery();
        s <$ lap eps_i (evalQ d q);
        if(t <= s){
          r <- i;
        }
      }
      i <- i+1;
    }
    return r;
  }
}.

(*******************************************************************************)

(* Offline Variations *)
module Svt = {
  proc above_t (d : db, qs : query list
    , tHold : int) : int = {
    var i, q, s, r, t;
    i <- 0; r <- r_init; t <$ lap eps_t tHold;

    (* Assume that N = size qs *)
    while (i < N){
      if (r = r_init){
        q <- nth nullQ qs i;
        s <$ lap eps_i (evalQ d q);
        if(t <= s){
          r <- i; 
        }
      }
      i <- i+1;
    }
    return r;
  }

  proc numeric_above_t (d : db, qs : query list, tHold : int) : (int * int) = {
    var r, v;
    r <@ above_t(d, qs, tHold);
    v <$ lap eps (evalQ d (nth nullQ qs r));
    return (r, v);
  }

  proc sparse(d : db, qs : query list, tHold : int) : int list = {
    var rs, i, r;

    rs <- []; i <- 0;

    while(i < C){
      r <@ above_t(d, qs, tHold);
      qs <- drop r qs;

      rs <- rs ++ [r];
      i <- i+1;
    }
    return rs;
  }
}.

(*******************************************************************************)

lemma above_t_dp : 
  aequiv[[eps & 0%r ] Svt.above_t ~ Svt.above_t :
    (adj d{1} d{2} /\ ={qs, tHold} /\ N = size qs{1}) ==> ={res}].
proof.
  proc => //=.

  (* Handle initialization *)
  seq 2 2 : (adj d{1} d{2} 
    /\ N = size qs{1} 
    /\ ={qs, tHold, i, r} 
    /\ i{1} = 0 
    /\ r{1} = r_init).
    by toequiv; auto.
  
  (* couple the thresholds *)
  seq 1 1 : (adj d{1} d{2} 
    /\ N = size qs{1}
    /\ ={qs, tHold, i, r} 
    /\ i{1} = 0 
    /\ r{1} = r_init 
  
       (* Threshold coupling *)
    /\ t{1}+1 = t{2}
      ) <[eps_t & 0%r]>.
  + by lap 1 1.

  (* This in unavoidable as r is manipulated in the inner loop. *)
  pweq (r, r).
  + while true (N - i); auto; try if; auto; progress; 
          try rewrite (lap_ll); try skip; smt().
  + while true (N - i); auto; try if; auto; progress; 
          try rewrite (lap_ll); try skip; smt().
  + move => &1 &2 /(_ (r){1}); smt().
  move => R.
  
  (* We check on k = N-R as k is the loop variant *)
  conseq <[(bigi predT (fun (k : int) => if k = N-R then 2%r*eps_i else 0%r) 0 (N+1)) & 0%r]>.
  + by rewrite (bigD1_cond_if _ _ _ (N-R)) ?range_uniq big1 /=;1..2:smt.
  
  awhile[ (fun k => if k=N-R then 2%r*eps_i else 0%r)
        & (fun _ => 0%r)]
          (N+1)
          [N-i] (* Loop variant. k0 = this *) 
          ( (* The usual properties *)
             ={i, qs}
          /\ adj d{1} d{2}
          /\ N = size qs{1}
          /\ 0 <= i{1}
                 
             (* Propagation of threshold coupling *)
          /\ t{1}+1 = t{2}
                
             (* Properties about rfrom the paper *)
          /\ (r{1}= r_init => r{2}= r_init)    (* Before we have found a candidate *)
          /\ (r= r_init \/ r < i){1} (* After we found the candidate{1} *)
          /\ (r= r_init \/ r < i){2} (* After we found the candidate{2} *)
          /\ (r{1} = R => r{2} = R)  (* ambient and Hoare level binding *)
          ); 1..5: smt (eps_gt0 N_gt0).
  + by smt.
  (* Note that k is the loop variant *)
  move => k0. wp.

  (* Case on the critical section on the Hoare logic level *)  
  if{1}.
  + rcondt{2} 1;1:by auto; smt().
  (* Case on the ambient level, that we are in the R case *)
  case @[ambient] (k0 = N-R) => Hk0. wp.



  (* Handle obtaining the new query *)
  + seq 1 1 : ((* The usual properties *)
                   ={i, qs} 
                /\ adj d{1} d{2}
                /\ N = size qs{1}
                /\ 0 <= i{1}
                   
                   (* Propagation of threshold coupling *)
                /\ t{1}+1 = t{2}
                 
                   (* Properties from the paper *)
                /\ (r{1} = r_init => r{2} = r_init) 
                /\ (r = r_init \/ r < i){1}
                /\ (r = r_init \/ r < i){2}

                   (* Properties about the q variablw *)
                /\ q{1} = (nth nullQ qs i){1}
                /\ q{2} = (nth nullQ qs i){2}
                 
                   (* Necessary invariants *)
                /\ N-i{1} <= N+1 
                /\ (r = r_init){1} 
                /\ k0 = N - i{1}).
  + by toequiv; auto.

      (* In the then clause we couple the s's *)  
    * exists * t{1}, t{2}; elim * => t1 t2.
      conseq (_ : _ ==> (t1 <= s){1} = (t2 <= s){2}); first smt ().
      lap 1 2; smt (one_sens). (* This was subtle... *)

  + seq 1 1 : ((* The usual properties *)
                   ={i, qs} 
                /\ adj d{1} d{2}
                /\ N = size qs{1}
                /\ 0 <= i{1}
                   
                   (* Propagation of threshold coupling *)
                /\ t{1}+1 = t{2}
                 
                   (* Properties from the paper *)
                /\ (r{1} = r_init => r{2} = r_init) 
                /\ (r = r_init \/ r < i){1}
                /\ (r = r_init \/ r < i){2}

                   (* Properties about the q variable *)
                /\ q{1} = (nth nullQ qs i){1}
                /\ q{2} = (nth nullQ qs i){2}
                 
                   (* Necessary invariants *)
                /\ N-i{1} <= N+1  
                /\ (r = r_init){1} 
                /\ k0 = N - i{1}).
    + by toequiv; auto.

    (* We are in the other case of the ambient cases *)
    * exists* (evalQ d q){1}, (evalQ d q){2}; elim* => e1 e2. wp.

      (* Apply null coupling *)
      lap (e2-e1) 0; smt (one_sens). 

    (* Hoare level else branch *)
  + toequiv. smt (eps_gt0 N_gt0).
    if{2}; auto; smt.
qed.

(*******************************************************************************)

lemma numeric_at_dp : 
  aequiv[[(eps*2%r) & 0%r ] Svt.numeric_above_t ~ Svt.numeric_above_t :
    (adj d{1} d{2} /\ ={qs, tHold} /\ N = size qs{1}) ==> ={res}].
proof.
  proc => //=.

  (* We need to propagative adj d1 d2 through the pointwise equality *)
  seq 1 1 : (={r, qs} /\ adj d{1} d{2}) <[(eps) & 0%r]>.
  + admit. (* TODO: Call tactic for apRHL *)

  conseq <[eps & 0%r]>.
  + smt ().

  lap 0 1.
  + smt (one_sens).
qed.

(*******************************************************************************)

lemma sparse_dp :
  aequiv[[(eps_o_i*(C+1)%r) & 0%r] Svt.sparse ~ Svt.sparse :
     (adj d{1} d{2} /\ ={qs, tHold}) ==> ={res}].
proof.
  proc => //=.
  
  seq 2 2 : (adj d{1} d{2} /\ ={qs, tHold, rs, i} /\ rs{1} = [] /\ i{1} = 0).
  + by toequiv; auto.

  (* Sequential composition for loops *)
  awhile      [(fun k => (eps_o_i)) & (fun _ => 0%r)]
              (C+1)
              [C - i] 
              (    ={i, rs}
                /\ 0 <= i{1}
                /\  adj d{1} d{2});
    1..4: smt (eps_gt0 C_gt0).
  + by rewrite sumr_const; smt.
  + by smt.
  move => k0.

  seq 1 1 : (      r{1} = r{2} (* This is the coupling *)
                /\ ={i, rs} 
                /\ 0 <= i{1} 
                /\ adj d{1} d{2} 
                /\ i{1} < C 
                /\ i{2} < C 
                /\ k0 = C - i{1} 
                /\ C - i{1} <= C + 1) <[eps_o_i & 0%r]>.

  * admit. (* TODO: Use the call tactic for apRHL *)

  toequiv; auto; smt.
qed.

(*******************************************************************************)

section Ex.
declare module A : Adv.

axiom adv_ll : islossless A.getQuery.

lemma above_t_adv_dp : 
  aequiv[[eps & 0%r ] 
    Svt_a(A).adaptive_above_t ~ Svt_a(A).adaptive_above_t :
      (adj d{1} d{2} /\ ={glob A, tHold}) ==> ={res, glob A}].
proof.
  proc => //=.

  (* Handle initialization *)
  seq 2 2 : (adj d{1} d{2} 
    /\ ={glob A, tHold, i, r} 
    /\ i{1} = 0 
    /\ r{1} = r_init).
    by toequiv; auto.
  
  (* couple the thresholds *)
  seq 1 1 : (adj d{1} d{2} 
    /\ ={glob A, tHold, i, r} 
    /\ i{1} = 0 
    /\ r{1} = r_init 
  
       (* Threshold coupling *)
    /\ t{1}+1 = t{2}
      ) <[eps_t & 0%r]>.
  + by lap 1 1.

  (* This in unavoidable as r is manipulated in the inner loop. *)
  pweq ((r, glob A), (r, glob A)).
  + while true (N - i). auto. if. 
     + auto; call adv_ll; skip; progress; try skip; try apply lap_ll; smt ().
          skip; smt ().
          skip; smt ().
  + while true (N - i). auto. if. 
    + auto; call adv_ll; skip; progress; try skip; try apply lap_ll; smt ().
          skip; smt ().
          skip; smt ().
  + move => &1 &2 /(_ (r, glob A){1}); smt.
  move => [R globA].
  
  (* We check on k = N-R as k is the loop variant *)
  conseq <[(bigi predT (fun (k : int) => if k = N-R then 2%r*eps_i else 0%r) 0 (N+1)) & 0%r]>.
  + by rewrite (bigD1_cond_if _ _ _ (N-R)) ?range_uniq big1 /=;1..2:smt.
  
  (* We define r in the outer scope to avoid lifting it using pweq *)
  awhile      [(fun k => if k = N-R then 2%r*eps_i else 0%r) & (fun _ => 0%r)]
              (N+1)
              [N-i] 
              (    (* The usual properties *)
                   ={i} 
                /\ adj d{1} d{2}
                /\ 0 <= i{1}
                   
                   (* Propagation of threshold coupling *)
                /\ t{1}+1 = t{2}
                
                   (* Progress relation on glob A *)
                /\ ((r{1} = r_init \/ r{1} = R) => ={glob A})

                   (* Properties about r and R *)
                /\ (r{1}= r_init => r{2}= r_init)  
                /\ (r= r_init \/ r < i){1} 
                /\ (r= r_init \/ r < i){2} 
                /\ (r{1} = R => r{2} = R)); 
    1..5:smt (eps_gt0 N_gt0).
  + by smt.
  move => k0. wp.

  (* Case on the critical section on the Hoare logic level *)  
  if{1}.
  + rcondt{2} 1;1:by auto=> /#.

  (* Handle obtaining the new query *)
  + seq 1 1 : (    ={i, q} 
                /\ adj d{1} d{2}
                /\ 0 <= i{1}
                   
                   (* Progress relation on glob A *)
                /\ ((r{1} = r_init \/ r{1} = R) => ={glob A})

                   (* Propagation of threshold coupling *)
                /\ t{1}+1 = t{2}
                 
                   (* Properties about r and R *)
                /\ (r{1} = r_init => r{2} = r_init) 
                /\ (r = r_init \/ r < i){1}
                /\ (r = r_init \/ r < i){2}
         
                /\ N-i{1} <= N+1
                /\ (r = r_init){1}
                /\ k0 = N - i{1}).
  +  toequiv; call (_: true); auto.

  (* Case on the ambient level, that we are in the R case *)
  + case @[ambient] (k0 = N-R) => Hk0. wp.

      (* In the then clause we couple the s's *)  
    * exists * t{1}, t{2}; elim * => t1 t2.
      conseq (_ : _ ==> (t1 <= s){1} = (t2 <= s){2}); first smt ().
    * lap 1 2; smt (one_sens). (* This was subtle... *)

    (* We are in the other case of the ambient cases *)
    * exists* (evalQ d q){1}, (evalQ d q){2}; elim* => e1 e2. wp.
      (* Apply null coupling *)
      lap (e2-e1) 0;  smt (one_sens).

    (* Hoare level else branch *)
  + toequiv.
    * smt (eps_gt0 N_gt0).

    if{2}.
    + auto. print adv_ll.
      * call{2} adv_ll; auto => &1 &2 [#]; smt (lap_ll).
      * auto; smt ().
qed.
