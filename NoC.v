(* Formalize On-chip Network
 * CS 6115 Big Project
 * Yao Wang
 *)

Require String.
Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Require Import Arith.

Require Import Init.Datatypes.

Require Import Coq.Lists.List.

Require Import Coq.Lists.Streams.

(* ~~~~~~~~~ DEFINITIONS ~~~~~~~~~ *)
Inductive noc : nat -> nat -> Type :=
  | bus         : noc 0 0
  | rin {n}     : noc 0 n
  | mesh {m n}  : noc m n
  | torus {m n} : noc m n.

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat := 
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat := 
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Fixpoint abs_minus (m n : nat): nat :=
  match m with
    | O => n 
    | S m' => match n with
                | O => m
                | S n' => abs_minus m' n'
              end
  end.

Definition tor_minus (s d m : nat): nat :=
  min (abs_minus (min s d + m) (max s d)) (abs_minus s d).

Eval compute in tor_minus 1 4 5.

Definition distance (m n : nat) (R : noc m n) (s d : natprod): nat :=
  match R with
    | bus => 1
    | rin n => tor_minus (fst s) (fst d) n
    | mesh m n => abs_minus (fst s) (fst d) + abs_minus (snd s) (snd d)
    | torus m n => tor_minus (fst s) (fst d) m + tor_minus (snd s) (snd d) n
  end.

Eval compute in distance 0 4 (rin) (1,0) (4,0).

Eval compute in distance 5 5 (torus) (4,4) (1,1).

Inductive dataflow : Type :=
  _dataflow : natprod -> natprod -> nat -> dataflow.

Inductive link : Type :=
  _link : natprod -> natprod -> nat -> link.

Fixpoint partial_routes_fst (time : nat) (s : natprod) (d : nat) : list natprod :=
  match time with
  | O => cons s nil
  | S time' => if beq_nat (fst s) d then cons s nil
               else
                 if leb d (fst s) then cons s (partial_routes_fst time' (pair ((fst s) - 1) (snd s)) d)
                 else cons s (partial_routes_fst time' (pair ((fst s) + 1) (snd s)) d)
  end.

Fixpoint partial_routes_snd (time : nat) (s : natprod) (d : nat) : list natprod :=
  match time with
  | O => cons s nil
  | S time' => if beq_nat (snd s) d then cons s nil
               else
                 if leb d (snd s) then cons s (partial_routes_snd time' (pair (fst s) ((snd s) - 1)) d)
                 else cons s (partial_routes_snd time' (pair (fst s) ((snd s) + 1)) d)
  end.

Eval compute in partial_routes_fst 10 (4,0) 1.
Eval compute in partial_routes_snd 10 (1,5) 10.

Definition min_routes (m n : nat) (R : noc m n) (s d : natprod) : list natprod :=
  match R with
    | bus => cons s (cons d nil)
    | rin n => 
      if beq_nat (tor_minus (fst s) (fst d) n) (abs_minus (fst s) (fst d)) then
          partial_routes_fst n s (fst d)
      else
        if leb (fst s) (fst d) then
          (partial_routes_fst n s 1) ++ (partial_routes_fst n (pair n 0) (fst d))
        else
          (partial_routes_fst n s n) ++ (partial_routes_fst n (pair 1 0) (fst d))
    | mesh m n => 
      (partial_routes_fst m s (fst d)) ++ (tail (partial_routes_snd n (pair (fst d) (snd s)) (snd d)))
    | torus m n =>
      if beq_nat (tor_minus (fst s) (fst d) m) (abs_minus (fst s) (fst d)) then
        if beq_nat (tor_minus (snd s) (snd d) n) (abs_minus (snd s) (snd d)) then
          (partial_routes_fst m s (fst d)) ++ (tail (partial_routes_snd n (pair (fst d) (snd s)) (snd d)))
        else
          if (leb (snd s) (snd d)) then
            (partial_routes_fst m s (fst d)) ++ 
              (tail ((partial_routes_snd n (pair (fst d) (snd s)) 1) ++ 
                      (partial_routes_snd n (pair (fst d) n) (snd d))))
          else
            (partial_routes_fst m s (fst d)) ++
              (tail ((partial_routes_snd n (pair (fst d) (snd s)) n) ++
                      (partial_routes_snd n (pair (fst d) 1) (snd d))))
      else
        if beq_nat (tor_minus (snd s) (snd d) n) (abs_minus (snd s) (snd d)) then
          if (leb (fst s) (fst d)) then
            ((partial_routes_fst m s 1) ++ (partial_routes_fst m (pair n (snd s)) (fst d))) ++
              (tail (partial_routes_snd n (pair (fst d) (snd s)) (snd d)))
          else
            ((partial_routes_fst m s n) ++ (partial_routes_fst m (pair 1 (snd s)) (fst d))) ++
              (tail (partial_routes_snd n (pair (fst d) (snd s)) (snd d)))
        else
          if (leb (fst s) (fst d)) then
            if (leb (snd s) (snd d)) then
              ((partial_routes_fst m s 1) ++ (partial_routes_fst m (pair n (snd s)) (fst d))) ++
                (tail ((partial_routes_snd n (pair (fst d) (snd s)) 1) ++ 
                      (partial_routes_snd n (pair (fst d) n) (snd d))))
            else
              ((partial_routes_fst m s 1) ++ (partial_routes_fst m (pair n (snd s)) (fst d))) ++
                (tail ((partial_routes_snd n (pair (fst d) (snd s)) n) ++
                      (partial_routes_snd n (pair (fst d) 1) (snd d))))
          else
             if (leb (snd s) (snd d)) then
              ((partial_routes_fst m s n) ++ (partial_routes_fst m (pair 1 (snd s)) (fst d))) ++
                (tail ((partial_routes_snd n (pair (fst d) (snd s)) 1) ++ 
                      (partial_routes_snd n (pair (fst d) n) (snd d))))
            else
              ((partial_routes_fst m s n) ++ (partial_routes_fst m (pair 1 (snd s)) (fst d))) ++
                (tail ((partial_routes_snd n (pair (fst d) (snd s)) n) ++
                      (partial_routes_snd n (pair (fst d) 1) (snd d))))
  end.

(** tests for minimal routes **)
Eval compute in min_routes 0 0 bus (0,0) (1,1).

Eval compute in min_routes 0 5 rin (1,0) (5,0).
Eval compute in min_routes 0 5 rin (1,0) (2,0).
Eval compute in min_routes 0 5 rin (5,0) (1,0).
Eval compute in min_routes 0 5 rin (2,0) (1,0).

Eval compute in min_routes 5 5 mesh (1,4) (5,1).
Eval compute in min_routes 5 5 mesh (1,4) (5,4).

Eval compute in min_routes 5 5 torus (2,4) (5,1).
Eval compute in min_routes 5 5 torus (2,4) (1,2).
Eval compute in min_routes 5 5 torus (2,4) (1,5).
Eval compute in min_routes 5 5 torus (2,4) (5,5).

Definition nonmin_routes (m n : nat) (R : noc m n) (s d : natprod) : list natprod :=
  match R with
    | bus => cons s (cons d nil)
    | rin n => 
      if leb (fst s) (fst d) then
        (partial_routes_fst n s (fst d))
      else
        (partial_routes_fst n s n) ++ (partial_routes_fst n (pair 1 0) (fst d))
    | mesh m n => 
      (partial_routes_fst m s m) ++ (tail (partial_routes_snd n (pair m (snd s)) (snd d))) ++
        (tail (partial_routes_fst m (pair m (snd d)) (fst d)))
    | torus m n =>
        (partial_routes_fst m s (fst d)) ++ (tail (partial_routes_snd n (pair (fst d) (snd s)) (snd d)))
  end.

Definition nonmin_distance (m n : nat) (R : noc m n) (s d : natprod) : nat :=
  match R with
    | bus => 1
    | rin n => abs_minus (fst s) (fst d)
    | mesh m n => abs_minus (fst s) m + abs_minus (snd s) (snd d) + abs_minus (fst d) m
    | torus m n => abs_minus (fst s) (fst d) + abs_minus (snd s) (snd d)
  end.

(** tests for non minimal routes **)
Eval compute in nonmin_routes 0 0 bus (0,0) (1,1).

Eval compute in nonmin_routes 0 5 rin (1,0) (5,0).
Eval compute in nonmin_routes 0 5 rin (1,0) (2,0).
Eval compute in nonmin_routes 0 5 rin (5,0) (1,0).
Eval compute in nonmin_routes 0 5 rin (2,0) (1,0).

Eval compute in nonmin_routes 5 5 mesh (1,4) (4,1).
Eval compute in nonmin_routes 5 5 mesh (1,4) (2,2).

Eval compute in nonmin_routes 5 5 torus (2,4) (5,1).
Eval compute in nonmin_routes 5 5 torus (2,4) (1,2).
Eval compute in nonmin_routes 5 5 torus (2,4) (1,5).
Eval compute in nonmin_routes 5 5 torus (2,4) (5,5).

Definition min_power (m n : nat) (R : noc m n) (df : dataflow) : nat :=
  match df with
    | _dataflow s d r => (length (min_routes m n R s d) - 1) * r
  end.

Eval compute in min_power 0 0 bus (_dataflow (1,1) (4,4) 15).
Eval compute in min_power 0 5 rin (_dataflow (1,0) (5,0) 30).
Eval compute in min_power 5 5 mesh (_dataflow (1,1) (4,4) 20).
Eval compute in min_power 5 5 torus (_dataflow (1,1) (4,4) 25).

Definition nonmin_power (m n : nat) (R : noc m n) (df : dataflow) : nat :=
  match df with
    | _dataflow s d r => (length (nonmin_routes m n R s d) - 1) * r
  end.

CoFixpoint repeat (a:bool) : Stream bool :=
Cons a (repeat (negb a)).

Eval compute in repeat true.
Eval compute in hd (tl (repeat true)).

Definition ref_stream := repeat true.

Definition nondet_routes (m n : nat) (t : nat) (R : noc m n) (s d : natprod) : list natprod :=
  match R with
    | bus => cons s (cons d nil)
    | rin n =>
      if Str_nth t ref_stream then
        if leb (fst s) (fst d) then
          (partial_routes_fst n s (fst d))
        else
          (partial_routes_fst n s n) ++ (partial_routes_fst n (pair 1 0) (fst d))
      else
        if leb (fst s) (fst d) then
          (partial_routes_fst n s 1) ++ (partial_routes_fst n (pair n 0) (fst d))
        else
          (partial_routes_fst n s (fst d))
    | mesh m n => 
      if Str_nth t ref_stream then
        (partial_routes_fst m s (fst d)) ++ (tail (partial_routes_snd n (pair (fst d) (snd s)) (snd d)))
      else
        (partial_routes_snd n s (snd d)) ++ (tail (partial_routes_fst n (pair (fst s) (snd d)) (fst d)))
    | torus m n =>
      if Str_nth t ref_stream then
        min_routes m n torus s d
      else
        if beq_nat (tor_minus (fst s) (fst d) m) (abs_minus (fst s) (fst d)) then
          if beq_nat (tor_minus (snd s) (snd d) n) (abs_minus (snd s) (snd d)) then
            (partial_routes_snd m s (snd d)) ++ (tail (partial_routes_fst n (pair (fst s) (snd d)) (fst d)))
          else
            if (leb (snd s) (snd d)) then
              (partial_routes_snd n s 1) ++ (partial_routes_snd n (pair (fst s) 1) (snd d)) ++
                (tail (partial_routes_fst m (pair (fst s) (snd d)) (fst d)))
            else
              (partial_routes_snd n s n) ++ (partial_routes_snd n (pair (fst s) n) (snd d)) ++
                (tail (partial_routes_fst m (pair (fst s) (snd d)) (fst d)))
        else
          if beq_nat (tor_minus (snd s) (snd d) n) (abs_minus (snd s) (snd d)) then
            if (leb (fst s) (fst d)) then
              (partial_routes_snd n s (snd d)) ++ 
                (tail ((partial_routes_fst m (pair (fst s) (snd d)) 1) ++
                      (partial_routes_fst m (pair n (snd d)) (fst d))))
            else
              (partial_routes_snd n s (snd d)) ++ 
                (tail ((partial_routes_fst m (pair (fst s) (snd d)) m) ++
                      (partial_routes_fst m (pair 1 (snd d)) (fst d))))
          else
            if (leb (fst s) (fst d)) then
              if (leb (snd s) (snd d)) then
                ((partial_routes_snd n s 1) ++ (partial_routes_snd m (pair (fst s) 1) (snd d))) ++
                  (tail ((partial_routes_fst m (pair (fst s) (snd d)) 1) ++
                        (partial_routes_fst m (pair 1 (snd d)) (fst d))))
              else
                ((partial_routes_snd n s n) ++ (partial_routes_snd m (pair (fst s) n) (snd d))) ++
                  (tail ((partial_routes_fst m (pair (fst s) (snd d)) 1) ++
                        (partial_routes_fst m (pair 1 (snd d)) (fst d))))
            else
              if (leb (snd s) (snd d)) then
                ((partial_routes_snd n s 1) ++ (partial_routes_snd m (pair (fst s) 1) (snd d))) ++
                  (tail ((partial_routes_fst m (pair (fst s) (snd d)) m) ++
                        (partial_routes_fst m (pair m (snd d)) (fst d))))
              else
                ((partial_routes_snd n s n) ++ (partial_routes_snd m (pair (fst s) n) (snd d))) ++
                  (tail ((partial_routes_fst m (pair (fst s) (snd d)) m) ++
                        (partial_routes_fst m (pair m (snd d)) (fst d))))
end.

(** Tests for nondeterministic routing **)
Eval compute in (nondet_routes 0 5 1 rin (1,0) (5,0)).
Eval compute in (nondet_routes 0 5 2 rin (1,0) (5,0)).
Eval compute in (nondet_routes 5 5 1 mesh (1,2) (4,3)).
Eval compute in (nondet_routes 5 5 2 mesh (1,2) (4,3)).
Eval compute in (nondet_routes 5 5 1 torus (1,2) (4,4)).
Eval compute in (nondet_routes 5 5 2 torus (1,2) (4,4)).

Eval compute in (List.length (min_routes 5 5 mesh (1,2) (4,4))).
Eval compute in (List.length nil).

Fixpoint mapping (m n : nat) (R : noc m n) (dfs : list dataflow) (l : nat) : list (list natprod) :=
  match l with
    | O => nil
    | S l' => match (List.hd (_dataflow (0,0) (1,1) 10) dfs) with
                | _dataflow s d r => let rt := min_routes m n R s d in cons rt (mapping m n R (List.tl dfs) l')
              end
  end.

Definition dataflows := cons (_dataflow (1,1) (3,3) 10) (cons (_dataflow (2,2) (4,4) 20) nil).

Eval compute in (mapping 5 5 mesh dataflows 2).

Definition pair_minus (s d : natprod): nat :=
  (abs_minus (fst s) (fst d)) + (abs_minus (snd s) (snd d)).

(** Properties **)

Theorem abs_minus_theorem : forall (m n : nat),
  abs_minus m n = abs_minus n m.
Proof.
  intros m.
  induction m as [| m'].
  Case "m = O". intros n. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". simpl. reflexivity.
  Case "m = S m'". intros n. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". simpl. apply IHm'.
Qed. 

Theorem tor_minus_theorem : forall (s d n : nat),
  tor_minus s d n = tor_minus d s n.
Proof.
  intros s d n.
  unfold tor_minus.
  destruct (le_lt_dec s d).
    SCase "s <= d".
      rewrite (min_l s d).
      rewrite (max_r s d).
      rewrite (min_r d s).
      rewrite (max_l d s).
      rewrite (abs_minus_theorem s d). reflexivity.
      apply l. apply l. apply l. apply l.
    SCase "s > d".
      rewrite (min_r s d).
      rewrite (max_l s d).
      rewrite (min_l d s).
      rewrite (max_r d s).
      rewrite (abs_minus_theorem s d). reflexivity.
      apply lt_le_weak in l. apply l.  apply lt_le_weak in l. apply l. 
      apply lt_le_weak in l. apply l.  apply lt_le_weak in l. apply l.
Qed.
 
(** Distance Commutativity **)
Theorem distance_comm : forall (m n : nat) (s d : natprod) (R : noc m n),
  distance m n R s d = distance m n R d s.
Proof.
  intros m n s d R.
  destruct R.
  Case "R = bus". 
    reflexivity.
  Case "R = rin".
    simpl. apply tor_minus_theorem.
  Case "R = mesh".
    simpl. rewrite (abs_minus_theorem (fst s) (fst d)). 
    rewrite (abs_minus_theorem (snd s) (snd d)). reflexivity.
  Case "R = torus".
    simpl. rewrite (tor_minus_theorem (fst s) (fst d) m).
    rewrite (tor_minus_theorem (snd s) (snd d) n). reflexivity.
Qed.

(** Partial Step Property **)
Theorem partial_step : forall (time d : nat) (s : natprod),
  pair_minus (List.hd (0,0) (partial_routes_fst time s d)) (List.hd (0,0) (List.tl (partial_routes_fst time s d))) = 1.
Proof.
  intros time d s.
  simpl. admit.
Qed.
  

(** Step Property **)
Theorem step_property : forall (m n : nat) (s d : natprod) (R : noc m n),
  pair_minus (List.hd (0,0) (min_routes m n R s d)) (List.hd (0,0) (List.tl (min_routes m n R s d))) = 1.
Proof.
  intros m n s d R.
  destruct R.
  Case "R = bus". admit.
  Case "R = rin". admit.
  Case "R = mesh". 
    admit.
  Case "R = torus". admit.
Qed.

Theorem partial_routing_fst : forall (time : nat) (s : natprod) (d : nat),
  length(partial_routes_fst time s d)  = (abs_minus (fst s) d) + 1.
Proof.
  intros time s d.
  destruct (le_lt_dec (fst s) d).
  Case "fst s < d". simpl. admit. admit.
Qed.  

Theorem partial_routing_snd : forall (time : nat) (s : natprod) (d : nat),
  length(partial_routes_snd time s d)  = (abs_minus (snd s) d) + 1.
Proof.
  Admitted.

Variable A : Type.

Theorem length_tl : forall (l : list natprod),
  length l > 0 -> length (tail l) = length l - 1.
Proof.
  intros l.
  destruct l.
  Case "nil".
    intro H.
    inversion H.
  Case "a::l".
    intro H.
    simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Theorem plus_permute_3 : forall (n m p : nat),
  n + m + p = n + p + m.
Proof.
  Admitted.

Theorem plus_minus_3 : forall (n m : nat),
  n + m - m = n.
Proof.
  Admitted.

(** Minimum Routing **)
Theorem min_routing : forall (m n : nat) (s d : natprod) (R : noc m n),
  length(min_routes m n R d s)  = distance m n R d s + 1.
Proof.
  intros m n s d R.
  destruct R.
  Case "R = bus". simpl. reflexivity.
  Case "R = rin". 
    simpl. admit.
  Case "R = mesh".
    simpl. rewrite app_length. rewrite partial_routing_fst. 
    rewrite length_tl.
    rewrite partial_routing_snd.
    simpl. rewrite plus_permute_3. rewrite plus_minus_3. reflexivity.
    rewrite partial_routing_snd. simpl. rewrite plus_comm. apply lt_plus_trans.
    rewrite nat_compare_lt. simpl. reflexivity.
  Case "R = torus".
    admit.
Qed.

Theorem nonmin_routing : forall (m n : nat) (s d : natprod) (R : noc m n),
  length(nonmin_routes m n R d s) = nonmin_distance m n R d s + 1.
Proof.
  Admitted.

Theorem abs_minus_trans : forall (m n : nat),
  m <= n -> abs_minus m n = n - m.
Proof.
  Admitted.

(** Minimal Power **)
Theorem power_comp : forall (m n : nat) (R : noc m n) (s d : natprod) (r : nat),
  (fst s) <= m -> (fst d) <=  m -> min_power m n R (_dataflow s d r) <= nonmin_power m n R (_dataflow s d r).
Proof.
  intros m n R s d r.
  intros H0 H1.
  destruct R.
  Case "R = bus". 
    simpl. reflexivity.
  Case "R = rin".
    unfold min_power. rewrite -> min_routing. admit.
  Case "R = mesh".
    unfold min_power. rewrite min_routing.
    unfold nonmin_power. rewrite nonmin_routing. 
    apply mult_le_compat_r.
    rewrite plus_minus_3. rewrite plus_minus_3.
    simpl. rewrite plus_permute_3.
    apply plus_le_compat_r.
    destruct (le_lt_dec (fst s) (fst d)).
      SCase "fst s <= fst d".
        repeat (rewrite abs_minus_trans).
        assert (H: fst d - fst s <= m - fst s).
          SSCase "Proof of assertion". apply minus_le_compat_r.
        assumption. apply le_plus_trans. apply H. apply H1. apply H0. apply l.
      SCase "fst d < fst s".
        rewrite abs_minus_theorem.
        repeat (rewrite abs_minus_trans). rewrite plus_comm.
        assert (H: fst s - fst d <= m - fst d).
          SSCase "Proof of assertion". apply minus_le_compat_r.
        assumption. apply le_plus_trans. apply H. apply H1. apply H0. apply lt_le_weak. apply l.
  Case "R = torus".
    admit.
Qed.

