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

(** Distance Commutativity **)
Theorem distance_comm : forall (m n : nat) (s d : natprod) (R : noc m n),
  distance m n R s d = distance m n R d s.
Proof.
Admitted.

(** Step Property **)
Theorem step_property : forall (m n : nat) (s d : natprod) (R : noc m n),
  pair_minus (List.hd (0,0) (min_routes m n R s d)) (List.hd (0,0) (List.tl (min_routes m n R s d))) = 1.
Proof.
Admitted.

(** Minimum Routing **)
Theorem min_routing : forall (m n : nat) (s d : natprod) (R : noc m n),
  length(min_routes m n R d s) = distance m n R d s.
Proof.
Admitted.

(** Minimal Power **)
Theorem power_comp : forall (m n : nat) (R : noc m n) (df : dataflow),
  min_power m n R df <= nonmin_power m n R df.
Proof.
Admitted. 

