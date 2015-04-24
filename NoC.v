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

Definition routes (m n : nat) (R : noc m n) (s d : natprod) : list natprod :=
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

(** tests for routes **)
Eval compute in routes 0 0 bus (0,0) (1,1).

Eval compute in routes 0 5 rin (1,0) (5,0).
Eval compute in routes 0 5 rin (1,0) (2,0).
Eval compute in routes 0 5 rin (5,0) (1,0).
Eval compute in routes 0 5 rin (2,0) (1,0).

Eval compute in routes 5 5 mesh (1,4) (5,1).
Eval compute in routes 5 5 mesh (1,4) (5,4).

Eval compute in routes 5 5 torus (2,4) (5,1).
Eval compute in routes 5 5 torus (2,4) (1,2).
Eval compute in routes 5 5 torus (2,4) (1,5).
Eval compute in routes 5 5 torus (2,4) (5,5).
