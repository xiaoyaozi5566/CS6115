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

Definition distance {m n} (R : noc m n) (s d : natprod): nat :=
  match R with
    | bus => 1
    | rin n => abs_minus (fst s) (fst d)
    | mesh m n => abs_minus (fst s) (fst d) + abs_minus (snd s) (snd d)
    | torus m n => abs_minus (fst s) (fst d) + abs_minus (snd s) (snd d)
  end.

Eval compute in distance (rin) (1,0) (3,0).
  
