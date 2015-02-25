(* Modeling Electrical Circuits
 * CS 6115 Small Project
 * Brittany Nkounkou and Yao Wang
 *
 * 2/24/15: initial circuit and function definitions -BN
 *)

Inductive Circuit : nat -> nat -> Type :=
  | high : Circuit 0 1
  | low  : Circuit 0 1
  | wire : Circuit 1 1
  | not  : Circuit 1 1
  | and  : Circuit 2 1
  | or   : Circuit 2 1
  | xor  : Circuit 2 1
  | nand : Circuit 2 1
  | and3 : Circuit 3 1
  | comp {m n o} : Circuit m n -> Circuit n o -> Circuit m o
  | par  {m n o p} : Circuit m n -> Circuit o p -> Circuit (m + o) (n + p).

Fixpoint area {i o} (C : Circuit i o) : nat :=
  match C with
    | high => 0
    | low  => 0
    | wire => 0
    | not  => 1
    | and  => 1
    | or   => 1
    | xor  => 1
    | nand => 1
    | and3 => 1
    | comp _ _ _ c1 c2 => (area c1) + (area c2)
    | par _ _ _ _ c1 c2 => (area c1) + (area c2)
  end.

Fixpoint delay {i o} (C : Circuit i o) : nat :=
  match C with
    | high => 0
    | low  => 0
    | wire => 0
    | not  => 1
    | and  => 1
    | or   => 1
    | xor  => 1
    | nand => 1
    | and3 => 1
    | comp _ _ _ c1 c2 => (delay c1) + (delay c2)
    | par _ _ _ _ c1 c2 => max (delay c1) (delay c2)
  end.

Require Import Fin Vector.
Import VectorNotations.

Definition BoolVect := t bool.

Fixpoint bv_plus_left {n m} (bv : BoolVect (n + m)) : BoolVect n :=
  match n as n return BoolVect (n + m) -> BoolVect n with
    | O => fun _ => []
    | S n' => fun bv => hd bv :: bv_plus_left (tl bv)
  end bv.

Fixpoint bv_plus_right {n m} (bv : BoolVect (n + m)) : BoolVect m :=
  match n as n return BoolVect (n + m) -> BoolVect m with
    | O => fun bv => bv
    | S n' => fun bv => bv_plus_right (tl bv)
  end bv.

Fixpoint behavior {i o} (C : Circuit i o) : BoolVect i -> BoolVect o :=
  match C with
    | high => fun _ => [true]
    | low  => fun _ => [false]
    | wire => fun bv => bv
    | not  => fun bv => map negb bv
    | and  => fun bv => [fold_right andb bv true]
    | or   => fun bv => [fold_right orb bv false]
    | xor  => fun bv => [xorb bv[@ F1] bv[@ FS F1]]
    | nand => fun bv => [negb (fold_right andb bv true)]
    | and3 => fun bv => [fold_right andb bv true]
    | comp _ _ _ c1 c2 => fun bv => behavior c2 (behavior c1 bv)
    | par _ _ _ _ c1 c2 => fun bv => append (behavior c1 (bv_plus_left bv))
                                            (behavior c2 (bv_plus_right bv))
  end.