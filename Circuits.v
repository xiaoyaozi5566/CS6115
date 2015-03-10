(* Modeling Electrical Circuits
 * CS 6115 Small Project
 * Brittany Nkounkou and Yao Wang
 *)



Require Import Vector.
Import VectorNotations.

Require Import FunctionalExtensionality.

Require Import Plus.
Require Import Arith.

Require String. Open Scope string_scope.

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



(* ~~~~~~~ DEFINITIONS ~~~~~~~ *)

Inductive Circuit : nat -> nat -> Type :=
  | none : Circuit 0 0
  | high : Circuit 0 1
  | low  : Circuit 0 1
  | wire : Circuit 1 1
  | split: Circuit 1 2
  | inv  : Circuit 1 1
  | buf  : Circuit 1 1
  | and  : Circuit 2 1
  | or   : Circuit 2 1
  | xor  : Circuit 2 1
  | nand : Circuit 2 1
  | nor  : Circuit 2 1
  | xnor : Circuit 2 1
  | and3 : Circuit 3 1
  | comp {m n o} : Circuit m n -> Circuit n o -> Circuit m o
  | par  {m n o p} : Circuit m n -> Circuit o p -> Circuit (m + o) (n + p).

Fixpoint area {i o} (C : Circuit i o) : nat :=
  match C with
    | none => 0
    | high => 0
    | low  => 0
    | wire => 0
    | split=> 0
    | inv  => 108
    | buf  => 144
    | and  => 216
    | or   => 216
    | xor  => 360
    | nand => 144
    | nor  => 144
    | xnor => 396
    | and3 => 252
    | comp _ _ _ c1 c2 => (area c1) + (area c2)
    | par _ _ _ _ c1 c2 => (area c1) + (area c2)
  end.

Fixpoint delay {i o} (C : Circuit i o) : nat :=
  match C with
    | none => 0
    | high => 0
    | low  => 0
    | wire => 0
    | split=> 0
    | inv  => 23
    | buf  => 66
    | and  => 53
    | or   => 62
    | xor  => 88
    | nand => 31
    | nor  => 50
    | xnor => 89
    | and3 => 68
    | comp _ _ _ c1 c2 => (delay c1) + (delay c2)
    | par _ _ _ _ c1 c2 => max (delay c1) (delay c2)
  end.

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
    | none => fun _ => []
    | high => fun _ => [true]
    | low  => fun _ => [false]
    | wire => fun bv => bv
    | split=> fun bv => [hd bv; hd bv]
    | inv  => fun bv => map negb bv
    | buf  => fun bv => bv
    | and  => fun bv => [fold_right andb bv true]
    | or   => fun bv => [fold_right orb bv false]
    | xor  => fun bv => [xorb (hd bv) (hd (tl bv))]
    | nand => fun bv => [negb (fold_right andb bv true)]
    | nor  => fun bv => [negb (fold_right orb bv false)]
    | xnor => fun bv => [negb (xorb (hd bv) (hd (tl bv)))]
    | and3 => fun bv => [fold_right andb bv true]
    | comp _ _ _ c1 c2 => fun bv => behavior c2 (behavior c1 bv)
    | par _ _ _ _ c1 c2 => fun bv => append (behavior c1 (bv_plus_left bv))
                                            (behavior c2 (bv_plus_right bv))
  end.



(* ~~~~~~~ ASSOCIATIVITY ~~~~~~~ *)

Theorem area_comp_assoc : forall (m n o p : nat) (A : Circuit m n) (B : Circuit n o) (C : Circuit o p),
  area (comp A (comp B C)) = area (comp (comp A B) C).
Proof.
  intros m n o p A B C.
  simpl.
  rewrite plus_assoc.
  reflexivity.
Qed.

Theorem area_par_assoc : forall (m n o p q r : nat) (A : Circuit m n) (B : Circuit o p) (C : Circuit q r),
  area (par A (par B C)) = area (par (par A B) C).
Proof.
  intros m n o p q r A B C.
  simpl.
  rewrite plus_assoc.
  reflexivity.
Qed.

Theorem delay_comp_assoc : forall (m n o p : nat) (A : Circuit m n) (B : Circuit n o) (C : Circuit o p),
  delay (comp A (comp B C)) = delay (comp (comp A B) C).
Proof. 
  intros m n o p A B C.
  simpl.
  rewrite plus_assoc.
  reflexivity.
Qed.

Theorem delay_par_assoc : forall (m n o p q r : nat) (A : Circuit m n) (B : Circuit o p) (C : Circuit q r),
  delay (par A (par B C)) = delay (par (par A B) C).
Proof.
  intros m n o p q r A B C.
  simpl.
  destruct (le_lt_dec (delay B) (delay C)).
    rewrite (max_r (delay B) (delay C)).
    destruct (le_lt_dec (delay A) (delay B)).
      rewrite (max_r (delay A) (delay B)).
      rewrite (max_r (delay A) (delay C)).
      rewrite (max_r (delay B) (delay C)).
      reflexivity. apply l. apply le_trans with (delay B). apply l0. apply l. apply l0.
      destruct (le_lt_dec (delay A) (delay C)).
        rewrite (max_r (delay A) (delay C)).
        rewrite (max_l (delay A) (delay B)).
        rewrite (max_r (delay A) (delay C)).
        reflexivity. apply l1. apply lt_le_weak in l0. apply l0. apply l1.
        rewrite (max_l (delay A) (delay C)).
        rewrite (max_l (delay A) (delay B)).
        rewrite (max_l (delay A) (delay C)).
        reflexivity. apply lt_le_weak in l1. apply l1. apply lt_le_weak in l0. apply l0. 
        apply lt_le_weak in l1. apply l1. apply l.
    rewrite (max_l (delay B) (delay C)).
    destruct (le_lt_dec (delay A) (delay B)).
      rewrite (max_r (delay A) (delay B)).
      rewrite (max_l (delay B) (delay C)).
      reflexivity. apply lt_le_weak in l. apply l. apply l0.
      rewrite (max_l (delay A) (delay B)).
      rewrite (max_l (delay A) (delay C)).
      reflexivity. apply lt_le_weak in l. apply lt_le_weak in l0. apply le_trans with (delay B). apply l. apply l0.
      apply lt_le_weak in l0. apply l0. apply lt_le_weak in l. apply l.
Qed.
  

Theorem behavior_comp_assoc : forall (m n o p : nat) (A : Circuit m n) (B : Circuit n o) (C : Circuit o p),
  behavior (comp A (comp B C)) = behavior (comp (comp A B) C).
Proof.
  reflexivity.
Qed.

Theorem behavior_par_assoc : forall (m n o p q r : nat) (A : Circuit m n) (B : Circuit o p) (C : Circuit q r),
  behavior (par A (par B C)) = eq_rect_r (fun x => BoolVect x -> _)
                                         (eq_rect_r (fun x => _ -> BoolVect x)
                                                    (behavior (par (par A B) C))
                                                    (plus_assoc _ _ _))
                                         (plus_assoc _ _ _).
Proof. Admitted.



(* ~~~~~~~ IDENTITY ELEMENTS ~~~~~~~ *)

Fixpoint par_wire (n : nat) : Circuit n n :=
  match n with
    | O => none
    | S n' => par wire (par_wire n')
  end.

Theorem area_par_wire : forall (n : nat),
  area (par_wire n) = 0.
Proof. 
  intros n.
  induction n as [|n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. apply IHn'.
Qed.

Theorem area_comp_ident_l : forall (m n : nat) (A : Circuit m n),
  area (comp (par_wire m) A) = area A.
Proof. 
  intros m n A. 
  simpl. rewrite -> area_par_wire. reflexivity.
Qed.

Theorem area_comp_ident_r : forall (m n : nat) (A : Circuit m n),
  area (comp A (par_wire n)) = area A.
Proof.
  intros m n A.
  simpl. rewrite -> area_par_wire.
  rewrite -> plus_comm. reflexivity.
Qed.

Theorem area_par_ident_l : forall (m n : nat) (A : Circuit m n),
  area (par none A) = area A.
Proof. 
  intros m n A.
  reflexivity.
Qed.

Theorem area_par_ident_r : forall (m n : nat) (A : Circuit m n),
  area (par A none) = area A.
Proof. 
  intros m n A.
  simpl.  rewrite -> plus_comm.
  reflexivity.
Qed.

Theorem delay_par_wire : forall (n : nat),
  delay (par_wire n) = 0.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. apply IHn'.
Qed.

Theorem delay_comp_ident_l : forall (m n : nat) (A : Circuit m n),
  delay (comp (par_wire m) A) = delay A.
Proof. 
  intros m n A.
  simpl. rewrite -> delay_par_wire. reflexivity.
Qed.

Theorem delay_comp_ident_r : forall (m n : nat) (A : Circuit m n),
  delay (comp A (par_wire n)) = delay A.
Proof. 
  intros m n A.
  simpl. rewrite -> delay_par_wire.
  rewrite -> plus_comm.  reflexivity.
Qed.

Theorem delay_par_ident_l : forall (m n : nat) (A : Circuit m n),
  delay (par none A) = delay A.
Proof.
  intros m n A.
  reflexivity.
Qed.

Theorem delay_par_ident_r : forall (m n : nat) (A : Circuit m n),
  delay (par A none) = delay A.
Proof. 
  intros m n A.
  simpl. apply max_l.
  apply le_0_n.
Qed.

Theorem behavior_comp_ident_l : forall (m n : nat) (A : Circuit m n),
  behavior (comp (par_wire m) A) = behavior A.
Proof. Admitted.

Theorem behavior_comp_ident_r : forall (m n : nat) (A : Circuit m n),
  behavior (comp A (par_wire n)) = behavior A.
Proof. Admitted.

Theorem behavior_par_ident_l : forall (m n : nat) (A : Circuit m n),
  behavior (par none A) = behavior A.
Proof. Admitted.

Theorem behavior_par_ident_r : forall (m n : nat) (A : Circuit m n),
  behavior (par A none) = eq_rect_r (fun x => BoolVect x -> _)
                                    (eq_rect_r (fun x => _ -> BoolVect x)
                                               (behavior A)
                                               (plus_0_r _))
                                    (plus_0_r _).
Proof. Admitted.



(* ~~~~~~~ COMMUTATIVITY ~~~~~~~ *)

Theorem area_comp_comm : forall (m n : nat) (A : Circuit m n) (B : Circuit n m),
  area (comp A B) = area (comp B A).
Proof.
  intros m n A B.
  simpl.
  apply plus_comm.
Qed.

Theorem area_par_comm : forall (m n o p : nat) (A : Circuit m n) (B : Circuit o p),
  area (par A B) = area (par B A).
Proof.
  intros m n o p A B.
  simpl.
  apply plus_comm.
Qed.

Theorem delay_comp_comm : forall (m n : nat) (A : Circuit m n) (B : Circuit n m),
  delay (comp A B) = delay (comp B A).
Proof.
  intros m n A B.
  simpl.
  apply plus_comm.
Qed.

Theorem delay_par_comm : forall (m n o p : nat) (A : Circuit m n) (B : Circuit o p),
  delay (par A B) = delay (par B A).
Proof. 
  intros m n o p A B.
  simpl.
  destruct (le_lt_dec (delay A) (delay B)).
  rewrite max_r. rewrite max_l. reflexivity. apply l. apply l.
  rewrite max_l. rewrite max_r. reflexivity. apply lt_le_weak. apply l. apply lt_le_weak. apply l.
Qed.



(* ~~~~~~~ DISTRIBUTIVITY ~~~~~~~ *)

Theorem delay_distr_l : forall (m n o p q : nat) (A : Circuit m (n + p)) (B : Circuit n o) (C : Circuit p q),
  delay (comp A (par B C)) = delay (par (comp A (par B (par_wire p))) (comp A (par (par_wire n) C))).
Proof. Admitted.

Theorem delay_distr_r : forall (m n o p q : nat) (B : Circuit m n) (C : Circuit o p) (A : Circuit (n + p) q),
  delay (comp (par B C) A) = delay (par (comp (par B (par_wire p)) A) (comp (par (par_wire n) C) A)).
Proof. Admitted.



(* ~~~~~~~ ANNIHILATION ~~~~~~~ *)
(* ~~~~~~~ is this true? I'm not sure what none does. ~~~~~~~~ *)

Theorem area_anni_l : forall (n : nat) (A : Circuit 0 n),
  area (comp none A) = area none.
Proof. Admitted.

Theorem area_anni_r : forall (n : nat) (A : Circuit n 0),
  area (comp A none) = area none.
Proof. Admitted.

Theorem delay_anni_l : forall (n : nat) (A : Circuit 0 n),
  delay (comp none A) = area none.
Proof. Admitted.

Theorem delay_anni_r : forall (n : nat) (A : Circuit n 0),
  delay (comp A none) = area none.
Proof. Admitted.



(* ~~~~~~~ IDEMPOTENCE ~~~~~~~ *)

Theorem delay_par_idemp : forall (m n : nat) (A : Circuit m n),
  delay (par A A) = delay A.
Proof. 
  intros m n A.
  simpl. rewrite max_l. reflexivity. reflexivity.
Qed.

(* ~~~~~~~ I DON'T KNOW WHAT TO CALL THIS. IT'S KIND OF LIKE TRANSPOSITION. MANHATTAN EQUIVALENCE? ~~~~~~~ *)
(* TODO : generalize the theorems below to account for any finite number of rows/column
        : area_manhattan, comp_manhattan, behavior_manhattan *)

Theorem area_comp_par : forall (m n o p q r : nat) (A : Circuit m n) (B : Circuit n o) (C : Circuit p q) (D : Circuit q r),
  area (par (comp A B) (comp C D)) = area (comp (par A C) (par B D)).
Proof. 
  intros m n o p q r A B C D.
  simpl. apply plus_permute_2_in_4.
Qed.

(* ~~~~~~ This theorem seems to be wrong ~~~~~~ *)
Theorem delay_comp_par : forall (m n o p q r : nat) (A : Circuit m n) (B : Circuit n o) (C : Circuit p q) (D : Circuit q r),
  delay (par (comp A B) (comp C D)) = delay (comp (par A C) (par B D)).
Proof. Admitted.

Theorem behavior_comp_par : forall (m n o p q r : nat) (A : Circuit m n) (B : Circuit n o) (C : Circuit p q) (D : Circuit q r),
  behavior (par (comp A B) (comp C D)) = behavior (comp (par A C) (par B D)).
Proof. Admitted.



(* ~~~~~~~ FACTS ~~~~~~~ *)

Theorem nand_vs_and_inv : behavior nand = behavior (comp and inv) /\ area nand < area (comp and inv) /\ delay nand < delay (comp and inv).
Proof. Admitted.

Theorem nand_minimal_area : ~ exists (C : Circuit 2 1), behavior C = behavior nand /\ area C < area nand.
Proof. Admitted.

Theorem nand_minimal_delay : ~ exists (C : Circuit 2 1), behavior C = behavior nand /\ delay C < delay nand.
Proof. Admitted.
