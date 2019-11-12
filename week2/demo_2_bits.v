Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0).
(* ==> bits B1 B0 B1 B0 : nybble *)

Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).
(* ===> false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)).
(* ===> true : bool *)

Example test_bits1:  (all_zero (bits B1 B0 B1 B0))  = false.
Proof. simpl. reflexivity.  Qed.

Example test_bits2:  (all_zero (bits B0 B0 B0 B0))  = true.
Proof. simpl. reflexivity.  Qed.