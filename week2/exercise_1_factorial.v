
Notation "x + y" := (plus x y)
(at level 50, left associativity)
: nat_scope.
Notation "x - y" := (minus x y)
(at level 50, left associativity)
: nat_scope.
Notation "x * y" := (mult x y)
(at level 40, left associativity)
: nat_scope.

Check ((0 + 2) - 1).
Example test_sign:          ((0 + 2) - 1) = 1.
Proof. simpl. reflexivity.  Qed.

(** **** 练习：1 星, standard (factorial)  
求阶乘 *)
Fixpoint factorial (n:nat) : nat :=
    match n with
    | O => S O
    | S n' => n * factorial n'
    end.

Example test_factorial1:          (factorial 3) = 6.
Proof. simpl. reflexivity.  Qed.
Example test_factorial2:          (factorial 5) =  10 * 12.
Proof. simpl. reflexivity.  Qed.
