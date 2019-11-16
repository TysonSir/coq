(* == *)
Fixpoint eqb (n m : nat) : bool :=
match n with
| O => match m with
       | O => true
       | S m' => false
       end
| S n' => match m with
          | O => false
          | S m' => eqb n' m'
          end
end.

Example test_eqb1:             (eqb 2 2) = true.
Proof. simpl. reflexivity.  Qed.

Example test_eqb2:             (eqb 1 2) = false.
Proof. simpl. reflexivity.  Qed.

(* <= *)
Fixpoint leb (n m : nat) : bool :=
match n with
| O => true
| S n' =>
    match m with
    | O => false
    | S m' => leb n' m'
    end
end.

Example test_leb1:             (leb 2 2) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb2:             (leb 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb3:             (leb 4 2) = false.
Proof. simpl. reflexivity.  Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3':             (4 <=? 2) = false.
Proof. simpl. reflexivity.  Qed.