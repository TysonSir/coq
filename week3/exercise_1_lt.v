
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

Fixpoint leb (n m : nat) : bool :=
match n with
| O => true
| S n' =>
    match m with
    | O => false
    | S m' => leb n' m'
    end
end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Notation "x && y" := (andb x y).
Notation "! x" := (negb x)(at level 70).

(** **** 练习：1 星, standard (ltb)  
[ltb] 函数检查自然数间的小于关系，以布尔值表示。*)
Definition ltb (n m : nat) : bool :=
match n,m with
| S n', S m' => (!(n =? m)) && (n <=? m)
| O, O => false
| S n', O => false
| O, S m' => true
end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1:             (ltb 2 2) = false.
Proof. simpl. reflexivity.  Qed.
Example test_ltb2:             (ltb 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_ltb3:             (ltb 4 2) = false.
Proof. simpl. reflexivity.  Qed.
Example test_ltb4:             0 <? 2 = true.
Proof. simpl. reflexivity.  Qed.
Example test_ltb5:             4 <? 0 = false.
Proof. simpl. reflexivity.  Qed.
Example test_ltb6:             0 <? 0 = false.
Proof. simpl. reflexivity.  Qed.