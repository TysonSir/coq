Module NatPlayground.


Inductive nat : Type :=
  | O
  | S (n : nat).


Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End NatPlayground.


Check (S (S (S (S O)))).
  (* ===> 4 : nat *)

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Compute (minustwo 4).
  (* ===> 2 : nat *)

Compute (pred 4).
  (* ===> 3 : nat *)

Check S.
Check pred.
Check minustwo.


Inductive bool : Type :=
| true
| false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Notation "! x" := (negb x)(at level 70).

(* 偶数 *)
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

  (* 奇数 *)
Definition oddb (n:nat) : bool   :=   ! (evenb n).

Example test_evenb0:    evenb 1 = false.
Proof. simpl. reflexivity.  Qed.

Example test_oddb1:    oddb 1 = true.
Proof. simpl. reflexivity.  Qed.
Example test_oddb2:    oddb 4 = false.
Proof. simpl. reflexivity.  Qed.