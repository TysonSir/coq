(** **** bool 基本定义 *)  
Inductive bool : Type :=
| true
| false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

(* 为何取反的符号不能定义,报错： *)
(* The reference x was not found in the current environment. *)
(* Notation "!x" := (negb x). *)
Notation "! x" := (negb x)(at level 70).

Example test_orb:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

Example test_not:  !false = true.
Proof. simpl. reflexivity. Qed.