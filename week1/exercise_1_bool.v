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
(* Notation "!x" := (negb x). *)

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

(** **** 练习：1 星, standard (nandb)  
此函数应在两个输入中包含 [false] 时返回 [true] 。  *)
(* 此处代码冗余，希望学到后面能改进 *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => (negb (b1 && b2))
  | false => (negb (b1 && b2))
  end.

Example test_nandb1:               (nandb true false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_nandb2:               (nandb false false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. simpl. reflexivity.  Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. simpl. reflexivity.  Qed.

(** **** 练习：1 星, standard (andb3)  
此函数应在所有输入均为 [true] 时返回 [true]，否则返回 [false]。 *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => (b1 && b2 && b3)
  | false => (b1 && b2 && b3)
  end.

Example test_andb31:                 (andb3 true true true) = true.
Proof. simpl. reflexivity.  Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. simpl. reflexivity.  Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. simpl. reflexivity.  Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. simpl. reflexivity.  Qed.