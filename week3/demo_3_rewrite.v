Theorem plus_id_example : forall n m:nat,
n = m ->
n + n = m + m.

Proof.
(* 将两个量词移到上下文中： *)
intros n m.
(* 将前提移到上下文中： *)
intros H.
(* 用前提改写目标： *)
rewrite <- H.
reflexivity.  Qed.


(* 引入已有证明 *)
Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.