(** **** 练习：1 星, standard (plus_id_exercise)  
证明等式*)
Theorem plus_id_exercise : forall n m o : nat,
n = m -> m = o -> n + m = m + o.

Proof.
intros n m o.
intros H1.
rewrite <- H1. (* 替换成左边的形式 *)
intros H2.
rewrite <- H2.
reflexivity.  Qed.


(** **** 练习：2 星, standard (mult_S_1)  
引入已有证明*)
Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  rewrite <- plus_1_l.
  intros H1.
  rewrite <- H1. (* 替换成左边的形式 *)
  reflexivity.  Qed.