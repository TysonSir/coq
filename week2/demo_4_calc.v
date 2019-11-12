Module NatPlayground2.

(* 加 *)
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

(* 乘 *)
Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity.  Qed.

(* 减 *)
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

Example test_minus1: (minus 3 2) = 1.
Proof. simpl. reflexivity.  Qed.

(* 幂 *)
Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Example test_exp1: (exp 2 10) = 1024.
Proof. simpl. reflexivity.  Qed.

End NatPlayground2.