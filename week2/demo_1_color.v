Inductive rgb : Type :=
| red
| green
| blue.

Inductive color : Type :=
| black
| white
| primary (p : rgb).

Definition monochrome (c : color) : bool :=
match c with
| black => true
| white => true
| primary q => false
end.

Definition isred (c : color) : bool :=
match c with
| black => false
| white => false
| primary red => true
| primary _ => false
end.

Example test_color1:  (monochrome black)  = true.
Proof. simpl. reflexivity.  Qed.

Example test_color2:  (monochrome (primary red))  = false.
Proof. simpl. reflexivity.  Qed.

Example test_color3:  (isred (primary red))  = true.
Proof. simpl. reflexivity.  Qed.

Example test_color4:  (isred black)  = false.
Proof. simpl. reflexivity.  Qed.
