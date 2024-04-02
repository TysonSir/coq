(** * INITIATION TO COQ (2): interactive definition of functions *)

(** Additional material to coq01_intro.v, where we show how
    the [next_col] function can be developed interactively,
    using tactics.
*)

Inductive tlcolor : Set :=
  | Green  : tlcolor
  | Orange : tlcolor
  | Red    : tlcolor
.

(** Original definition *)
Definition next_col : tlcolor -> tlcolor :=
  fun c =>
    match c with
    | Green  => Orange
    | Orange => Red
    | Red    => Green
    end.

(** Interactive definition *)
Definition next_col2 : tlcolor -> tlcolor.
Proof.
  intro c.
  Show Proof.
  destruct c as [ (*Green*) | (*Orange*) | (*Red*) ].
  Show Proof.
  -Show Proof.
    exact Orange.
  - exact Red.
    Show Proof.
  - exact Green.
Defined.

Print next_col2.

Compute next_col2 Red.

(** Definition using the tactic [refine].
    The argument given to [refine] is a piece of program to be completed. *)
Definition next_col3 : tlcolor -> tlcolor.
Proof.
  intro c. Undo 1.
  refine (fun c => _).
  destruct c as [ (*Green*) | (*Orange*) | (*Red*) ]. Undo 1.
  refine (match c with
          | Green => _
          | Orange => _
          | Red => _
          end).
  Show Proof. Undo 2.
  refine (fun c =>
            match c with
            | Green => _
            | Orange => _
            | Red => _
            end).
  Undo 1.
  refine (fun c =>
            match c with
            | Green => _
            | Orange => Red
            | Red => _
            end).
  - refine Orange.
  - refine Green.
Defined.

Print next_col3.
Compute next_col3 Red.


(** And what about theorems? *)

(**
In the famous Curry-Howard correspondence, 
"[p] is a proof of formula [F]" can be written [p : F],
that is, [p] can be seen as a data or a functional program of type [F].
In the sequel we write "function" for as a shorthand for "functional program".

The types seen until now in the programming part could be divided
into basic data, such as [tlcolor], and functional types, 
written with arrows [->].
Similarly, the previous statements of theorems were build with 
basic equalities, implications written with [->] and universal quantification.

This double use of the arrow is on purpose:
  A proof of [P -> Q] is a function that builds a proof of [Q]
  from any proof of [P].

To complete the picture about data, we have also tree-like structures
both for data (binary trees, AST, etc.) and for proofs (that is,
proof trees), to be presented soon.

Finally, proofs of universally quantified formulas have also a natural
functional interpretation:
  A proof of [∀x, P x] is a function that builds a proof of [P x]
  from any [x].
 *)

(**
Actually, interesting theorems are stated by universally quantified formulae.
From the point of view of functional programs, they involve a notion 
of type that is not present in usual programming languages, including OCaml:
dependent types.
Reading or writing complete programs using dependent types requires some
care and is posponed at the moment.
 *)

(** 
However a simple manipulation is easy and important to understand at this stage.
Consider a theorem such as:
[Theorem t : forall x : some_type, blablah x.]
And consider an expression [e] of type [some_type],
then [t] applied to [e], that is [t e] makes sense and yields a proof of [blablah e].

Let us see an example.
 *)


Lemma nextnextnext_id : forall c, next_col (next_col (next_col c)) = c.
Proof.
  intro c.
  destruct c as [ (*Green*) | (*Orange*) | (*Red*) ]; reflexivity.
Qed.

Example ex_nnnid : next_col (next_col (next_col (next_col Green))) = next_col Green.
Proof. (* without computation such as [cbn] *)
  (* We want to use the previous theorem, with [next_col Green] of [c] *)
  Check (nextnextnext_id Green). (* not the right one *)
  Check (nextnextnext_id (next_col Green)). (* right on target! *)
  exact (nextnextnext_id (next_col Green)).
Qed.

(* A more interesting application *)
Lemma id_nextnextnext : forall c, c = next_col (next_col (next_col c)).
Proof.
  (* We choose a different name for [c], for clarity of the sequel *)
  intro c1.
  Show Proof.
  (* Here we want to replace [next_col (next_col (next_col c1))] by [c1] *)
  Check (nextnextnext_id c1).
  rewrite (nextnextnext_id c1).
  reflexivity.
Qed.

(* In the previous proof, we could just write
   [rewrite nextnextnext_id].
   But it is better to know that actually, Coq completed the tactic
   as shown explicily.
   Here is a simple situation where explicit application is required. *)


Lemma next_col_inj : forall c1 c2, next_col c1 = next_col c2 -> c1 = c2.
Proof.
  intros c1 c2 e.
  rewrite id_nextnextnext. (* Coq chose [c2] *)
  rewrite id_nextnextnext. (* Bad, Coq chose [c2] again! *)
  (* Let us have better control *)
  Undo 2.
  rewrite (id_nextnextnext c1).
  rewrite (id_nextnextnext c2).
  rewrite e.
  reflexivity.
Qed.
