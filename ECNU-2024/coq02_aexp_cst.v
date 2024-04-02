(** Abstract Syntax Trees (AST) and induction *)

(** * AST of arithmetical expressions *)

(** ** Définitions *)

(** We consider a data structure for encoding simple artihmetical expressions
    involving only numerical constants of type [nat], addition and  multiplication.
    The constructors are respectively named Cst, Apl et Amu *)

Inductive aexp : Set :=
| Cst : nat -> aexp
| Apl : aexp -> aexp -> aexp
| Amu : aexp -> aexp -> aexp
.

(* Define aexp trees corresponding to
  (1 + 2) * 3  and  (1 * 2) + 3
 *)

Definition exp_1 : aexp. Admitted.
Definition exp_2 : aexp. Admitted.

(** The functional semantics interprets an AST by a mathematical function.
    Here we use the functions of the Coq language, and the functional
    semantics is simply a recursive function called [eval].
    We use the functions [+] and [*] of the standard library. *)

Fixpoint eval (a : aexp) : nat :=
  match a with
  | Cst n => n
               (* COMPLETE HERE AND REMOVΕ THΕ NEXT LINE *)
  | _ => 0
  end.

(** Use Eval or Compute to get the functional semantics of exp_1 and exp_2 *)

(* COMPLETE HERE *)

(** Number of leaves *)

(** Define the function computing the number of leaves in an AST
    of arith expressions (that is, the number of constants contained
    in the expression) *)

Fixpoint nbl (a : aexp) :=
  match a with
               (* COMPLETE HERE AND REMOVΕ THΕ NEXT LINE *)
  | _ => 0
  end.

(** ** Reasonnig by case on an AST *)

(** Write a function that transforms an AST as follows:
   - if the AST represents a constant, return the (AST of) the constant 1
   - if the AST represents an addition, return the constant 2
   - if the AST represents an product, return the constant 3
 *)

Definition categorize (a : aexp) :=
  match a with
               (* COMPLETE HERE AND REMOVΕ THΕ NEXT LINE *)
  | _ => Cst 0
  end.

(** Proof that the resu de la fonction précédente
    returns an AST of size 1, in th sense of [nbl].
    Reason by case using the tactic [destruct].
 *)

Lemma nbl_cat : forall a, nbl (categorize a) = 1.
Proof.
(* COMPLETE HERE AND REPLACE [Admitted] BY [Qed] *)
Admitted.

(** Number of operators *)

(** Define the function that computes the number of nodes in an AST
    (the number of binary operations of the corresponding expression) *)

Fixpoint nbo (a : aexp) :=
  match a with
               (* COMPLETE HERE AND REMOVΕ THΕ NEXT LINE *)
  | _ =>  0
  end.

(** Using structural induction, proof that [nbl] and [nbo] are related as follows *)

(** Basic arithmetical from the std library lemmas can be used. *)

Require Import Arith. Import Nat.
Check add_assoc.

Lemma nbl_nbo_plus_1: forall a : aexp, nbl a = nbo a + 1.
Proof.
  intro a.
  induction a as [ (*Cst*) n
                 | (*Apl*) a1 Hrec_a1 a2 Hrec_a2
                 | (*Amu*) a1 Hrec_a1 a2 Hrec_a2 ].
(* COMPLETE HERE AND REPLACE [Admitted] BY [Qed] *)
Admitted.

(** Transformation of expressions *)

(* Write a function that transforms an AST as follows:
 - constants are replaced by 1
 - all binary operators are replaced by +
 *)

Fixpoint transform (a : aexp) :=
  (* COMPLETE HERE AND REMOVΕ THΕ NEXT LINE *)
  Cst 0.

(** Compute the previous function on exp_1 et exp_2 *)

(* COMPLETE HERE *)

(** Now proof that the evaluation of [transform a] yields the number
    of leaves of [a]. *)

Lemma eval_transform_nbl : forall a, eval (transform a) = nbl a.
Proof.
(* COMPLETE HERE AND REPLACE [Admitted] BY [Qed] *)
Admitted.

(** ** Simplification of (AST of) expressions *)

(** The intention here is to optimize (AST of) expressions by
    removing in advance, at compile time, some unnecessary
    computations.  A very mall number of optimizations will
    be sufficient to illustrate the idea: only a zero on
    the left of [+] or of [*] will be considered.  The point
    is to take the propagation of such simplifications into account.
    To this effect we first consider an auxiliary function named simpl0
    that performs the desired simplifications at the root of an AST.
    It can be specified by the following drawings.
    
              Add
    simpl0    / \      =  a2
            Cst  a2
             |
             0
    
              Mul         Cst
    simpl0    / \      =   |
            Cst  a2        0
             |
             0
    
    simpl0    a       =  a       in all other cases
    
 *)    

(** Défine the function [simpl0] using pattern-matching. *)

Definition simpl0 (a : aexp) :=
  match a with
  (* COMPLEΤΕ BETWEEN HERE *)
  (* AND HERE *)
  | _ => a
  end.

(* -------------------------------------------------------------------------- *)

(** Now we want to prove that [simpl0] preserves the result of the evaluation. *)

(* We introduce a user-defined tactic whos meaning is:
   proof cases "0 + a2" and "0 * a2", 
   anticipating that all other cases are proven by computation and 
   réflexivity.
   You are only expected to use this tactic, explanations on its
   design will come later.
   WARNING: if you considered additional simplifications in [simpl0],
   the following tactic HAS to be adapted accordingly, otherwise you
   will experience issues...
*)
Ltac case_simpl0 a :=
  refine ( match a with
           | Apl (Cst 0) a2 => _
           | Amu (Cst 0) a2 => _
           | _ => eq_refl _
           end).

(** The two following lemmas from the standard library may be useful. *)
Check add_0_l.
Check mul_0_l.

Lemma eval_simpl0: forall a, eval (simpl0 a) = eval a.
Proof.
  intro a. case_simpl0 a.
  - cbn [simpl0]. cbn [eval]. rewrite add_0_l. reflexivity.
(* COMPLETE HERE AND REPLACE [Admitted] BY [Qed] *)
Admitted.

(** Write the function [simpl_rec] that recursively applies [simpl0] to 
    all sub-expressions of the input. *)

Fixpoint simpl_rec (a : aexp) :=
  (* COMPLETE HERE AND REMOVΕ THΕ NEXT LINE *)
  Cst 0.

(** Proof that [simpl_rec] preserves the value of (AST of) expressions. *)

Lemma eval_simpl_rec: forall a, eval (simpl_rec a) = eval a.
Proof.
(* COMPLETE HERE AND REPLACE [Admitted] BY [Qed] *)
Admitted.

