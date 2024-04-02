(** * INITIATION TO COQ (1) *)

(**
- Please read carefully the explanations in comments 
- if you use emacs/Proof-general,
  - 1 step forward:        C-c C-n
  - 1 step backwards:      C-c C-p
  - up to cursor position: C-c RET.
  Look at Proof-General and Coq menus to discover other shortkeys.
*)


(** ** General introduction *)

(** Coq is primitively a programming language.
    More precisely a typed, functional, programming language,
    like OCaml or Haskell.
    Its typing system is however much richer, allowing us to state
    logical formulae and, maybe to prove them.

    In a first stage, we focus on programming aspects.  Then we
    will consider very simple logical formulae: equalities.
 *)

(** A Coq script is a sequence of declarations for types, values,
    (very often: functions), theorem statements followed by their proof.

    Additional commands are available in order to get information
    or compute expressions.
*)

(** DON'T FORGET: IN COQ, ALL SENTENCES END WITH A DOT '.' *)

(** Executive summary.

    In a functional programming language (PL):
    - forget about memory states, side effects, especially assignments,
      we only use pure EXPRESSIONS
    - the intended meaning of an expression is a FIXED value
    - variables are invariable
    - beyond variables, expressions are made of functions
    - functions can be input arguments of functions
    - functions can be returned as output

    Additionally
    - we have anonymous functions, i.e., functions without name
      (like in math : x ↦ x * 2)
      This is because they are also expressions, and expressions
      make sense before they are provided a name.

    Program extraction: Coq ---> OCaml
 *)

(** Historical note.

    Recently, a number of mainstream programming languages such as C++
    introduced a "new" feature, called lambdas, in order to allow
    some functional programming.
    The name lambda comes from a theoretical functional programming language,
    invented by Church in the 1930s, because he used the greek letter λ 
    for introducing anonymous functions.
    A by-product of this course is that you will master an important
    and modern feature of mainstream PL. *)

(** ** Expressions *)

(** Disclaimer: for convenience in this section and the next section,
    we will freely use simple arithmetical expressions like [6 + x * 2].
    Here 2 and 6 are actually a convenient notation for *mathematical
    natural numbers* whose precise contents will be seen later.  They
    are not the [int] of usual progranning language.  But we can
    forget about this in this file. *)

(** In Coq only well-typed expressions make sense. As type checking is central,
    we have the command [Check] allowing us to perform type checking on
    any expression. For instance, the type of 6 is called [nat].  *)

Check 6.


(** A definition binds a name to a type and an expression
    Let us bind the name [my_typed_six], of type [nat], to 6. *)

Definition my_typed_six : nat := 6.

(** We can also let Coq guess the type. *)
Definition my_six := 6.

(** As [my_six] is defined, it is accepted as an expression. *)

Check my_six.

(** A defined name can be displayed. *)
Print my_six.

(** Let us bind the name [anothernat] to [my_six + 5 * 2] *)
Definition anothernat := my_six + 5 * 2.

(** We can display it (with its type). *)
Print anothernat.

(** We can also compute it with the [Eval] command, which returns
    the result and its type. It means "evaluate what follows using
    the given strategy".  We don't have to know about evaluation strategies
    at the moment, we use [cbn] which is the convenient on of this section. *)
Eval cbn in anothernat.

(** Any well-typed expression can be evaluated *)
Eval cbn in my_six + 5 * 2.

(** The above expression involves arithmetical operations,
    which are binary functions.
    At this stage, we see that expressions are either constants,
    names bound to an expression,
    or functions applied to other expressions (e.g., multiplication
    applied to 2 and 5).*)

(** ** Functions *)

(** The next stage consists in introducing variables.
    Like [my_six] or [anothernat], they are names, but their
    underlying contents is unknown. So they are pnly provided a type.
    It is better to limit their use inside a scope delimited by
    a "section", between [Section name_sec] and [End name_sec]. *)

Section sec_x.
  Variable x : nat.

  Check x * 2.
  Eval cbn in x * 2.

End sec_x.

(** BEWARE: [x] represents an unknown but IMMUTABLE (or constant) value.
    Like in maths, [x] refers to the same (unknown) thing everywhere
    (in a given scope). 
    This allows us to confidently perform equational reasoning, for instance.
    In contrast, as popular programming languages are imperative: their variables 
    represent things that evolve with time, depending on assignments performed 
    on the memory state.
    In short:
    in the functional setting (and in maths), VARIABLES ARE INVARIABLE. *)

(** The next stage consists in defining functions.
    The very point of functional languages is that functions are themselves
    expressions. 
    To illustrate the syntax of an anonymous function, the function with 
    input [x] and output [x * 2] is written [fun (x : nat) => x * 2], 
    or just [fun x => x * 2]
    because the type of [x] can be guessed from its usage.
    The scope of the argument [x] is delimited by the body of the function.
    Let us check that the type of [x] is correctly guessed. *)

Check fun x => x * 2.

(** And we see that the type of a function taking a nat as input and returning
    a nat is written [nat -> nat]. *)

(** Now we can bind this anonymous expression to the name mul2 using the same
    construct as before. *)

Definition mul2 := fun x => x * 2.

Check mul2.

Print mul2.

(** The next thing to know is how to get an expression where the
    above function is applied to an argument, say 5.
    The common convention coming from maths is to use parentheses: mul2 (5).
          FORGET ABOUT THIS USAGE OF PARENTHESES
    for reasons which will become clear later.
    We just write [mul2 5] *)

Eval cbn in mul2 5.

(** Equivalently, we can use (fun x => 2 * x) instead of mul2;
    PARENTHESES ARE USED TO GROUP THINGS TOGETHER. *)

Eval cbn in (fun x => x * 2) 5.

(** Now [fun (f : nat -> nat) => f 5] is a function whose argument is 
    a function [f] from nat to nat, and returns [f 5].
    What is its type? *)

Check fun (f : nat -> nat) => f 5.

(** It can be given a name *)
Definition app_to_5 := fun (f : nat -> nat) => f 5.
Check app_to_5.

(** And it can be applied to [mul2] *)
Eval cbn in app_to_5 mul2.

(** IN A FUNCTIONAL SETTING, FUNCTIONS CAN BΕ INPUT ARGUMENTS OF FUNCTIONS *)

(** The body of a function (the expression on the right of [=>])
    is a well-type expression. It can contain occurrences of
    its argument, here [x], and of other declared variables. *)

Section sec_n.
  Variable n : nat.

  Check fun x => n + x * 2.
End sec_n.

(** We can write a function of [n] that returns [fun x => n + x * 2] *)

Definition fun_as_output := fun n => (fun x => n + x * 2).

(* The type should be: nat -> (nat -> nat) *)

(** IN A FUNCTIONAL SETTING, FUNCTIONS CAN BΕ RETURNED AS OUTPUT *)

Check fun_as_output.

Check fun_as_output 6.

(** The latter function can be applied to 5 *)

Eval cbn in (fun_as_output 6) 5.

(** NOTATIONAL CONVENTIONS: parentheses can be removed as follows
    - [ (fun_as_output 6) 5 ] can be written [ fun_as_output 6 5 ]
    - [fun n => (fun x => n + x * 2)] can be written
      [fun n => fun x => n + x * 2] and even
      [fun n x => n + x * 2] *)

(** Altogether we get *)
Eval cbn in (fun n x => n + x * 2) 6 5.

(** In other words, A BINARY FUNCTION 
    is just a unary function returning a unary function.
    And so on for functions of 3, 4... arguments. No need for tuples. *)

(** Finally, here is a function which takes a function in argument
    and returns a function *)
Definition translate1 := fun (f : nat -> nat) => (fun n => f (n + 1)).

(** ** Enumerated types *)

(** Let us declare a type [tlcolor] (traffic light colors) inhabited by 
    three canonical values named [Green), [Orange) and [Red].
    These 3 names are called the constructors of [tlcolor].
*)

Inductive tlcolor : Set :=
  | Green  : tlcolor
  | Orange : tlcolor
  | Red    : tlcolor
.

(** In Coq everything has a type; the previous declaration states
    that the type of [Green], [Orange] and [Red] is [tlcolor],
    and also that the type of [tlcolor] is [Set];
    [Set] is the type of datatypes and of functions between them.
*)

(** ** Pattern-matching *)

(** Pattern-matching is a prominent feature of typed functions languages.
    It allows you to provide a result for each possible case of a datatype.
    The syntax is
    match expr with
    | pattern1 => result1
    | pattern2 => result2
    etc.
    end.

    If the type of [expr] is [tlcolor], the patterns are just its constructors.
 *)

Definition next_col : tlcolor -> tlcolor :=
  fun c =>
    match c with
    | Green  => Orange
    | Orange => Red
    | Red    => Green
    end.

(** Let us check and evaluate some simple expressions. *)

Check next_col.
Check (next_col Green).
Eval cbn in (next_col Green).

(** For expresssions without variable, it is common to
    use the strategy [compute]. *)
Eval compute in (next_col Green).

(** Shorthand *)
Compute (next_col Green).

(** ** Enriched constructors *)

(** The constructors of a datatype can be endowed with additional contents
    of any type. In Coq, they are typed like functions.

    The underlying idea is that a data can have several disjoint shapes.
    Each constructor acts as a switch for deciding which shape is relevant,
    so we get a CHOICE between JUXTAPOSITIONS.
    In the language of set theory: disjoint unions of cartesian products.
 *)

Inductive color : Set :=
| Yellow : color
| TLC    : tlcolor -> color
| Grey   : nat -> color.

Inductive colpoint : Set :=
| CP : color -> nat -> nat -> colpoint.

Example gr6 := Grey 6.
Example mycp := CP (TLC Red) 2 3.

Print mycp.

(** Then patterns are special expressions made only of
    constructors and new variables (no computation).
    Each case has its own scope for these new variables.
    Type-checking allows us to ensure that only relevant
    components are used on the right hand side of [=>] *)

Example snd_coord : colpoint -> nat :=
  fun cp =>
    match cp with
    | CP c x y   => y
    end.

Example no_meaning : colpoint -> tlcolor :=
  fun cp =>
    match cp with
    | CP Yellow x1 y1   => Green
    | CP (TLC tc) x y   => next_col tc (* [tc] makes sense only in this case *)
    | CP (Grey n) x2 y2 => Red
    end.

Compute no_meaning mycp.

(** Unused variables can be replaced by a joker [_].
    Cases can be written in another order and are
    considered top-down. *)

Example jokers : colpoint -> tlcolor :=
  fun cp =>
    match cp with
    | CP (TLC tc) _ _   => next_col tc (* [tc] makes sense only in this case *)
    | _                 => Orange
    end.

Compute jokers (CP gr6 1 1).
Compute jokers (CP Yellow 1 1).
Print jokers.

(** Inductive types can also be recursive, providing many kinds
    of tree-like data-structures.  
    An example will be given at the end of this file. *)

(** ** First theorem, tactics [cbn] and [reflexivity] *)

Theorem ex1_next_col : next_col (next_col Green) = Red.
Proof.
  cbn [next_col].
  (** Note that the strategy [cbn] can be provided a list of
      names to be reduced, for additional accuracy. *)
  reflexivity.
Qed.

(** Remark: other keywords can be used in place of [Theorem].
They are synonyms and their choice is only a matter of taste.
For instance [Lemma] can be used for auxiliary statements, 
[Remarck can be used for easy to prove statements, [Example]
for showing the expected result returned by a function on 
some argument. For instance we have written:
Example ex1_next_col : next_col (next_col Green) = Red.
*)


(** A *tactic* is a command allowing us to progress in a proof. *)

(** In the above example we used the following tactics:
    - cbn [function_name]: (partial) evaluation of [function_name]
    - reflexivity: check that the two members of the equality to be proven
                   are identical (proof of x = x).
 *)

(** ΑT THE END OF A PROOF SCRIPT, DON'T FORGET TO WRITE  "Qed." *)

(** ** Variables *)

(** Proofs by reflexivity works not only between identical
    constant expressions, but also between expressions with
    variables. *)

(** In Coq (in contrast with OCaml) it is allowed to declare
    variables, taht is, names which are only provided a type.
    Such names are declared in a scope (where they are visible)
    defined by a section.
*)

(** Here we open a section where a proof by reflexivity
    will be performed. *)

Section sec_refl.
  Variable c : tlcolor.
  (** Intuitive meaning: "let [c] be an unknown [tlcolor]". *)

  Theorem th1_refl_simple : c = c.
  (** Remark that the goal contains an environment that includes
      a hypothesis stating that [c] has the type [tlcolor]. *)
  Proof. reflexivity. Qed.

  Check c.
  Check th1_refl_simple.

(** Closing the section, so that declared variable, here
    [c : tlcolor], will no longer remain available. *)
End sec_refl.

Fail Check c.
(* The keyword [Fail] states that we expect what follows to fail *)
(* Here is another example *)
Fail Definition x := Green + 2.

(** ** Leibniz Principle: tactic [rewrite] *)

Section sec_reec.
  Variable c : tlcolor.
  Hypothesis c_isred : c = Red.
  (** Intuitive meaning, similar to the previous line:
      "let [c_isred] be an unknown proof of [c = Red]". *)

  Theorem next_col_Red : next_col c = Green.
  Proof.
    rewrite c_isred.
    cbn [next_col].
    reflexivity.
  Qed.

End sec_reec.

(** ** Reasoning by cases : tactic [destruct] *)

Section sec_cas.
  Variable c : tlcolor.

  Theorem th3_next_col : next_col (next_col (next_col c)) = c.
  Proof.
    (** reflexivity does not work. *)
    Fail reflexivity.
    (** We need to reason by case on the three possible values of [c]. *)
    (** This yields three subgoals, one for ecah case.
        Each of them are handled in the same way, below we show some
        possible shortcuts to be explained in the lecture. *)
    destruct c as [ (*Green*) | (*Orange*) | (*Red*) ].
    - cbn [next_col]. reflexivity.
    - cbn. reflexivity.
    - reflexivity
     (* First illustration of KEY DEEP FEATURE of Coq, to be discussed later:
        "computations are for free in proof checking". *).
  Qed.

  (** Remark : tactic [destruct] works like a pattern matching where
      constructors are not named and handled in the order indicated
      in the declaration of the relevant type, here [tlcolor].
      Indeed, [destruct] *builds* a pattern matching: this can be observed
      by displaying the contents of the proof -- using [Print], as usual.
      Warning: the material displayed is somewhat complicated, please just
      look at the general shape for the moment. *)

  Print th3_next_col.

End sec_cas.

(** ** Universal reasoning: tactic [intro] *)

(** It is possible to state universally quantified formulae.
    For example: [forall c : tlcolor, c = c].
 *)

Theorem th_refl_gen : forall c : tlcolor, c = c.
Proof.
  (** To show this, the first step consists in saying
      "let [c0] an arbitrary color, show [c0 = c0]." *)
  intro c0.
  (** Remark that [intro] introduced the hypothesis [c0 : tlcolor]. *)
  (** We already know that [reflexivity] works in this situation. *)
  reflexivity.
Qed.

(** The tactic [intro] can also be used to prove an implication. *)
Theorem th_c_isred_gen : forall c : tlcolor, c = Red -> next_col c = Green.
Proof.
  intro c0.
  (** In order to prove [c0 = Red -> next_col c0 = Green],
      we assume [c0 = Red]
      and we then need to prove [next_col c0 = Green]
      under this additional hypothesis;
      when introducing an hypothesis, it must be given a name. *)
  intro c0_isred.
  (** The underlying reasoning is:
      let [c0_isred] be an arbitrary (unknown) proof of [c0 = Red],
      we are allowed to used it to make a proof of [next_col c0 = Green]. *)
  rewrite c0_isred. cbn [next_col]. reflexivity.
Qed.

(** Remark: we often have to make several successive introductions
    We then use the shortcut [intros] (plural).
    On the previous example this yields: *)
Theorem th_c_isred_gen_bis : forall c : tlcolor, c = Red -> next_col c = Green.
Proof.
  intros c0 c0_isred.
  rewrite c0_isred. cbn [next_col]. reflexivity.
Qed.

(** * Homework *)

(** *** Exercise: Variant of the previous theorem using the section mechanism. *)

Section sec_alt_th_c_isred_gen.
  Variable c : tlcolor.
  Theorem th_c_isred_demi_gen : c = Red -> next_col c = Green.
  Proof.
    (** PLEASE COMPLETE HERE *)

  (* When a proof is uncomplete, you can leave it and consider the sequel
     using [Admitted] in place of [Qed].
     Don't forget to replace [Admitted] by [Qed] when you succeed! *)
  Admitted.

End sec_alt_th_c_isred_gen.

(** *** Exercise: proof by case on a theorem starting with [forall] *)

Lemma nextnextnext_id : forall c : tlcolor, next_col (next_col (next_col c)) = c.
Proof.
(** PLEASE COMPLETE HERE *)
Admitted.

(** ** Recursive inductive types, structural recursion and structural induction *)

(** The idea is ilustrated on colored binary trees *)
Inductive bintree : Set :=
  | L : tlcolor -> bintree
  | N : bintree -> bintree -> bintree.

(**
To define a recursive function, we need
- its name in order to refer to it inside its body;
- a distinguished argument having an inductive type, which is required to be
  a structurally smaller component of the input in each recursive call.
This special kind of functions can be defined usind the following syntax.
 *)

Fixpoint revt t : bintree :=
  match t with
  | L c   => L c
  | N g d => N (revt d) (revt g)
  end.

(** By the way we also have an alternative similar syntax for named functions *)
Definition next_col_alt c : tlcolor :=
    match c with
    | Green  => Orange
    | Orange => Red
    | Red    => Green
    end.

(** *** Exercise: prove that reversing twice a tree returns the same tree *)
Theorem revt_revt : forall t, revt (revt t) = t.
Proof.
  intro t.
  (** Attempt to reason by case on t *)
  (** The names given in each case ([c] for the first, [t1 t2] for the second)
      refer to the components of the constructors, respectively [L] and [N]. *)
  destruct t as [ (* L *) c
                | (* N *) t1 t2 ].
  - cbn [revt]. reflexivity.
  - cbn [revt].
    (** We see that a simple reasoning by case is not enough, *)
    (** then we stop here... *)
 Abort.

(** ... and we restart using structural induction. *)
Theorem revt_revt : forall t, revt (revt t) = t.
Proof.
  intro t.
  (** Structural induction on the inductive type bintree. *)
  (** Remark the analogy with the use of the tactic [destruct] :
      the names given in each case ([c] for the first, [t1 t2] for the second)
      refer to the components of the constructors, respectively [L] and [N]
      but we also add two names for induction hypotheses,
      [Hrec_t1] for the hypothesis on [t1] and [Hrec_t2] for the
      hypothesis on [t2]. *)
  induction t as [ (* L *) c
                 | (* N *) t1 Hrec_t1 t2 Hrec_t2 ].
  - cbn [revt]. reflexivity.
  - cbn [revt].
    (* COMPLETE HERE *)

Admitted.

