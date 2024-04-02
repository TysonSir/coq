(** Basic constructs of functional programming in OCaml *)

(** This file is supposed to be read after the corresponding introductory
    file in Coq. *)

(** Coq and OCaml functional programming languages but, as they
    are designed for different purposes, a number of tradeoffs are
    different: 
    - Coq is a language designed to formalize and check mathematical proofs;
      the notion of computation to be dealt with is general enough
      to cover, for instance, expressions containing free variables
      (variables which are not bound to a specific value);
      efficiency of computations is important but not crucial.
    - OCaml is designed to be used as a "real" programming language;
      its computations mechanism is based on an evaluation strategy
      which is at the same time efficient, simple and predictible
      -- the one which is favoured in most programming languages:
      in a function call, arguments are computed before considering
      the body of the function. This strategy is called "call by value".
      BTW, as the order of evaluation is easy to follow, it makes
      some sense to add "impure" (imperative) features in OCaml,
      in order to deal with input/output for instance, preferably
      in a limited manner. These features are not covered here.
    This file shows how the functional programs and datatypes
    describe in the corresponding Coq file are written in OCaml,
    so that similarities and differences can be illustrated.*)
    
(** A functional OCaml program is a sequence of let-bindings;
    each [let] binds a name to a value, which is compted from an expression *)

(** DON'T PUT A DOT at the end of let-constructs! *)


(** ** Expressions *)

(** We start with arithmetic expressions: OCaml includes primitive
    integers, as in usual programming languages *)

(** Let us bind the name [my_typed_six] of type [int] to 6 *)

let my_typed_six : int = 6

(* We can also let OCaml guess the type. *)
let my_six = 6

(** Let us bind the name [anotherint] to the result of [my_six + 5 * 2] *)
let anotherint = my_six + 5 * 2

(** If we are only interested in the computation, we can bind the result 
     to nothing using [_] as follows *)
let _ = my_six + 5 * 2

(** The above expression involves arithmetical operations,
    which are binary functions.
    At this stage, we see that expressions are either constants,
    or functions applied to other expressions (e.g., multiplication
    applied to 2 and 5). *)

(** ** Functions *)

(** The next stage consists in definining functions.
    The very point of functional languages is that functions are themselves
    expressions. 
    To illustrate the syntax of an anonymous function, the function with 
    input [x] and output [x * 2] is written [fun (x : int) -> x * 2], 
    or just [fun x -> x * 2]
    because the type of [x] can be guessed from its usage.
    Note that, in Coq, the arrow used here would be [=>].
    We can bind this expression to the name mul2 using the let construct,
    and check that we get the expected type. *)

let mul2 = fun x -> x * 2

(** Notice that OCaml displays the type of a function but not its code. *)

(**  The next thing to know is how to get an expression where the
above function is applied to an argument, say 5.
As in Coq,
          FORGET ABOUT THIS USAGE OF PARENTHESES:
we just write [mul2 5] *)

let mul2_of_five = mul2 5

(** Equivalently, we can use [fun x -> 2 * x] instead of mul2;
    parentheses are used to group things together *)
let another_mul2_of_five = (fun x -> x * 2) 5

(** Now [fun (f : int -> int) -> f 5] is a function whose argument is 
    a function [f] from int to int, and returns [f 5].
    What is its type? *)
    
let app_to_5 = fun (f : int -> int) -> f 5

(** It can be applied to [mul2] *)
let _ = app_to_5 mul2

(** IN A FUNCTIONAL SETTING, FUNCTIONS CAN BΕ INPUT ARGUMENTS OF FUNCTIONS *)

(** Conversely, we can write a function of [n] that returns
    [fun x -> n + x * 2] *)

let fun_as_output = fun n -> (fun x -> n + x * 2)

(** It can be applied to [6] *)

let fao_of_6 = fun_as_output 6

(** The latter function can be applied to [5] *)
let _ = fao_of_6 5
let _ = (fun_as_output 6) 5

(** IN A FUNCTIONAL SETTING, FUNCTIONS CAN BΕ RETURNED AS OUTPUT *)

(** NOTATIONAL CONVENTIONS; as in Coq, parentheses can be removed:
    - [ (fun_as_output 6) 5 ] can be written [ fun_as_output 6 5 ]
    - [fun n -> (fun x -> n + x * 2)] can be written
      [fun n -> fun x -> n + x * 2] and even
      [fun n x -> n + x * 2] *)

(** Altogether we get *)
let _ = (fun n x -> n + x * 2) 6 5

(** In other words, A BINARY FUNCTION 
    is just a unary function returning a unary function.
    And so on for functions of 3, 4... arguments. No need for tuples. *)

(** Finally, here is a function which takes a function in argument
    and returns a function *)
let translate1 = fun (f : int -> int) -> (fun n -> f (n + 1))

(** ** Enumerated types *)

(** Let us declare a type [tlcolor] (traffic light colors) inhabited by 
    three canonical values called [Green], [Orange] and [Red].
*)

type tlcolor =
  | Green
  | Orange
  | Red

(** Pattern-matching works the same in OCaml and in Coq, but
    the syntax is slightly different (arrows; and no ending [end]. *)
let next_col : tlcolor -> tlcolor =
  fun c ->
    match c with
    | Green  -> Orange
    | Orange -> Red
    | Red    -> Green

let _ = next_col Green

(** Choice, juxtaposition *)

type color =
| Yellow
| TLC    of tlcolor
| Grey   of int

(** When a constructor has several components, they are aggregated in a tuple *)
type colpoint = CP of color * int * int

let gr6 = Grey (6)
let mycp = CP (TLC Red, 2, 3)

let snd_coord : colpoint -> int =
  fun cp ->
    match cp with
    | CP (c, x, y)   -> y

let no_meaning : colpoint -> tlcolor =
  fun cp ->
    match cp with
    | CP (Yellow, x1, y1)   -> Green
    | CP (TLC tc, x, y)   -> next_col tc (* [tc] makes sense only in this case *)
    | CP (Grey n, x2, y2) -> Red

let _ = no_meaning mycp


let jokers : colpoint -> tlcolor =
  fun cp ->
    match cp with
    | CP (TLC tc, _, _)   -> next_col tc (* [tc] makes sense only in this case *)
    | _                   -> Orange

let _ =  jokers (CP (gr6, 1, 1))

(** ** Recursive inductive types and recursive functions *)

type bintree =
  | L of tlcolor
  | N of bintree * bintree

let rec revt t : bintree =
  match t with
  | L c      -> L c
  | N (g, d) -> N (revt d, revt g)

let btg = L Green
let bto = L Orange
let btr = L Red

let _ = revt (N (btr, N (btg, bto)))
