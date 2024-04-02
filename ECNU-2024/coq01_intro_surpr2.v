(** * INITIATION TO COQ (2): dependet types and proofs *)

(** Additional material to coq01_intro_surpr1.v, developing the idea
    saying that
    - develop a typed functional program , and
    - build a proof
    are identical activities.
    (Curry_Howard correspondence).
    This is especially amazing when we consider *dependent types*.
*)

(* ------------------------------------------------------------ *)
(** ** I. Our usual definitions *)

Inductive tlcolor : Set :=
  | Green  : tlcolor
  | Orange : tlcolor
  | Red    : tlcolor
.

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
  destruct c as [ (*Green*) | (*Orange*) | (*Red*) ].
  Show Proof.
  -Show Proof.
    exact Orange.
  - exact Red.
  - exact Green.
Defined.

(** Using the tactic [refine]. *)
Definition next_col3 : tlcolor -> tlcolor.
Proof.
  refine (fun c =>
            match c with
            | Green => _
            | Orange => Red
            | Red => _
            end).
  - refine Orange.
  - refine Green.
Defined.

(* ------------------------------------------------------------ *)
(** ** II. A very common tactic:  [apply] *)

(** A meaningless function calling [next_col]. *)
Definition call_nc : tlcolor -> tlcolor :=
  fun c =>
    match c with
    | Green => Orange
    | Orange => next_col Red
    | Red => Green
    end.

(** In interactive mode, use the tactic [apply]. *)
Definition call_nc2 : tlcolor -> tlcolor.
Proof.
  intro c.
  destruct c as [ (*Green*) | (*Orange*) | (*Red*) ].
  Show Proof.
  - exact Orange.
  - apply next_col. Show Proof.  exact Red.
  - refine (next_col _). exact Green.
Defined.

(** It is the expected code *)
Print call_nc2.

(** Using [refine] for developing code in an incremental manner. *)
Definition call_nc3 : tlcolor -> tlcolor.
Proof.
  refine (fun c => _).
  refine (match c with
          | Green => Orange
          | Orange => _
          | Red => Green
          end).
  - refine (next_col _). refine Red.
Defined.

(** It is the same. *)
Print call_nc3.


(* --------------------------------------------------------------- *)
(** ** III. Step-by-step construction of a proof seen as a program *)

(** [refine] can also be used for writing proofs. *)
(** Instead of the type [tlcolor -> tlcolor], we state the formula
    to be proven. *)
Lemma nextnextnext_id :
  forall c:tlcolor, next_col (next_col (next_col c)) = c.
Proof.
  (** We make a function returning an equality proof for all [c] *)
  refine (fun c => _).
  (** Reasoning by case ([destruct]) *)
  refine (match c with
          | Green => _
          | Orange => _
          | Red => _
          end).
  all:exact refl_equal.
Qed.

(* -------------------------------------------------------- *)
(** Forget about proofs and go back to ordinary programming *)
(** ... well, almost ordinary:
    we start with a program  computing not a data,
    but ea type (written [Set] in Coq : the type of [nat], etc.)

    Here we go beyond OCaml *)
Definition waow : tlcolor -> Set :=
  fun c =>
    match c return Set with
    | Green => nat
    | Orange => tlcolor
    | Red => tlcolor -> nat
    end.

(** We use it to write a function of [c] whose result depends on [c]:
    hence the name *dependent type*.
    It cannot be written with an arrow as usual, i.e..
    [tlcolor -> "some_type"], because this "some_type" depends on the input
    Again, this is beyond then capabilities of OCaml (in a match the type
    to be returned is the same in each case).   *)
Definition waow_waow : forall c : tlcolor, waow c :=
  fun c =>
    match c return waow c with
    | Green => 2
    | Orange => Green
    | Red => fun c => match c with Green => 1 | Orange => 6 | Red => 4  end
    end.

(** Actually, [A -> B] can be written [forall a: A, B], example : *)
Check (forall c : tlcolor, nat).

(** Interactive development of [waow_waow]. *)
Definition waow_waow2 : forall c, waow c.
Proof.
  refine (fun c => _).
  refine (match c with
    | Green => _
    | Orange => _
    | Red => _
          end).

  Show Proof.

  - cbn [waow]. exact 2.
  - cbn [waow]. refine Green.
  - cbn [waow]. refine (fun c => _). destruct c as [ | | ].
    + refine 1.
    + exact 6.
    + apply 4.
Defined.

Compute (waow_waow2 Green).
Compute (waow_waow2 Orange).
Compute (waow_waow2 Red).
Compute (waow_waow2 Red Green).

(** [waow_waow2] is indeed the same as [waow_waow]. *)
Lemma meme_waow_waow : waow_waow2 = waow_waow.
Proof. reflexivity. Qed.

(** Let us see the full patter-matching, using a "return" clause.
    It makes clear that the program is well-typed. *)
Print waow_waow.
Print waow_waow2.

(* Let us play with [nextnextnext_id]. *)
Definition suivsuivsuiv_id_direct :
  forall c:tlcolor, next_col (next_col (next_col c)) = c :=
  fun c => 
    match c with
    | Green => eq_refl
    | Orange => eq_refl
    | Red => eq_refl
    end.

(** TODO TRANSLATE
<<
  +-----------------------+
  | En résumé, à retenir. |
  +-----------------------+
>>
  En Coq on a deux activités : poser des définitions et démontrer des théorèmes.
  En réalité il s'agit d'une seule et même activité, car une démonstration n'est au fond
  rien d'autre qu'une function qui fabrique une preuve de la conclusion pour tout paramètre
  effectif donné en entrée, par exemple une preuve de  [next_col (next_col (next_col c)) = c]
  pour tout [c].
  On est ici dans un univers où les preuves sont matérialisées par des arbres appelés arbres 
  de preuve. Ces derniers sont, d'une manière générale, des structures de données
  dont on a vu jusqu'ici quelques espèces, notamment :
  - des feuilles étiquetées "réflexivité de l'égalité" fabriquant des preuves de formules [x = x] ;
  - des nœuds binaires étiquetés "rewrite" fabriquant une preuve de [P y] à partir
    d'un sous-arbre prouvant une égalité de la forme [x = y]
    et d'un sous-arbre prouvant [P x] ;
  - des nœuds étiquetés "intro" permettant de prouver des propriétés de la forme [P -> Q],
    ou plus généralement [∀x, P x] ;
    on obtient ainsi des (AST de) programmes functionnels manipulant des (arbres de) preuves.

  Les types de tous ces arbres de preuve sont exprimés avec une formule logique,
  comprenant notamment la flèche (se lisant indifféremment comme l'implication ou comme un type
  functionnel) et le quantificateur ∀.

  Les formules [Q -> R] et [P -> Q -> R] sont des types de functions ayant respectivement 1 
  et 2 arguments. Pour l'uniformité, on considérera que [R] est également le type d'une function, 
  ayant 0 argument, ce qui permet de voir tous les arbres de preuve comme des (AST de) 
  programmes functionnels.

  On a également vu la notion de *type dépendant* sur l'exemple de la function [waow_waow] qui 
  rend un résultat dont *le type* (et non seulement le résultat) dépend de l'entrée,
  ce qui est au-delà des possibilités des langages usuels y compris OCaml.

  On observe alors qu'en tant que type, une proposition à démontrer telle que
  [next_col (next_col (next_col c)) = c] est un type dépendant :
  d'une manière générale [P vert] et [P rouge] sont des propriétés distinctes,
  et en particulier [next_col (next_col (next_col Green)) = Green] est une égalité distincte
  de [next_col (next_col (next_col Rouge)) = Rouge], même s'il se trouve que leurs
  preuves sont analogues du fait de la simplicité de l'exemple.

  Plus profondément, on a illustré la correspondance suivante, dite de Curry-Howard :
<<
            preuve         =   programme functionnel (sous forme d'AST)
            formule        =   type
     prouver une formule   =   programmer
>>
  La correspondance de Curry-Howard est une avancée conceptuelle majeure qui fonde
  les assistants modernes à la preuve comme Coq.

  *)
