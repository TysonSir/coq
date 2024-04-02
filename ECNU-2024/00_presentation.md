
# Table of Contents

1.  [How to find me and support material](#orgdd1e4b0)
2.  [On your machine, install](#orgac63b8c)
3.  [Objectives](#org871be56)
    1.  [What do you prefer:](#org34bf601)
        1.  [If you are in the first category,](#org27d3423)
        2.  [If you are in the second category,](#org2fb363e)
        3.  [With Coq, doing maths becomes an IA](#orgd7b6793)
4.  [An ubiquitous concept coming from computer science: TREES](#org9561c81)
5.  [Coq: a proof assistant based on Type Theory](#orgf67274a)
    1.  [Proof](#org0b0268f)
    2.  [Assistant](#orgb0e8653)
    3.  [Type Theory](#org3234e29)

Certified programs and proofs in Coq, OCaml and dependent Type Theory
Jean-François Monin, Verimag, Univ Grenoble Alpes
jean-francois.monin@univ-grenoble-alpes.fr


<a id="orgdd1e4b0"></a>

# How to find me and support material

    search engine -> monin verimag
    https://www-verimag.imag.fr/~monin/
       -> Teaching material for students -> ECNU-2024
       https://www-verimag.imag.fr/~monin/Enseignement/ECNU-2024


<a id="orgac63b8c"></a>

# On your machine, install

-   Coq
-   OCaml
-   for editing: coqide or emacs+proof-general

For them opam (pck manager for OCaml) is a good choice.

Possible alternative: vscode.

I use emacs+proof-general (independent from opam).

A basic installation will be enough (otherwise it may take time)


<a id="org871be56"></a>

# Objectives


<a id="org34bf601"></a>

## What do you prefer:

-   create an exciting program?
-   or read/write a boring scientific paper?


<a id="org27d3423"></a>

### If you are in the first category,

Coq is for you.


<a id="org2fb363e"></a>

### If you are in the second category,

Coq is for you as well:
Supporting paper-and-pencil elliptic "proofs" by a 
machine-checked formal developement became a standard in
prominent conferences such as POPL.


<a id="orgd7b6793"></a>

### With Coq, doing maths becomes an IA

1.  IA =

    Interesting Activity
    YOU become more intelligent, 
    because you are doomed to UNDERSTAND what you are doing,
    
    -   Don't rush on the next exercises.
        Understand what you are doing, read the feedback of Coq.
    -   In this course I'll refrain to use dark magics.
        Everything will be explained in terms of elementary steps
        that are expected to be easy to follow.

2.  Disclaimer

    Using Coq is an addictive game


<a id="org9561c81"></a>

# An ubiquitous concept coming from computer science: TREES

-   data structures
    e.g. binary trees, lists, Peano natural numbers
-   AST (Abstract Syntax Trees)
-   Proofs seen as proof trees
-   Operational semantics


<a id="orgf67274a"></a>

# Coq: a proof assistant based on Type Theory


<a id="org0b0268f"></a>

## Proof

It is about mathematical reasoning.
Makes sense in (usual) Maths and in Computer Science,
which can be seen as a special branch of maths.

We will focus on Computer Science, in particular we will rely
on intuitions and knowledge famiiar to programmers:
no background on analysis, geometry or even Set Theory
is needed.
But we expect some familiarity with 
&#x2013; data structures, especially recursive data structures 
   such as trees and lists
&#x2013; programming, especially recursive programs
   (our programs we be called functions)
&#x2013; basic notions on typing, however this topic will be
   developed a lot.


<a id="orgb0e8653"></a>

## Assistant

Coq is a software interactive tool helping the user to
develop definitions and theorems in an **interactive** way.
Ideally: <span class="underline">clever</span> inputs are entered by the human user, whereas 
<span class="underline">tedious</span> details are machine-checked.
In practice: to be discussed; anyway the proof-checking performed
in tools like Coq is actually <span class="underline">very secure</span> by design. Kernel based.


<a id="org3234e29"></a>

## Type Theory

An extension of a well-known good practice in programming.
The usual tension between benefits and constraints disappears
thanks to the power of polymorphism and dependent types.
PASCAL ADA.

