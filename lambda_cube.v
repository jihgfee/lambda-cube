(** OBS: Work in progress. Do not take at face value, as some correspondences are
not entirely formal. *)

(**
The road to logic programming, in terms of the Barendregt cube (also called the lambda cube).
By Jonas Kastberg Hinrichsen
*)

(**
This file seeks to provide an understanding of the "what"'s and "how"'s
of logic programming, while we won't be much concerned with the "why's".

The "what"'s:
Logic programming is about "programming" the proofs of mathematical statements.
That is, by letting the compiler act as a strict referee, that oversees that we
carry out our proofs according to sound logical rules.
This is to improve the trustworthyness of proofs, which can otherwise become
hard to parse on pen and paper.

The "how"s:
We achieve logic programming by using an approach known as the
"curry-howard correspondence", which coins that "propositions are types" and
"programs are proofs".
What this means is that we will describe the propositions that we set out to
prove as types in the language, e.g. a type could be: TwoPlusTwoEqualsFour.
A term, or program, of that type can then be thought of as a proof that the
proposition holds.
As such, we can check that our proofs are sound using type checking.
To write expressive propositions, and proofs thereof, we thus need a highly
sophisticated type system.

The state of the art in this direction is what we call the
"Calculus of Constructions" (CoC), which is the basis of the Coq type system
(hence its name).

The calculus of construction is the apex of the so-called barendregt cube,
coined by Henk Barendregt, which illustrates three distinct extensions to
the conventional functional type system:
- Abstraction over types in terms
- Abstraction over types in types
- Abstraction over terms in types

In this file, we demonstrate how each of the three extensions allow us to model
specific properties in a logic, and how the properties are reflected in Coq.
*)

(** λ→, Standard strongly typed functional programming *)
(* We first consider a simply typed language, and the foundation of our logic *)
(* In a simply typed setting, we can create new types, each with their own set of constructors *)

(* Common examples of such types are the following *)
Module type_def_example.
  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.
  
  Inductive nat_list : Type :=
  | nat_nil : nat_list                      (* [] *)
  | nat_cons : nat -> nat_list -> nat_list. (* x :: xs *)
End type_def_example.

(* At the foundation of our logic we have the truth-values: True and False *)

(* The type of True propositions have _one_ constructor, with no arguments *)
(* That is to model the fact that we can _always_ prove True---it holds trivially *)
Inductive TTrue : Type :=
  | I : TTrue
.

(* The exact opposite is the case for False propositions, which has _no_ constructor *)
(* That is to model the fact that we can _never_ prove False---Obtaining False will in fact lead to a contradiction as will be shown later *)
Inductive FFalse : Type := .

(* We can now "prove" True propositions as follows---by using the I constructor *)
Definition True_unit : TTrue := I.
(* Similarly, we can illustrate how it is impossible to construct a proof of False *)
Fail Definition False_unit : FFalse := _.

(* A natural consequence of considering proofs as types is that we obtain
logical implication, being functions, for free! *)
(* That is, defining, and proving the logical proposition True -> True,
can be done as follows. *)
Definition True_impl_True : TTrue -> TTrue :=
  fun _ => I.

(* Conversely, we can show that we can prove False "assuming" False. *)
(* In particular, we take a term of "False" as input, and immediately use it
to construct the goal *)
Definition False_impl_False : FFalse -> FFalse :=
  fun HF => HF.

(* Alternatively, we can leverage the fact that False has no constructors,
by matching on it, and then construct the output for each constructor
(of which there are none!) *)
Definition False_impl_True : FFalse -> TTrue :=
  fun HF => match HF with end.

(* While this is a good start, we dont get much further, as our type system is *)
(* not expressive enough *)
(* We thus introduce the first Barendregt cube extension, parametric polymorphism *)

(* λ2, Parametric polymorphism! *)

(**
Parametric polymorphism introduces the "pi-type" (Πx:∗,T) to the type system.
This allow us to abstract over types in our terms.
Practically speaking, it is what allows us to define generic functions.

A common example of such a function is the following:
*)
Module parametric_polymorphism_example.
  (* The generic identity function *)
  Definition id : forall (T : Type), T -> T :=
    fun (T : Type) (t : T) => t.
End parametric_polymorphism_example.

(** With parametric polymorphism we can capture generic propositions,
such as "P implies P": P -> P *)
Definition P_id : forall (P : Type), P -> P :=
  fun (P : Type) (HP : P) => HP.
(** The term is identical to the identity function (up to renaming),
as we simply return the function argument (the assumption), as it serves as
proof that the conclusion holds. *)

(* Additionally, we can show how False implies anything (any P) *)
Definition ex_falso : forall (P : Type), FFalse -> P :=
  fun (P : Type) (HF : FFalse) => match HF with end.

(** In particular, as the argument (here FFalse), is "assumed" to hold
(i.e. that an instance of it exists), we can pattern match on it.
We then have to construct an instance of P for all of the constructors of False.
However, since False have no constructors (by its definition), this is trivial
(as there are no cases). *)

(** It is now time to enrich our logic with more interesting propositions,
namely, conjunction and disjunction.
To do this, we utilise another extension of the Barendregt cube: Type formers *)

(** λ_ω: Type formers! *)
(* The λ_ω extension formally means that "types can abstract over types" *)
(* More practically, this means that we can have type definitions of the form
Type -> ... -> Type *)

(* A common example of such a type former is the following *)
Module type_former_example.
  Inductive List (T : Type) : Type :=
  | nil : List T
  | cons : T -> List T -> List T.
  (* Some examples of languages with type formers are: *)
  (* Haskell, Scala *)

End type_former_example.

(** We define the type of logical conjunction (/\) as a type former
over two "propositions" (Types) P and Q.
The type has has one constructor with two arguments, one of each proposition
This intuitively means that to construct a "proof" of a conjunction P /\ Q,
we must "prove" both of the conjuncts P and Q *)
Inductive and : Type -> Type -> Type :=
  conj : forall (P Q : Type), P -> Q -> and P Q.
(** Note how we use both type formers and parametric polymorphism here.
We use type formers to construct the type of /\, which depends on two types,
notably those of P and Q.
In the constructor, we use parametric polymorphism to allow constructing generic
instances of the conjuction, e.g. True /\ False, (True /\ True) /\ False, etc.
 *)

(** The above notation is a bit superfluous, and thus Coq provides the following
syntactic sugar, which merges the type former arguments (Type -> Type -> _), with
the type abstractions in the term (forall (P Q : Type), _)  *)
Reset and.
Inductive and (P Q : Type) : Type :=
  conj : P -> Q -> and P Q.
(** OBS: There is some subtle difference between the two definitions.
 Explanation is TBD. *)

(* We can now express logical propositions such as "True /\ True",
and prove it by providing constructing both arguments (using the constructor I) *)
Definition True_and_True' : and TTrue TTrue :=
  conj TTrue TTrue I I.
(** We see a bit more repetition between the type arguments for `and`,
and those of the constructor `cons`.
In fact, the type arguments of `cons` can be inferred from `and`. *)

(** We can instruct Coq to try and _infer_ the type arguments of a `conj`,
using the following command. *)
Arguments conj {_ _} _ _.

(** Additionally, to make our propositions a bit more legible, Coq lets us
define custom notation for our definitions, such as the following for the
conjunction type. *)
Notation "P /\ Q" := (and P Q) : type_scope.

(** We can then construct the same proposition and proof as before, using the
following notation. *)
Definition True_and_True : TTrue /\ TTrue :=
  conj I I.

(** The following example illustrates how we cannot construct a proof of the
type True /\ False, even though we can construct the type (proposition). *)
Fail Definition True_and_False : TTrue /\ FFalse :=
  conj I _.

(** We can similarly add disjunctions (P \/ Q) to our logic as follows. *)
Inductive or (P Q : Type) : Type :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.
(** Dijunctions holds whenever either of the constituents hold.
To capture this, the type has two constructors, each depending on a term of one
of the type arugments P or Q. *)

(** Similar to before we let Coq infer the type arguments for the constructors,
and add custom notation for the type former. *)
Arguments or_introl {_ _} _.
Arguments or_intror {_ _} _.
Notation "P \/ Q" := (or P Q) : type_scope.

(** We can then construct propositions, and proofs thereof, as follows: *)
Definition True_or_True_l : TTrue \/ TTrue :=
  or_introl I.
(** Here we use the left constructor for the proposition, which is satisfiable
with either. *)

(** Similarly, we here construct a different term (proof) of the same type
(proposition) *)
Definition True_or_True_r : TTrue \/ TTrue :=
  or_intror I.

(** Some proposition require us to pick the correct constructor.
One such is the following which can only be proven using the right constructor. *)
Definition True_or_False_l : TTrue \/ FFalse :=
  or_introl I.

(** Finally, some propositions are still unsatisfiable such as the following. *)
Fail Definition False_or_False : or FFalse FFalse := _.

(** Up until this point we have mostly shown how we can construct proofs of
propositions based on type formers, but not how we can use them as assumptions. *)

(** The following is a proposition and proof capturing how the conjunction
P /\ Q implies the proposition P. *)
Definition conj_proj_1 : forall (P Q : Type), P /\ Q -> P :=
  fun (P Q : Type) (HPQ : P /\ Q) =>
    match HPQ with
    | conj HP HQ => HP
    end.
(** The type is defined using paremtric polymorphism and the type former for
conjunction.
The proof first takes the polymorphic types P and Q, and then _evidence_, that the
assumption P /\ Q holds (named HPQ).
This is similar to the identity proof that we saw previously.
To construct the proof of our conclusion (P), we pattern match on the assumption
HPQ, which has one constructor, consisting of evidence that both of the
constituents hold (HP : P) and (HQ : Q).
We then construct the proof using HP, as required by the conclusion. *)

(** A similar proposition and proof for the right conjunct is as follows. *)
Definition conj_proj_2 : forall (P Q : Type), P /\ Q -> Q :=
  fun (P Q : Type) (HPQ : P /\ Q) =>
    match HPQ with
    | conj HP HQ => HQ
    end.

(** It can also be necessary to use both constructor as illustrated by the
following proof, which states that P /\ Q implies Q /\ P. *)
Definition conj_sym : forall (P Q : Type), P /\ Q -> Q /\ P :=
  fun (P Q : Type) (HPQ : P /\ Q) =>
    match HPQ with
    | conj HP HQ => conj HQ HP
    end.
(** We again pattern match on the assumption HPQ, which gives us evidence that
both P and Q hold. We then proof the conclusion using the constructor for
conjunction, where we simply flip the proposition arguments *)

(** The use of type formers let us extend our logic quite substantially,
however we can still only express propositions made up of True and False.
To construct more interesting propositions we then use the final Barendregt
cube extension: Dependent types! *)

(* λP, Dependent types! *)
(* λ_ω + λ2 + λP = λC *)

(**
Dependent types let us abstract over terms in types.
More intuitively, this means that we can define types e.g. of the form:
nat -> Type
 *)

(* A common example of such a type former is the following *)
Module dependent_type_example.
  Inductive SizedList (T : Type) : nat -> Type :=
  | sized_nil : SizedList T O
  | sized_cons : forall (n : nat), T -> SizedList T n -> SizedList T (S n).
  (** This is a so-called sized list, where the type carries the lists lenght. *)
  (** With this we can more accurately capture the properties of the list,
   and of the functions on it. e.g. the append function would have the type:
   list n T -> list m T -> list (n+m) T

   The downside is that it can be difficult to satisfy the type checker. *)
End dependent_type_example.

(** With dependent types we can capture _predicates_, i.e. propositions that
depend on terms.
One important such predicate is that of equality. *)
Inductive eq (A : Type) (x : A) : A -> Type :=
  eq_refl : eq A x x.
(** The type takes three arguments: The type of the terms, and two terms.
The only constructor of the type captures that both of the term arguments must be
_syntactically_ identical. *)

(** Like before, we let Coq infer the type parameter, and add syntactic sugar
for the type. *)
Arguments eq {_} _ _.
Notation "x = y" := (eq x y) : type_scope.

(** An example of a proposition and proof using equality is the following.
This captures the symmetry of equality, i.e. that x = y implies that y = x. *)
Definition eq_sym : forall (A : Type) (x y : A), x = y -> y = x :=
  fun (A: Type) (x y : A) (H : x = y) =>
  match H with                (* Unifies y -> x *)
  | eq_refl _ _ => eq_refl A x (* Resolves since eq_refl A x : x = x *)
  end.
(** The proof matches on the hypothesis H, which gives us the single case of
the [eq_refl] constructor.
By its definition, we can infer that the value [x] is syntactically equivalent
to [y], as the constructor only holds for such syntactically equivalent values.
As such, the [x] and [y] of the conclusion [y = x] are "unified", meaning that
all their occurences are merged.
As such, the type of the conclusion ends up as [eq A x x], for which [eq_refl A x]
is a constructor. *)
