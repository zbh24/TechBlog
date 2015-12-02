Induction:
https://coq.inria.fr/tutorial-nahas

Lists are a common data structure in functional programming. (Imperative
programs use more arrays.) The definition of a singly-linked list in Coq is:
Inductive list (A : Type) : Type :=
 | nil : list A
  | cons : A -> list A -> list A.
  I'll address the type "Type" in a second, but for the moment know that a list
  takes a type called "A" and is either empty - constructed using "nil" - or a
  node containing a value of type "A" and a link to another list.
  In a number of earlier places, I've ignored the type "Type". It hides some
  magic in Coq. We saw early on that "proof_of_A" was a proof and had type "A",
  which was a proposition. "A", since it was a proposition, had type "Prop". But
  if types can have types, what type does "Prop" have? The answer is "Type(1)".
  The answer to your next N questions is that "Type(1)" has type "Type(2)".
  "Type(2)" has type "Type(3)". Etc.
  Similarly, "true" had type "bool". "bool" had type "Set". And "Set" has type
  "Type(1)" (just like "Prop").
  Coq hides this infinite hierarchy from the user with the magic type "Type".
  When you use "Type", Coq will determine if the value lies in "Prop", "Set", or
  any of the the "Type(...)" types.
  Going back to lists, there is an operator for building a list.
  Infix "::" := cons (at level 60, right associativity) : list_scope.
  So, the value "5 :: 4 :: nil" would be a "list nat" containing the values 5
  and 4.
  A simple function that works on all types of lists is "length":
  Definition length (A : Type) : list A -> nat :=
    fix length l :=
      match l with
         | nil => O
            | _ :: l' => S (length l')
              end.
              Just to get started, let's prove that adding an element to a list
              increases it's length by 1.


We often want to do more than just add one element at the front of a list. Coq
includes the function "app", short for "append", to concatenate two lists.
Definition app (A : Type) : list A -> list A -> list A :=
  fix app l m :=
    match l with
       | nil => m
          | a :: l1 => a :: app l1 m
            end.

            Infix "++" := app (right associativity, at level 60) : list_scope.
