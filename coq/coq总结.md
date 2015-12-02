#Coq总结
coq里面所有的函数都支持柯里化
:表示类型
：=表示定义为

[1]
定义函数，defintion 和 fixpoint
```
Fixpont length(L:list nat):nat :=
| O =>0
| CONS n ls => S (length (ls))

length: list -> nat
//length这个函数的类型是list -> nat
```

[2]
定义类型，有点枚举的意思
```
Inductive natprod: Type :=
pair: nat ->nat ->natprod.

Inductive nat:Type :=
| O:nat
| S:nat->nat.

Inductive option(X:type) :Type :=
| None:option X
| Some：X->option X.

//明白了
//:表示类型
//：=表示定义为
Inductive ev:nat ->Prop :=
| ev_0:ev 0
| ev_SS :vn:nat ,ev n -> ev S (S n)).

```

[3]
In Coq, "A : Prop" means you have something named "A" of type "Prop". In the future you will see "0 : nat" which means "0" of type "nat" (natural numbers) and you will see "true : bool" which means "true" of type "bool" (boolean or true-false values). In some places, you will see "A B C : Prop", which means "A", "B", and "C" all have type "Prop".
```
Inductive False : Prop := .

Inductive True : Prop :=
  | I : True.

Inductive bool : Set :=
  | true : bool
  | false : bool.
```
"true" and "false" have type "bool" and "bool" has type "Set". "Set" is the type of normal datatypes, like "bool" and natural numbers and most of the other types you'll see. The exception is propositions, which have type "Prop".

```
Inductive list (A : Type) : Type :=
 | nil : list A
 | cons : A -> list A -> list A.
```
I'll address the type "Type" in a second, but for the moment know that a list takes a type called "A" and is either empty - constructed using "nil" - or a node containing a value of type "A" and a link to another list.

In a number of earlier places, I've ignored the type "Type". It hides some magic in Coq. We saw early on that "proof_of_A" was a proof and had type "A", which was a proposition. "A", since it was a proposition, had type "Prop". But if types can have types, what type does "Prop" have? The answer is "Type(1)". The answer to your next N questions is that "Type(1)" has type "Type(2)". "Type(2)" has type "Type(3)". Etc.

Similarly, "true" had type "bool". "bool" had type "Set". And "Set" has type "Type(1)" (just like "Prop").

Coq hides this infinite hierarchy from the user with the magic type "Type". When you use "Type", Coq will determine if the value lies in "Prop", "Set", or any of the the "Type(...)" types.

Going back to lists, there is an operator for building a list.
Infix "::" := cons (at level 60, right associativity) : list_scope.
So, the value "5 :: 4 :: nil" would be a "list nat" containing the values 5 and 4.
A simple function that works on all types of lists is "length":

```
Definition length (A : Type) : list A -> nat :=
  fix length l :=
  match l with
   | nil => O
   | _ :: l' => S (length l')
  end.
```
 "partial evaluation" is passing only some of the arguments to a function. In Coq, and many functional languages, the result is a new function where the supplied arguments are now treated like constants in the function and the remaining parameters are can still be passed in.
 
```

"Theorem" starts a proof.
"Qed" ends a proof.
"Definition" declares a function.
"Fixpoint" declares a recursive function.
"Inductive" declares data types.
"Notation" creates new operators.
"Infix" also creates new operators.
"Show Proof" prints out the current state of the proof.
"Require Import" reads in definitions from a file.
"Check" prints out a description of a type.
"Compute" prints out the result of a function call. 
```
