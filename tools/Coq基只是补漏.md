# Coq基只是补漏

标签（空格分隔）： 未分类

---
```
Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.
  
  Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

```

Coq有自己的module系统
```
(** _Technical digression_: Coq provides a fairly sophisticated
    _module system_, to aid in organizing large developments.  In this
    course we won't need most of its features, but one is useful: If
    we enclose a collection of declarations between [Module X] and
    [End X] markers, then, in the remainder of the file after the
    [End], these definitions will be referred to by names like [X.foo]
    instead of just [foo].  Here, we use this feature to introduce the
    definition of the type [nat] in an inner module so that it does
    not shadow the one from the standard library. *)

Module Playground1.

```
来个例子来说明以下module的情况，coq的标准库环境
```
Module exampleenv
Inductive nat : Type :=
  | O : nat
  | S (n: nat) : nat.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.
  
Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.
  
Definition succ(n:nat) :nat := 
match n with
| O => S O
| _ => S n
end.

pred 1
End exampleenv

exapmleenv.pred 1
```
Print Playground1.nat.
Print nat.

他们的区别
[1]
[2]
Inductive nat : Set :=  O : nat | S : nat -> nat
For S: Argument scope is [nat_scope]

---
```
(** We can make numerical expressions a little easier to read and
    write by introducing "notations" for addition, multiplication, and
    subtraction. *)

Notation "x + y" := (plus x y)  
                       (at level 50, left associativity) 
                       : nat_scope.

```

(** The next line imports all of our definitions from the
    previous chapter. *)
Require Export Basics.

the string
    library (just for the concrete syntax of quoted strings) and the
    [Ltac] command, which allows us to declare custom tactics.  Kudos
    to Aaron Bohannon for this nice hack! *)

Require String. 
Open Scope string_scope. //告诉coq那些是什么意思

```
Require Export Imp
Require string
Open scope string_scope
Notation "e '||' n" := (aevalR e n) : type_scope.
```
Module就是相当于类一样，是个封装，以免重复定义冲突。
然后一个文件可以有好几个类，情况就是这个样子。
Require Exprot Bascis(相当于improt 类一样阿，但是它是文件)
访问里面的就需要用
xxx.pred

然后标准库的区别呢。

(* ####################################################### *)
(** ** The [omega] Tactic *)

(** The [omega] tactic implements a decision procedure for a subset of
    first-order logic called _Presburger arithmetic_.  It is based on
    the Omega algorithm invented in 1992 by William Pugh.

    If the goal is a universally quantified formula made out of

      - numeric constants, addition ([+] and [S]), subtraction ([-]
        and [pred]), and multiplication by constants (this is what
        makes it Presburger arithmetic),

      - equality ([=] and [<>]) and inequality ([<=]), and

      - the logical connectives [/\], [\/], [~], and [->],

    then invoking [omega] will either solve the goal or tell you that
    it is actually false. *)

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

(** Leibniz wrote, "It is unworthy of excellent men to lose
    hours like slaves in the labor of calculation which could be
    relegated to anyone else if machines were used."  We recommend
    using the omega tactic whenever possible. *)


While in the initial state, many operations and predicates of Peano’s arithmetic are defined, further operations and results belong to other modules. For instance, the decidability of the basic predicates are defined here. This is provided by requiring the module Arith.

Figure 3.5 describes notation available in scope nat_scope.
```
Notation "x + y" := (plus x y) 
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x - y" := (minus x y) 
                       (at level 50, left associativity) 
                       : nat_scope
```
