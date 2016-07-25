# Sf学习之路之sf的第二部分

标签（空格分隔）： 未分类

---

根据roadmap，我目前已经学习到了：

一,Hoare.v

Idea: create a domain specific logic for reasoning about properties of Imp programs.
This hides the low-level details of the semantics of the program
Leads to a compositional reasoning process
The basic structure is given by Hoare triples of the form:
  {{P}} c {{Q}}
P and Q are properties about the state of the Imp program
"If command c is started in a state satisfying assertion P, and if c eventually terminates in some final state, then this final state will satisfy the assertion Q."

Sometimes the preconditions and postconditions we get from the Hoare rules won't quite be the ones we want in the particular situation at hand — they may be logically equivalent but have a different syntactic form that fails to unify with the goal we are trying to prove, or they actually may be logically weaker (for preconditions) or stronger (for postconditions) than what we need.

Hoare Logic Rules (so far):


二.Hoare2
1）
修饰程序（Decorated Programs）：让程序自带证明，来非形式化地说明程序的正确性。
p{S}q:霍尔三元组，表示每当对于程序段的输入p为真时，就有q为真。

空语句公理:$$   \frac{}{\{P\}\ \textbf{skip}\ \{P\}} \! $$

赋值公理：
$$  \frac{}{\{P[E/x]\}\ x:=E \ \{P\} } \! $$
{P[e/x]}x := e {P}
这里的P[E/x]指示表达式P中变量x的所有自由出现都被替代为表达式E
例子：
{x+1=43  x=42} y:=x + 1 {y=43  x=42\}

顺序规则：$$  \frac {\{P\}\ S\ \{Q\}\ , \ \{Q\}\ T\ \{R\} } {\{P\}\ S;T\ \{R\}} \! $$
条件规则：$$ \frac { \{B \wedge P\}\ S\ \{Q\}\ ,\ \{\neg B \wedge P \}\ T\ \{Q\} }
              { \{P\}\ \textbf{if}\ B\ \textbf{then}\ S\ \textbf{else}\ T\ \textbf{endif}\ \{Q\} } \! $$
while规则:

$$ \frac { \{P \wedge B \}\ S\ \{P\} }
              { \{P \}\ \textbf{while}\ B\ \textbf{do}\ S\ \textbf{done}\ \{\neg B \wedge P\} }
\!  $$

推论规则：$$ 
\frac {  P^\prime \rightarrow\ P\ ,\ \lbrace P \rbrace\ S\ \lbrace Q \rbrace\ ,\ Q \rightarrow\ Q^\prime }
{ \lbrace  P^\prime\ \rbrace\ S\ \lbrace Q^\prime\rbrace }
\!
 $$

2）目标：we explain in detail how to construct decorations for several simple programs that don't involve non-trivial loop invariants.
1.下面给出几个例子，给程序的每一步写出specifications。
复制语句序列

```
 X ::= X + Y;;
 Y ::= X - Y;;
 X ::= X - Y;;

 (1)     {{ X = m ∧ Y = n }} ⇾
 (2)     {{ (X + Y) - ((X + Y) - Y) = n ∧ (X + Y) - Y = m }}
        X ::= X + Y;;
 (3)     {{ X - (X - Y) = n ∧ X - Y = m }}
        Y ::= X - Y;;
 (4)     {{ X - Y = n ∧ Y = m }}
        X ::= X - Y
 (5)     {{ X = n ∧ Y = m }}
 
```

明白了，直接替换就好了。
 
 2.
条件语句序列：

```
if x < y then
    z=y-x
else
    z=x-y
fi
We start with the outer precondition (1) and postcondition (8).

(1)     {{True}}
       IFB X ≤ Y THEN
 (2)       {{True ∧ X ≤ Y}} ⇾
 (3)       {{(Y - X) + X = Y ∨ (Y - X) + Y = X}}
         Z ::= Y - X
 (4)       {{Z + X = Y ∨ Z + Y = X}}
       ELSE
 (5)       {{True ∧ ~(X ≤ Y) }} ⇾
 (6)       {{(X - Y) + X = Y ∨ (X - Y) + Y = X}}
         Z ::= X - Y
 (7)       {{Z + X = Y ∨ Z + Y = X}}
       FI
 (8)     {{Z + X = Y ∨ Z + Y = X}}

```

3.
while语句序列：Trivial loop语句
```
 (1)    {{ True }} ⇾
 (2)    {{ n × 0 + m = m }}
      X ::= m;;
 (3)    {{ n × 0 + X = m }}
      Y ::= 0;;
 (4)    {{ n × Y + X = m }}
      WHILE n ≤ X DO
 (5)      {{ n × Y + X = m ∧ n ≤ X }} ⇾
 (6)      {{ n × (Y + 1) + (X - n) = m }}
        X ::= X - n;;
 (7)      {{ n × (Y + 1) + X = m }}
        Y ::= Y + 1
 (8)      {{ n × Y + X = m }}
      END
 (9)    {{ n × Y + X = m ∧ X < n }}
```
4.Finding Loop Invariants
Once the outermost precondition and postcondition are chosen, the only creative part in verifying programs with Hoare Logic is finding the right loop invariants. The reason this is difficult is the same as the reason that doing inductive mathematical proofs requires creativity: strengthening the loop invariant (or the induction hypothesis) means that you have a stronger assumption to work with when trying to establish the postcondition of the loop body (complete the induction step of the proof), but it also means that the loop body postcondition itself is harder to prove!

下面教导你如何去找循环不变式：
Example: Slow Subtraction(缓慢减少方法)
```
 {{ X = m ∧ Y = n }}
           WHILE X ≠ 0 DO
             Y ::= Y - 1;;
             X ::= X - 1
           END
             {{ Y = n - m }}
```

```
(1)      {{ X = m ∧ Y = n }}  ⇾     (a)
    (2)      {{ I }}
           WHILE X ≠ 0 DO
    (3)        {{ I ∧ X ≠ 0 }}  ⇾      (c)
    (4)        {{ I[X ↦ X-1][Y ↦ Y-1] }}
             Y ::= Y - 1;;
    (5)        {{ I[X ↦ X-1] }}
             X ::= X - 1
    (6)        {{ I }}
           END
    (7)      {{ I ∧ ~(X ≠ 0) }}  ⇾         (b)
    (8)      {{ Y = n - m }}
```
不管猜测，终于找出了循环不变式子：
```
  (1)      {{ X = m ∧ Y = n }}  ⇾               (a - OK)
    (2)      {{ Y - X = n - m }}
           WHILE X ≠ 0 DO
    (3)        {{ Y - X = n - m ∧ X ≠ 0 }}  ⇾    (c - OK)
    (4)        {{ (Y - 1) - (X - 1) = n - m }}
             Y ::= Y - 1;;
    (5)        {{ Y - (X - 1) = n - m }}
             X ::= X - 1
    (6)        {{ Y - X = n - m }}
           END
    (7)      {{ Y - X = n - m ∧ X = 0 }}  ⇾       (b - OK)
    (8)      {{ Y = n - m }}
```
Example: Parity
Example: Finding Square Roots
```
      {{ X=m }}
    Z ::= 0;;
    WHILE (Z+1)*(Z+1) ≤ X DO
      Z ::= Z+1
    END
      {{ Z×Z≤m ∧ m<(Z+1)*(Z+1) }}
```
Very often, if a variable is used in a loop in a read-only fashion (i.e., it is referred to by the program or by the specification and it is not changed by the loop) it is necessary to add the fact that it doesn't change to the loop invariant.

Weakest Preconditions
```
{{ Y ≤ 4 }}  X ::= Y + 1  {{ X ≤ 5 }}
```
In other words, Y ≤ 4 is the weakest valid precondition of the command X ::= Y + 1 for the postcondition X ≤ 5.

In general, we say that "P is the weakest precondition of command c for postcondition Q" if {{P}} c {{Q}} and if, whenever P' is an assertion such that {{P'}} c {{Q}}, we have P' st implies P st for all states st.

三：Small-setp

The evaluators we have seen so far (e.g., the ones for aexps, bexps, and commands) have been formulated in a "big-step" style — they specify how a given expression can be evaluated to its final value (or a command plus a store to a final store) "all in one big step."

But there are some things it does not do well. In particular, it does not give us a natural way of talking about concurrent programming languages, where the "semantics" of a program — i.e., the essence of how it behaves — is not just which input states get mapped to which output states, but also includes the intermediate states that it passes through along the way, since these states can also be observed by concurrently executing code.

A much more natural approach is simply to say that the behavior of an expression like 2+nil is undefined — it doesn't evaluate to any result at all. And we can easily do this: we just have to formulate aeval and beval as Inductive propositions rather than Fixpoints, so that we can make them partial functions instead of total ones.

As a first step, we need a different way of presenting the semantics that allows us to distinguish nontermination from erroneous "stuck states."
```
Inductive tm : Type :=
  | C : nat -> tm         (* Constant *)
  | P : tm -> tm -> tm.   (* Plus *)
```

```
如果是bigstep，就是这样EVAL的。
一种是定义操作的
Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P a1 a2 => evalF a1 + evalF a2
  end.

一种是定义relation的
Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n || n
  | E_Plus : forall t1 t2 n1 n2, 
      t1 || n1 -> 
      t2 || n2 ->
      P t1 t2 || (n1 + n2)

  where " t '||' n " := (eval t n).

```
大步语义
```
(** 
                               --------                                (E_Const)
                               C n || n

                               t1 || n1
                               t2 || n2
                           ------------------                          (E_Plus)
                           P t1 t2 || n1 + n2
*)

```
小步语义

```
(** Now, here is a small-step version. *)
(** 
                     -------------------------------        (ST_PlusConstConst)
                     P (C n1) (C n2) ==> C (n1 + n2)

                              t1 ==> t1'
                         --------------------                        (ST_Plus1)
                         P t1 t2 ==> P t1' t2

                              t2 ==> t2'
                      ---------------------------                    (ST_Plus2)
                      P (C n1) t2 ==> P (C n1) t2'
*)
```
小步语义的定义
```
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) ==> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ==> t1' ->
      P t1 t2 ==> P t1' t2
  | ST_Plus2 : forall n1 t2 t2',
      t2 ==> t2' -> 
      P (C n1) t2 ==> P (C n1) t2'

  where " t '==>' t' " := (step t t').
```
一个很好的小步语义的例子来说明这个道理
```
Example test_step_1 : 
      P 
        (P (C 0) (C 3))
        (P (C 2) (C 4))
      ==>
      P 
        (C (0 + 3))
        (P (C 2) (C 4)).
Proof.
  apply ST_Plus1. apply ST_PlusConstConst.  Qed.
```

```
Inductive value : tm -> Prop :=
  v_const : forall n, value (C n).
Check v_const 3.
```
使用VALUE的优美定义
```
(** Having introduced the idea of values, we can use it in the
    definition of the [==>] relation to write [ST_Plus2] rule in a
    slightly more elegant way: *)

(** 
                     -------------------------------        (ST_PlusConstConst)
                     P (C n1) (C n2) ==> C (n1 + n2)

                              t1 ==> t1'
                         --------------------                        (ST_Plus1)
                         P t1 t2 ==> P t1' t2

                               value v1
                              t2 ==> t2'
                         --------------------                        (ST_Plus2)
                         P v1 t2 ==> P v1 t2'
*)
```
这是最新的形式化定义
```
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          P (C n1) (C n2)
      ==> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 ==> t1' ->
        P t1 t2 ==> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 ->                     (* <----- n.b. *) 
        t2 ==> t2' ->
        P v1 t2 ==> P v1 t2'

  where " t '==>' t' " := (step t t').
```
这是最新的定义
```
The definition of single-step reduction for our toy language is fairly simple, but for a larger language it would be pretty easy to forget one of the rules and create a situation where some term cannot take a step even though it has not been completely reduced to a value. The following theorem shows that we did not, in fact, make such a mistake here.
```
这是最新定义
```
Theorem strong_progress : forall t,
  value t \/ (exists t', t ==> t').
  
This important property is called strong progress, because every term either is a value or can "make progress" by stepping to some other term. 
```