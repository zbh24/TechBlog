Inductive binary_word : nat -> Set :=
  empty_binary_word :  binary_word 0
| cons_binary_word :
   forall p:nat, bool -> binary_word p -> binary_word (S p).

Fixpoint binary_word_concat
   (n:nat)(w1:binary_word n)(m:nat)(w2:binary_word m) {struct w1} :
      binary_word (n+m) :=
 match w1 in binary_word p return binary_word (p+m) with
   empty_binary_word => w2
 | cons_binary_word q b w1' =>
   cons_binary_word (q+m) b (binary_word_concat q w1' m w2)
 end.
