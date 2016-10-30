Require Export Bool.

Inductive binary_word : nat -> Set :=
  empty_binary_word :  binary_word 0
| cons_binary_word :
   forall p:nat, bool -> binary_word p -> binary_word (S p).

Theorem discriminate_O_S : forall p, 0=S p -> False.
Proof.
 intros;discriminate.
Qed.

Theorem discriminate_S_O : forall p, S p=0 -> False.
Proof.
 intros;discriminate.
Qed.

Implicit Arguments discriminate_S_O.
Implicit Arguments discriminate_O_S.

Fixpoint binary_word_or (n:nat)(w1:binary_word n) {struct w1}:
    binary_word n -> binary_word n :=
 match w1 in binary_word p return binary_word p -> binary_word p with
   empty_binary_word =>
     (fun w2:binary_word 0 =>
        match w2 in binary_word p' return p'=0->binary_word p' with
          empty_binary_word =>
            (fun h => empty_binary_word)
        | cons_binary_word q b w2' =>
            (fun h => False_rec (binary_word (S q)) (discriminate_S_O h))
        end (refl_equal 0))
  | cons_binary_word q b1 w1' =>
      (fun w2:binary_word (S q) =>
        match w2 in binary_word p' return S q=p'->binary_word p' with
          empty_binary_word =>
            (fun h => False_rec (binary_word 0) (discriminate_S_O h))
        | cons_binary_word q' b2 w2' =>
            (fun h =>
               cons_binary_word q'
                  (orb b1 b2)
                  (binary_word_or q'
(* this use of eq_rec transforms w1' into an element of (binary_word (S q'))
    instead of (binary_word (S q)), thanks to the equality h. *)
                    (eq_rec (S q)
                      (fun v:nat => binary_word (pred v))
                      w1'
                      (S q')
                      (h:S q=S q'))
                      w2'))
         end (refl_equal (S q)))
  end.
