Require Import List.

Definition two_first (A:Set)(l:list A) : list A :=
 match l with a :: b :: l' => a :: b :: nil
            | other => (nil (A:=A))
 end.

Eval compute in (two_first _ (true::false::true::nil)).

Eval compute in (two_first _ ((6 * 6)::nil)).

Fixpoint firsts (A:Set)(n:nat)(l:list A){struct n}: list A :=
   match (n,l) with
     (0, l') => nil
   | (S n', nil) => nil
   | (S n', a::l') => a::(firsts _ n' l')
  end.

