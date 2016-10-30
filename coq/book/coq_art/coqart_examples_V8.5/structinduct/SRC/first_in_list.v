Require Export List.

Fixpoint first_in_list (A:Set)(f:A->bool)(l:list A){struct l}:option A :=
  match l with
    nil => None
  | a::tl =>
     match f a with
       true => Some a
     | false => first_in_list A f tl
     end
  end.