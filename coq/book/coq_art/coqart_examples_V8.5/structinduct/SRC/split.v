Require Import List.

Open Scope type_scope.

Fixpoint split (A B: Set)(l: list (A * B)) {struct l} : (list A)*(list B) :=
 match l with nil => (nil, nil)
            | (a,b)::l' => (let (l'1,l'2) := split _ _ l' 
                           in (a::l'1, b::l'2))
         end.

Fixpoint combine (A B: Set)(l1 : list A)(l2 :list B){struct l1}: list (A*B):=
  match l1,l2 with nil,nil => nil
                 | (a::l'1),( b::l'2) => (a,b)::(combine _ _ l'1 l'2)
                 | _,_  => nil
  end.

Theorem combine_of_split : forall (A B:Set) (l:list (A*B)),
   let ( l1,l2) :=  (split _ _ l) 
   in combine _ _ l1 l2 = l.
Proof.
 simple induction l; simpl; auto.
 intros p l0; case (split A B l0); simpl; auto.
 case p; simpl; auto.
 destruct 1; auto. 
Qed.

