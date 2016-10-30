Require Import ZArith.

Inductive Z_btree : Set :=
 |  Z_leaf : Z_btree 
 | Z_bnode : Z->Z_btree->Z_btree->Z_btree.

Fixpoint value_present (z:Z)(t:Z_btree){struct t} : bool :=
   match t with
   | Z_leaf => false
   | Z_bnode z1  t1 t2 => if Zeq_bool z z1
                          then  true
                          else  if value_present z t1 
                                then true 
                                else value_present z t2
   end.


