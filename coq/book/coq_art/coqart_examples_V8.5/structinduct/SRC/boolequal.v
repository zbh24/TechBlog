
Theorem bool_equal : forall b:bool, b = true \/ b = false.
Proof
  bool_ind (fun b:bool => b = true \/ b = false)
    (or_introl _ (refl_equal true)) (or_intror _ (refl_equal false)).


Theorem bool_equal' : forall b:bool, b = true \/ b = false.
Proof.
 intro b; pattern b; apply bool_ind; [ left | right ]; reflexivity.
Qed. 

    


