Require Import  month.

Definition is_January : month -> Prop :=
 month_rect (fun m => Prop) 
  True
  False
  False
  False
  False
  False
  False 
  False
  False
  False
  False
  False.
 
Eval compute in (is_January February).

Eval compute in (is_January January).


(* alternate solution *)
Reset is_January.
  
Definition is_January (m : month) : Prop :=
 match m with
 | January => True 
 | other_month => False
 end.

Print is_January.
