Require Export Eqdep.
 
Section update_def.
Variables (A : Set) (A_eq_dec : forall (x y : A),  { x = y } + { x <> y }).
Variables (B : A ->  Set) (a : A) (v : B a) (f : forall (x : A),  B x).
 
(* should be eq_rec *)

Definition update (x : A) : B x :=
   match A_eq_dec a x with
     left h => eq_rect a B v x h   
    | right h' => f x
   end.
 
End update_def.
 
Theorem update_eq:
 forall (A : Set) (eq_dec : forall (x y : A),  { x = y } + { x <> y })
        (B : A ->  Set) (a : A) (v : B a) (f : forall (x : A),  B x),
  update A eq_dec B a v f a = v.
Proof.
intros A eq_dec B a v f.
unfold update.
case (eq_dec a a).
intros e.  
rewrite <- eq_rect_eq.
auto.
intros Hneq; elim Hneq; trivial.
Qed.
