Inductive vehicle : Set :=
  | bicycle : nat -> vehicle 
  | motorized : nat -> nat -> vehicle.

Check vehicle_rec.

Definition nb_seats  : vehicle -> nat :=
 vehicle_rec (fun v => nat) 
              (fun nseats => nseats)
              (fun nbseats nbwheels => nbseats).


Eval compute in (nb_seats (bicycle 1)).

(* the bus I take to go to work and write this book *)
Eval compute in (nb_seats (motorized 50 4)).

