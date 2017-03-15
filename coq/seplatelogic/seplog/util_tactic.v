(*
 *  Seplog is an implementation of separation logic (an extension of Hoare
 *  logic by John C. Reynolds, Peter W. O'Hearn, and colleagues) in the
 *  Coq proof assistant (version 8, http://coq.inria.fr) together with a
 *  sample verification of the heap manager of the Topsy operating system
 *  (version 2, http://www.topsy.net). More information is available at
 *  http://web.yl.is.s.u-tokyo.ac.jp/~affeldt/seplog.
 *
 *  Copyright (c) 2005, 2006 Reynald Affeldt and Nicolas Marti
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *)

Require Import List.
Require Import ZArith.
Require Import List.
Require Import EqNat.
Require Import Classical.

Require Import util.

(*
 * tactics for applying presburger 
 *)

Lemma Z0_mech: Z0 = Z_of_nat 0.
intuition.
Qed.


Ltac mult_dist :=
  (rewrite mult_plus_distr_l; (mult_dist || idtac)) || 
    (rewrite mult_plus_distr_r; (mult_dist || idtac)) || 
      (rewrite mult_minus_distr_r; [(mult_dist || idtac) | OmegaZ]) || 
        (rewrite mult_minus_distr_l; [(mult_dist || idtac) | OmegaZ]) || idtac
with 
 Z_to_nat x:= 
 assert (Z_to_natA1: Zpos x = Z_of_nat (nat_of_P x)); [auto | rewrite Z_to_natA1; clear Z_to_natA1; unfold nat_of_P; simpl (Pmult_nat x 1);idtac ]
with 
 Supr_Z t := match t with 
               | Z0 =>rewrite Z0_mech
               | Zpos ?x =>Z_to_nat x
               | Zplus ?x1 ?x2 => (((Supr_Z x1 || idtac); (Supr_Z x2 || idtac); rewrite <- inj_plus) || idtac)
               | Zminus ?x1 ?x2 => (((Supr_Z x1 || idtac); (Supr_Z x2 || idtac); rewrite <- inj_minus1; [idtac | omega]) || idtac)
               | Zmult ?x1 ?x2 => (((Supr_Z x1 || idtac); (Supr_Z x2 || idtac); rewrite <- inj_mult) || idtac)
	       | Z_of_nat ?x => idtac
               | ?E => (assert (Supr_Z'A1: (E >= 0)%Z); [omega | generalize (nat_of_Z _ Supr_Z'A1); clear Supr_Z'A1; intro X; let x := fresh in (let y := fresh in (destruct X as [x y]; rewrite y))] || idtac)
	       | _ => idtac
             end
with
 Supr_Z_eq_left :=
             match goal with
                | |- (?x1 = ?x2)%Z => Supr_Z x1
                | |- (?x1 <= ?x2)%Z => Supr_Z x1
                | |- (?x1 >= ?x2)%Z => Supr_Z x1
                | |- (?x1 > ?x2)%Z => Supr_Z x1
                | |- (?x1 < ?x2)%Z => Supr_Z x1
		| |- _ => idtac
             end
with
 Supr_Z_eq_right :=
             match goal with
                | |- (?x1 = ?x2)%Z => Supr_Z x2
                | |- (?x1 <= ?x2)%Z => Supr_Z x2
                | |- (?x1 >= ?x2)%Z => Supr_Z x2
                | |- (?x1 > ?x2)%Z => Supr_Z x2
                | |- (?x1 < ?x2)%Z => Supr_Z x2
		| |- _ => idtac
             end
with
 Supr_Z_eq :=
             match goal with
	        | |- ((Z_of_nat ?x1) = (Z_of_nat ?x2))%Z =>  apply Z_of_nat_inj'
	        | |- ((Z_of_nat ?x1) <= (Z_of_nat ?x2))%Z =>  apply Z_of_nat_le_inj'
	        | |- ((Z_of_nat ?x1) < (Z_of_nat ?x2))%Z =>  apply Z_of_nat_lt_inj'
	        | |- ((Z_of_nat ?x1) >= (Z_of_nat ?x2))%Z =>  apply Z_of_nat_ge_inj'
	        | |- ((Z_of_nat ?x1) < (Z_of_nat ?x2))%Z =>  apply Z_of_nat_gt_inj'
		| |- _ => idtac
             end
with
 Z_to_nat_Hyp x id:= assert (Z_to_natA1: Zpos x = Z_of_nat (nat_of_P x)); [auto | rewrite Z_to_natA1 in id; clear Z_to_natA1; unfold nat_of_P in id; simpl (Pmult_nat x 1) in id;idtac ]
with
 Supr_Z_Hyp t id:= 
            match t with 
               | Z0 =>rewrite Z0_mech  in id
               | Zpos ?x =>Z_to_nat_Hyp x id
               | Zplus ?x1 ?x2 => (Supr_Z_Hyp x1 id || idtac) ; (Supr_Z_Hyp x2 id || idtac); rewrite <- inj_plus in id
               | Zminus ?x1 ?x2 => (Supr_Z_Hyp x1 id || idtac) ; (Supr_Z_Hyp x2 id || idtac); rewrite <- inj_minus1 in id; [idtac | omega]
               | Zmult ?x1 ?x2 => (Supr_Z_Hyp x1 id || idtac) ; (Supr_Z_Hyp x2 id || idtac); rewrite <- inj_mult in id
	       | Z_of_nat ?x => idtac
               | ?E => (assert (Supr_Z'A1: (E >= 0)%Z); [omega | generalize (nat_of_Z _ Supr_Z'A1); clear Supr_Z'A1; intro X; let x := fresh in (let y := fresh in (destruct X as [x y]; rewrite y in id))] || idtac)
	       | _ => idtac
             end

with
 Supr_Z_eq_hyp_left :=
             match goal with
                | id: (?x1 = ?x2)%Z |- _ => Supr_Z_Hyp x1 id
                | id: (?x1 <= ?x2)%Z |- _ => Supr_Z_Hyp x1 id
                | id: (?x1 >= ?x2)%Z |- _ => Supr_Z_Hyp x1 id
                | id: (?x1 > ?x2)%Z |- _ => Supr_Z_Hyp x1 id
                | id: (?x1 < ?x2)%Z |- _ => Supr_Z_Hyp x1 id
		| |- _ => idtac
             end
with
 Supr_Z_eq_hyp_right :=
             match goal with
                | id: (?x1 = ?x2)%Z |- _ => Supr_Z_Hyp x2 id
                | id: (?x1 <= ?x2)%Z |- _ => Supr_Z_Hyp x2 id
                | id: (?x1 >= ?x2)%Z |- _ => Supr_Z_Hyp x2 id
                | id: (?x1 > ?x2)%Z |- _ => Supr_Z_Hyp x2 id
                | id: (?x1 < ?x2)%Z |- _ => Supr_Z_Hyp x2 id
		| |- _ => idtac
             end
with Supr_Z_eq_Hyp := 
             match goal with
                | id: (?x1 = ?x2)%Z |- _ => generalize (Z_of_nat_inj _ _ id); intros
                | id: (?x1 > ?x2)%Z |- _ => generalize (Z_of_nat_gt_inj _ _ id); intros
                | id: (?x1 < ?x2)%Z |- _ => generalize (Z_of_nat_lt_inj _ _ id); intros
                | id: (?x1 >= ?x2)%Z |- _ => generalize (Z_of_nat_ge_inj _ _ id); intros
                | id: (?x1 <= ?x2)%Z |- _ => generalize (Z_of_nat_le_inj _ _ id); intros
                | |- _ => idtac
             end
           

(* OmegaZ : extension of omega to handle goals/hypos that contains Z_of_nat *)
with
 OmegaZ := ((Supr_Z_eq_hyp_left; Supr_Z_eq_hyp_right; Supr_Z_eq_Hyp); (Supr_Z_eq_left; Supr_Z_eq_right; Supr_Z_eq) || idtac); mult_dist; (omega || tauto).

(*
Lemma test: forall x y,
            ((Z_of_nat x) + 4%Z - 2%Z > (Z_of_nat (y +4)))%Z ->
            ((Z_of_nat (x+ 2)) + 2%Z >= (Z_of_nat y) + 6%Z)%Z.
intros.

OmegaZ.


Qed.
*)
