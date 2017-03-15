(*
 *  Seplog is an implementation of separation logic (an extension of Hoare
 *  logic by John C. Reynolds, Peter W. O'Hearn, and colleagues) in the
 *  Coq proof assistant (version 8, http://coq.inria.fr) together with a
 *  sample verification of the heap manager of the Topsy operating system
 *  (version 2, http://www.topsy.net). More information is available at
 *  http://staff.aist.go.jp/reynald.affeldt/seplog.
 *
 *  Copyright (c) 2005, 2006, 2007 Reynald Affeldt and Nicolas Marti
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

Load seplog_header.

Require Import frag_list_entail.
Require Import frag_list_triple.
Require Import frag_list_vcg.

(* A simple one: swap *)

Definition i : var.v := 1.
Definition j : var.v := 2.
Definition x : var.v := 4.
Definition y : var.v := 3.
Definition vx : var.v := 5.
Definition vy : var.v := 6.

Definition swap (x y:var.v) : cmd :=
    i <-* var_e x;
    j <-* var_e y;
    var_e x *<- var_e j;
    var_e y *<- var_e i.

Definition swap_precond (x y:var.v) (vx vy : nat) : assrt := 
  (true_b, star (singl (var_e x) (var_e vx)) (singl (var_e y) (var_e vy))).

Definition swap_postcond (x y:var.v) (vx vy : nat) : assrt := 
  (true_b, star (singl (var_e x) (var_e vy)) (singl (var_e y) (var_e vx))).

Lemma tmp : forall (P Q:assert), P ==> Q ->
  P ==> (fun s h => Q s h \/ False).
red; intros.
red in H.
auto.
Qed.

Lemma swap_verif: 
    {{ assrt_interp (swap_precond x y vx vy) }}
    swap x y
    {{ Assrt_interp ((swap_postcond x y vx vy)::nil) }}.
intros.
unfold swap_precond.
unfold swap_postcond.
eapply tritra_use.
simpl; intuition.
unfold x; unfold y; unfold i; unfold j; unfold vx; unfold vy.

(* step-by-step proof *)

(*Rotate_tritra_sig_lhs.
eapply tritra_lookup.
intros.
Omega_exprb.

Rotate_tritra_sig_lhs.
eapply tritra_subst_lookup'.
intros.
Omega_exprb.
simpl; intuition.

eapply tritra_subst_mutation.
simpl.
Rotate_tritra_sig_lhs.
eapply tritra_mutation.
Omega_exprb.

eapply tritra_subst_mutation.
simpl.
Rotate_tritra_sig_lhs.
eapply tritra_mutation.
Omega_exprb.

eapply tritra_subst_elt.
simpl.
eapply tritra_entail.
unfold Assrt_interp.

apply tmp.
eapply entail_soundness.
Entail.*)

Tritra.
(*Show Proof.*)
Qed.

Lemma swap_verif': 
    {{ Assrt_interp ((swap_precond x y vx vy)::nil) }}
    swap x y
    {{ Assrt_interp ((swap_postcond x y vx vy)::nil) }}.
intros.
unfold swap_precond.
unfold swap_postcond.
unfold swap.
unfold x; unfold y; unfold i; unfold j; unfold vx; unfold vy.

Open Local Scope frag2_scope.

match goal with
|- {{ _ }} ?C {{ _ }} =>
  replace C with (proj_cmd
    (seq' (1 <-* var_e 4)
      (seq' (2 <-* var_e 3)
        (seq' ((var_e 4) *<- (var_e 2))
          ((var_e 3) *<- (var_e 1))))))
end.

Close Local Scope frag2_scope.

eapply bigtoe_fct_correct.
compute.
reflexivity.
reflexivity.
(*Show Proof*)
Qed.

(* an initialization of a field for an array of structure *)

Definition ptr : var.v := 1.
Definition startl : var.v := 2.
Definition size: var.v := 3.
Definition idx: var.v := 4.
Definition init_val: var.v := 5.

Fixpoint init_body (n: nat) {struct n} : cmd := 
  match n with
    0 => skip
    | S n' => 
      ((var_e ptr) +e (var_e idx)) *<- var_e init_val;
       ptr <- (var_e ptr) +e (var_e size);
       init_body n'
   end.

Definition init (n: nat) : cmd :=
    ptr <- var_e startl;
    init_body n.

Fixpoint init_precond_sigma (n: nat) {struct n} : Sigma :=
  match n with 
    0 => emp
    | S n' => star 
        (cell (((var_e startl) +e (var_e idx)) +e ((var_e size) *e (int_e (Z_of_nat n'))) )) 
	(init_precond_sigma n')
end. 

Definition init_precond (n: nat) : assrt :=
  (var_e startl >> int_e 0%Z, init_precond_sigma n).

Fixpoint init_postcond_sigma (n: nat) {struct n}: Sigma :=
  match n with 
    0 => emp
    | S n' => star 
	(singl (((var_e startl) +e (var_e idx)) +e ((var_e size) *e (int_e (Z_of_nat n'))) ) (var_e init_val)) 
	(init_postcond_sigma n')
end. 

Definition init_postcond (n: nat) : assrt :=
  (var_e startl >> int_e 0%Z, init_postcond_sigma n).

Lemma init_verif: forall n,
    n = 6 -> 
    {{ assrt_interp (init_precond n) }}
    (init n)
    {{ Assrt_interp (init_postcond n::nil) }}.

intros; subst n. 
unfold init; simpl init_body.
unfold init_precond; simpl init_precond_sigma.
unfold init_postcond; simpl init_postcond_sigma.
unfold ptr; unfold startl; unfold size; unfold idx; unfold init_val.

eapply tritra_use.
simpl; intuition.

Tritra.
(*Show Proof.*)
Qed.

Lemma init_verif': forall n,
    n = 2 -> 
    {{ Assrt_interp (init_precond n :: nil) }}
    (init n)
    {{ Assrt_interp (init_postcond n :: nil) }}.

intros; subst n. 
unfold init; simpl init_body.
unfold init_precond; simpl init_precond_sigma.
unfold init_postcond; simpl init_postcond_sigma.
unfold ptr; unfold startl; unfold size; unfold idx; unfold init_val.

Open Local Scope frag2_scope.

match goal with
|- {{ _ }} ?C {{ _ }} =>
replace C with (proj_cmd
(1 <- var_e 2;
   var_e 1 +e var_e 4 *<- var_e 5;
   1 <- var_e 1 +e var_e 3; 
   var_e 1 +e var_e 4 *<- var_e 5;
   1 <- var_e 1 +e var_e 3; skip')
)
end.

Close Local Scope frag2_scope.

eapply bigtoe_fct_correct.
(*2: auto.
auto.
Show Proof.
Qed.*)
Admitted. (* too slow *)

Goal 
  {{ assrt_interp (true_b, emp) }}
  ifte (var_e 1 >>= var_e 2) thendo
    ifte (var_e 1 >>= var_e 3) thendo
      (0 <- var_e 1)
    elsedo
      (0 <- var_e 3)
  elsedo
    ifte (var_e 2 >>= var_e 3) thendo
      (0 <- var_e 2)
    elsedo
      (0 <- var_e 3)
  {{ Assrt_interp ((true_b,emp)::nil) }}.

eapply tritra_use.
simpl; intuition.

Tritra.
(*Show Proof.*)
Qed.

Goal
  {{ Assrt_interp ((true_b, emp)::nil) }}
  ifte (var_e 1 >>= var_e 2) thendo
    ifte (var_e 1 >>= var_e 3) thendo
      (0 <- var_e 1)
    elsedo
      (0 <- var_e 3)
  elsedo
    ifte (var_e 2 >>= var_e 3) thendo
      (0 <- var_e 2)
    elsedo
      (0 <- var_e 3)
  {{ Assrt_interp (((var_e 0 == var_e 1) ||| (var_e 0 == var_e 2) ||| (var_e 0 == var_e 3), emp)::nil) }}.

Open Local Scope frag2_scope.

match goal with
|- {{ _ }} ?C {{ _ }} =>
replace C with
(proj_cmd (ifte' (var_e 1 >>= var_e 2)
     (ifte' (var_e 1 >>= var_e 3) (0 <- var_e 1) (0 <- var_e 3))
     (ifte' (var_e 2 >>= var_e 3) (0 <- var_e 2) (0 <- var_e 3))))
end.

Close Local Scope frag2_scope.

eapply bigtoe_fct_correct.
compute; auto.
auto.
(*Show Proof.*)
Qed.

Goal
  {{ assrt_interp (true_b, emp) }}
  ifte (var_e 1 >>= var_e 2) thendo
    ifte (var_e 1 >>= var_e 3) thendo
      (0 <- var_e 1)
    elsedo
      (0 <- var_e 3)
  elsedo
    ifte (var_e 2 >>= var_e 3) thendo
      (0 <- var_e 2)
    elsedo
      (0 <- var_e 3)
  {{ Assrt_interp (((var_e 0 == var_e 1) ||| (var_e 0 == var_e 2) ||| (var_e 0 == var_e 3), emp)::nil) }}.

eapply tritra_use.
simpl; intuition.

Tritra.

(*Show Proof.*)
Qed.

Inductive tritra_Step : list (Pi * Sigma * wpAssrt) -> Prop :=
  finish: tritra_Step nil
  | step: forall l l' p s L,
    tritra_step p s L = Some l' ->
    tritra_Step (l' ++ l) ->
    tritra_Step ((p,s,L)::l).

(*
Lemma tritra_Step_app: forall l,  
  tritra_Step l ->
  forall l1 l2,
    l = l1 ++ l2 ->
    tritra_Step l1 /\ tritra_Step l2.
  do 2 intro.
  induction H.
  simpl; intros.
  destruct l1; destruct l2; simpl in H; try discriminate.
  split; apply finish.
  intros.
  generalize (tritra_step_correct p s L l'); intros.
  destruct (tritra_step p s L); try discriminate.
  generalize (H2 H); clear H H2; intros.
  
  

Fixpoint tritra_Step_semantics (l: (list (Pi * Sigma * wpAssrt))) : Prop :=
  match l with
    | nil => True
    | (pi,sig,L)::tl =>
      ((assrt_interp (pi,sig)) ==> (wpAssrt_interp L)) /\ (tritra_Step_semantics tl)
  end.

Lemma tritra_Step_sound: forall l,
  tritra_Step l -> tritra_Step_semantics l.
  intros.
  induction H.
  simpl; auto.
  simpl.
  
*)  

(*
Ltac Resolve_tritra_Step :=
  ((eapply finish)||(eapply step; [compute; auto | simpl; Resolve_tritra_Step])).


Goal 
  tritra_Step ((true_b, epsi, (L_if (var_e 1 >>= var_e 2)
          (L_if (var_e 1 >>= var_e 3)
             (L_subst ((0, var_e 1) :: nil)
                (L_elt
                   (((var_e 0 == var_e 1) ||| (var_e 0 == var_e 2))
                    ||| (var_e 0 == var_e 3), epsi)))
             (L_subst ((0, var_e 3) :: nil)
                (L_elt
                   (((var_e 0 == var_e 1) ||| (var_e 0 == var_e 2))
                    ||| (var_e 0 == var_e 3), epsi))))
          (L_if (var_e 2 >>= var_e 3)
             (L_subst ((0, var_e 2) :: nil)
                (L_elt
                   (((var_e 0 == var_e 1) ||| (var_e 0 == var_e 2))
                    ||| (var_e 0 == var_e 3), epsi)))
             (L_subst ((0, var_e 3) :: nil)
                (L_elt
                   (((var_e 0 == var_e 1) ||| (var_e 0 == var_e 2))
                    ||| (var_e 0 == var_e 3), epsi))))))::nil).

Resolve_tritra_Step.

(*
eapply step.
compute.
intuition.
simpl.

eapply step.
compute.
intuition.
simpl.

eapply step.
compute.
intuition.
simpl.

eapply step.
compute.
intuition.
simpl.

eapply step.
compute.
intuition.
simpl.

eapply step.
compute.
intuition.
simpl.

eapply step.
compute.
intuition.
simpl.

eapply step.
compute.
intuition.
simpl.

eapply step.
compute.
intuition.
simpl.

eapply step.
compute.
intuition.
simpl.

eapply step.
compute.
intuition.
simpl.

apply finish.
*)
Show Proof.

Qed.    

Goal
  [[(true_b, epsi)]]
  ifte ((var_e 1) >>= (var_e 2)) thendo
    ifte ((var_e 1) >>= (var_e 3)) thendo
      (0 <- (var_e 1))
    elsedo
      (0 <- (var_e 3))
  elsedo
    ifte ((var_e 2) >>= (var_e 3)) thendo
      (0 <- (var_e 2))
    elsedo
      (0 <- (var_e 3))
  [[(((var_e 0) == (var_e 1)) ||| ((var_e 0) == (var_e 2)) ||| ((var_e 0) == (var_e 3)),epsi)]].

eapply frag_hoare_correct.

compute.
auto.
Show Proof.
Qed.
*)
