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
 *  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *)

Load seplog_header.

Require Import Bool.

(************************************************)
(*      tactics to make proof more readable     *)
(************************************************)

Ltac Step R :=
  match goal with
    | id: {{?P'}} ?c {{?Q'}} |- {{?P}} ?c {{?Q}} => eapply apply_triple; [apply id | idtac | idtac]
    | id: {{?P'}} ?c {{?Q'}} |- {{?P}} ?c; ?c' {{?Q}} => eapply apply_triple'; [apply id | idtac | idtac]
    | |- {{?P}} ?x <- ?e {{?Q}} => eapply semax_assign'; red
    | |- {{?P}} ?x <- ?e ; ?c {{?Q}} => eapply semax_assign'' with R; [red; intros | idtac]
    | |- {{?P}} ?x <-* ?e {{?Q}} => eapply semax_lookup_backwards'
    | |- {{?P}} ?x <-* ?e ; ?c {{?Q}} =>  eapply semax_lookup_backwards'' with R; [red; intros | idtac]
    | |- {{?P}} ?e1 *<- ?e2 {{?Q}} => eapply semax_mutation_backwards'
    | |- {{?P}} ?e1 *<- ?e2 ; ?c {{?Q}} => eapply semax_mutation_backwards'' with R; [red; intros | idtac]
    | |- {{?P}} while ?b ?c1 {{?Q}} => eapply semax_while' with R
    | |- {{?P}} while ?b ?c1 ; ?c2 {{?Q}} => eapply semax_while'' with R; [red; intros | idtac | idtac]
    | |- {{?P}} skip {{?Q}} =>  eapply semax_skip'
    | |- {{?P}} ifte ?b thendo ?c1 elsedo ?c2 {{?Q}} =>  eapply semax_ifte
    | |- {{?P}} (ifte ?b thendo ?c1 elsedo ?c2); ?c' {{?Q}} => apply semax_seq with R; [eapply semax_ifte; [idtac| idtac] | idtac]
    | |- {{?P}} ?c1; ?c2 {{?Q}} => apply semax_seq with R; [idtac| idtac]
  end.

Notation " s '|b=' b " := (eval_b b s = true) (right associativity, at level 80).

Notation " s '|b/=' b " := (eval_b b s = false) (right associativity, at level 80).

Ltac Decompose_hyp := 
  match goal with
    | id: ?P1 /\ ?P2 |- _ => (decompose [and] id; clear id); Decompose_hyp
    | id: (?P1 ** ?P2) ?s ?h |- _ =>
       (let x:=fresh in (
           inversion_clear id as [x X];
           let y:= fresh in (
              inversion_clear X as [y Y];
              decompose [and] Y; clear Y
           )
        )); Decompose_hyp
    | id: ex ?P |- _ => (inversion_clear id); Decompose_hyp
    | _ => idtac
  end.

Ltac Rewrite_heap h :=
  (match goal with 
    | id: h = (?h1 +++ ?h2) |- _ => rewrite id; (Rewrite_heap h1); (Rewrite_heap h2)
    | _ => idtac
   end) .

Ltac Resolve_assert1 :=
  match goal with 
    | |- (?P1 ** ?P2) ?s ?h  => Rewrite_heap h; repeat rewrite sep.con_assoc_equiv
    | |- (?P1 -* ?P2) ?s ?h => red; intro; intro X; inversion_clear X; intros
    | _ => idtac
  end.

(***************************************************************)
(*                 Some lemmas and definition                  *)
(***************************************************************)

(******************)
(*   rewriting    *)
(******************)

Lemma expr_store_update_rewrite: forall e x p s,
  eval (expr_rewrite e (var_e x) (int_e p)) s = eval e (store.update  x p s).
induction e; simpl; intros; auto.

generalize (beq_nat_classic v x); intro X; inversion_clear X.
rewrite H.
generalize (beq_nat_true _ _ H); intro; subst v.
rewrite store.lookup_update'.
auto.
rewrite H.
generalize (beq_nat_false _ _ H); intro.
rewrite <- (store.lookup_update); auto.
rewrite IHe1; rewrite IHe2; auto.
rewrite IHe1; rewrite IHe2; auto.
rewrite IHe1; rewrite IHe2; auto.
rewrite IHe1; rewrite IHe2; auto.
rewrite IHe1; rewrite IHe2; auto.
Qed.

Lemma expr_b_store_update_rewrite: forall b x p s,
  eval_b (expr_b_rewrite b (var_e x) (int_e p)) s = eval_b b (store.update  x p s).
induction b; simpl; intros; auto.
repeat rewrite expr_store_update_rewrite; auto.
repeat rewrite expr_store_update_rewrite; auto.
repeat rewrite expr_store_update_rewrite; auto.
repeat rewrite expr_store_update_rewrite; auto.
rewrite IHb; auto.
rewrite IHb1; rewrite IHb2; auto.
rewrite IHb1; rewrite IHb2; auto.
Qed.

Lemma mapsto_store_update_rewrite: forall e1 e2 x p s h,
  ((expr_rewrite e1 (var_e x) (int_e p)) |-> (expr_rewrite e2 (var_e x) (int_e p))) s h ->
  (e1 |-> e2) (store.update x p s) h.
intros.
red in H; red.
inversion_clear H.
inversion_clear H0.
exists x0.
split.
rewrite <- expr_store_update_rewrite.
auto.
rewrite <- expr_store_update_rewrite.
auto.
Qed.

(******************)
(*    bool_eq     *)
(******************)

Definition bool_eq (a b: bool) :=
  match (a,b) with
     | (true, true) => true
     | (false, false) => true
     | _ => false
  end.

Lemma bool_eq_classic: forall a b,
  bool_eq a b = true \/ bool_eq a b = false.
intros.
destruct bool_eq; auto.
Qed.

Lemma bool_eq_true: forall a b,
  bool_eq a b = true -> a = b.
destruct a; destruct b; (tauto || auto).
Qed.

Lemma bool_eq_false: forall a b,
  bool_eq a b = false -> a <> b.
destruct a; destruct b; intuition.
Qed.

Lemma bool_eq_dif: forall a b,
  a <> b -> bool_eq a b = false.
destruct a; destruct b; intuition.
Qed.

Lemma bool_eq_refl: forall a,
  bool_eq a a = true.
destruct a; auto.
Qed.

(**************************)
(*   heap list related    *)
(**************************)

Fixpoint get_endl (l:list (nat * bool)) (startl: nat) {struct l} : nat :=
   match l with
     nil => startl
     | (b,c)::tl => get_endl tl (startl + 2 + b)
   end.

Lemma get_endl_app: forall a b startl,
  get_endl (a++b) startl = get_endl b (get_endl a startl).
induction a; auto.
destruct a.
simpl.
intuition.
Qed.

Lemma get_endl_gt: forall l startl,
  startl <= get_endl l startl.
induction l.
trivial.
destruct a.
simpl; intros.
generalize (IHl (startl + 2 + n)); intros.
omega.
Qed.

Fixpoint In_hl (l:list (nat*bool)) (block:nat*nat*bool) (startp: nat) {struct l}: Prop :=
  match l with
    nil => False
    | (size , stat)::tl => match block with
                             (adr,sz,st) =>
                                if (andb (andb (beq_nat startp adr) (bool_eq st stat)) (beq_nat size sz)) then
                                    True
                                else
                                    In_hl tl block (get_endl ((size,stat)::nil) startp)
                           end
  end.

Lemma In_hl_app_or: forall l1 l2 a b c startp,
  In_hl (l1 ++ l2) (a,b,c) startp -> 
  (In_hl l1 (a,b,c) startp \/ In_hl l2 (a,b,c) (get_endl l1 startp)).
induction l1; auto.
destruct a.
simpl.
intros.
destruct (beq_nat startp a && bool_eq c b && beq_nat n b0).
intuition.
intuition.
Qed.

Lemma In_hl_or_app: forall l1 l2 a b c startp,
  (In_hl l1 (a,b,c) startp \/ In_hl l2 (a,b,c) (get_endl l1 startp)) ->
  In_hl (l1 ++ l2) (a,b,c) startp.
induction l1.
simpl; tauto.
destruct a; simpl; intros.
destruct (beq_nat startp a && bool_eq c b && beq_nat n b0).
trivial.
auto.
Qed.

Open Local Scope Z_scope.

Definition HM_FREEFAILED := int_e 0.
Definition HM_FREEOK := int_e 1.

Definition Allocated := int_e 0.
Definition Free := int_e 1.

Definition alloc := false.
Definition free := true.

Definition status := 0.
Definition next := 1.

Close Local Scope Z_scope.

Definition hmStart := 0.
Definition hmEnd := 1.
Definition entry := 3.
Definition cptr := 4.
Definition nptr := 5.
Definition result := 6.
Definition fnd := 7.
Definition stts := 8.
Definition sz := 9.

Hint Unfold fnd.
Hint Unfold stts.
Hint Unfold sz.
Hint Unfold entry.
Hint Unfold cptr.
Hint Unfold nptr.
Hint Unfold result.
Hint Unfold HM_FREEFAILED.
Hint Unfold HM_FREEOK.
Hint Unfold Allocated.
Hint Unfold Free.
Hint Unfold status.
Hint Unfold next.
Hint Unfold hmStart.
Hint Unfold hmEnd.

(**************************)
(*        heap list       *)
(**************************)

Inductive hl : loc -> list (nat * bool) -> assert :=

  | hl_last: forall s p h,  
    sep.emp s h ->
    hl p nil s h

  | hl_Free: forall s h next p h1 h2 size flag tl,
    h1 # h2 -> h = h1 +++ h2 ->
    flag = true ->
    next = p + 2 + size ->
    (nat_e p |--> Free::nat_e next::nil ** Array (p+2) size) s h1 ->
    hl next tl s h2 ->
    hl p ((size,flag)::tl) s h

  | hl_Allocated: forall s h next p h1 h2 size flag tl,
    h1 # h2 -> h = h1 +++ h2 ->
    flag = false ->
    next = p + 2 + size ->
    (nat_e p |--> Allocated::nat_e next::nil) s h1 ->
    hl next tl s h2 ->
    hl p ((size,flag)::tl) s h.

Definition hlstat_bool2expr (b: bool) : expr := 
   match b with
      true => Free
      | false => Allocated
   end.

Definition Heap_List (l:list (nat * bool)) (p:nat) : assert :=
  (hl p l) ** (nat_e (get_endl l p) |--> Allocated::null::nil).

Lemma Heap_List_inde_store: forall l startl s h,
  Heap_List startl l s h -> forall s', Heap_List startl l s' h.
  intros.
  Decompose_sepcon H h1 h2.
  Compose_sepcon h1 h2; auto.
  clear H H1 H3 h2.
  induction H0.
  eapply hl_last.
  intuition.
  
  subst next0 flag.
  eapply hl_Free with (h1 := h1) (h2 := h2); auto.
  Decompose_sepcon H3 h11 h12.
  Compose_sepcon h11 h12; auto.
  eapply Array_inde_store.
  apply H6.
  
  subst next0 flag.
  eapply hl_Allocated with (h1 := h1) (h2 := h2); auto.
Qed.

Ltac Heap_List_equiv := 
  match goal with
    | id: Heap_List ?l ?start1 ?s1 ?h |-  Heap_List ?l ?start2 ?s2 ?h =>
      assert (Heap_List_equivA1: start2 = start1); [omega |
        ((rewrite Heap_List_equivA1) || idtac); 
        eapply (Heap_List_inde_store); apply id
      ]
  end.

Lemma hl_app : forall a b startl s h,
     (hl startl (a ++ b) s h)
     <-> 
     ((hl startl a ** hl (get_endl a startl) b) s h).
induction a.
simpl.
split; simpl; intros.
Compose_sepcon heap.emp h; auto.
eapply hl_last.
red; auto.
Decompose_sepcon H h1 h2.
inversion_clear H0.
assert (h = h2).
Heap_emp_clean; Equal_heap.
rewrite H0; auto.

destruct a.
split; simpl; intros.
inversion_clear H.

subst b next0.
generalize (IHa b0 (startl + 2 + n) s h2); intro X; inversion_clear X.
generalize (H H5); clear H5 H2 H; intros.
Decompose_sepcon H h21 h22.
Compose_sepcon (h1 +++ h21) h22; auto.
eapply hl_Free with (h1 := h1) (h2 := h21); [Heap_emp_clean; Disjoint_heap | Heap_emp_clean; Equal_heap | auto | intuition | auto | auto].

subst b next0.
generalize (IHa b0 (startl + 2 + n) s h2); intro X; inversion_clear X.
generalize (H H5); clear H5 H2 H; intros.
Decompose_sepcon H h21 h22.
Compose_sepcon (h1 +++ h21) h22; auto.
eapply hl_Allocated with (h1 := h1) (h2 := h21); [Heap_emp_clean; Disjoint_heap | Heap_emp_clean; Equal_heap | auto | intuition | auto | auto].

Decompose_sepcon H h1 h2.
inversion_clear H0.

subst b next0.
eapply hl_Free with (h1 := h3) (h2 := (h2 +++ h4)); [Heap_emp_clean; Disjoint_heap | Heap_emp_clean; Equal_heap | auto | intuition | auto | auto].
generalize (IHa b0 (startl + 2 + n) s (h2 +++ h4)); intro X; inversion_clear X.
apply H5; clear H5 H0.
Compose_sepcon h4 h2; auto.

subst b next0.
eapply hl_Allocated with (h1 := h3) (h2 := (h2 +++ h4)); [Disjoint_heap | Equal_heap | auto | intuition | auto | auto].
generalize (IHa b0 (startl + 2 + n) s (h2 +++ h4)); intro X; inversion_clear X.
apply H5; clear H5 H0.
Compose_sepcon h4 h2; auto.
Qed.

Lemma hl_compaction: forall l1 l2 size size' p s h,
  Heap_List (l1++(size,free)::(size',free)::nil++l2) p s h ->
  exists y, (nat_e (get_endl l1 p + 1) |-> y **
    (nat_e (get_endl l1 p + 1) |-> nat_e (get_endl l1 p + size + size' + 4) -*
      Heap_List (l1 ++ (size+size'+2,free)::nil ++ l2) p)) s h.
intros.
Decompose_sepcon H h1 h2.
generalize (hl_app l1 ((size, true) :: (size', true) :: l2) p s h1); intro X; inversion_clear X.
generalize (H2 H0); clear H2 H4 H0; intro.
Decompose_sepcon H0 h11 h12.
inversion_clear H6; try discriminate.
inversion_clear H11; try discriminate.
subst next0 next1.
clear H8 H13.
exists (nat_e (get_endl l1 p + 2 + size)).
Decompose_sepcon H10 h31 h32.
simpl in H9.
Decompose_sepcon H9 h311 h312.
Decompose_sepcon H18 h3121 h3122.
Compose_sepcon h3121 (h311 +++ h32 +++ h4 +++ h11 +++ h2).
Mapsto.
Intro_sepimp h3121' h'.
Compose_sepcon (h3121' +++ h311 +++ h32 +++ h4 +++ h11) h2.
generalize (hl_app l1 ((size + size' + 2, true) :: l2) p s (h3121' +++ h311 +++ h32 +++ h4 +++ h11)); intro X; inversion_clear X.
apply H25.
clear H25 H24.
Compose_sepcon h11 (h3121' +++ h311 +++ h32 +++ h4); auto.
eapply (hl_Free) with (h1 := h3121' +++ h311 +++ h32 +++ h5) (h2 := h6).
Disjoint_heap.
Heap_emp_clean; Equal_heap.
auto.
intuition.
Compose_sepcon (h3121' +++ h311) (h32 +++ h5).
simpl.
Compose_sepcon h311 h3121'.
Mapsto.
Compose_sepcon h3121' heap.emp.
Mapsto.
red; auto.
Decompose_sepcon H15 h51 h52.
TArray_concat_split_r size (2 + size').
Compose_sepcon h32 h5.
auto.
TArray_concat_split_r 2 size'.
Compose_sepcon h51 h52.
eapply mapstos_to_array.
apply H24.
OmegaZ.
auto.
auto.
cutrewrite (get_endl l1 p + 2 + (size + size' + 2) = get_endl l1 p + 2 + size + 2 + size'); [auto | omega].
rewrite get_endl_app in H3.
simpl get_endl in H3.
rewrite get_endl_app.
simpl get_endl.
cutrewrite ((get_endl l2 (get_endl l1 p + 2 + (size + size' + 2)) = (get_endl l2 (get_endl l1 p + 2 + size + 2 + size')))).
auto.
intuition.
Qed.

Lemma compaction_example: forall p,
 {{ Heap_List ((8,free)::(10,free)::nil) p }}
 nat_e p +e int_e 1%Z *<- nat_e (p + 22)
 {{ Heap_List ((20,free)::nil) p }}.
  intro.
  apply semax_mutation_backwards'.
  red; intros.
  generalize (hl_compaction nil _ _ _ _ _ _ H); intro.
  inversion_clear H0 as [x]; exists x.
  simpl in H1.
  Monotony H1.
  Monotony H0.
  auto.
Qed.

Lemma hl_splitting: forall l1 l2 a b startp s h,
   Heap_List (l1 ++ (a + 2 + b,true)::l2) startp s h ->
   (exists y, ((nat_e (get_endl l1 startp + a + 3) |-> y) **
     ((nat_e (get_endl l1 startp + a + 3) |-> (nat_e (get_endl l1 startp + a + b + 4))) -*
        (fun s h => exists y, ((nat_e (get_endl l1 startp + a + 2) |-> y) **
          ((nat_e (get_endl l1 startp + a + 2) |-> Free) -*
             (fun s h => exists y, ((nat_e (get_endl l1 startp + 1) |-> y) **
                 ((nat_e (get_endl l1 startp + 1) |-> (nat_e (get_endl l1 startp + a + 2))) -*
                    Heap_List (l1 ++ (a,true)::(b,true)::l2) startp
                 )) s h  
             ) 
          )) s h    
        ) 
     )) s h    
   ) .

intros.
Decompose_sepcon H h1 h2.
generalize (hl_app l1 ((a+2+b,true)::l2) startp s h1); intro X; inversion_clear X.
generalize (H2 H0); clear H0 H2 H4; intro.
Decompose_sepcon H0 h11 h12.
inversion_clear H6; try discriminate.
Decompose_sepcon H10 h31 h32.
TArray_concat_split_l_l a H14.
Decompose_sepcon H13 h321 h322.
TArray_concat_split_l_l 2 H18.
Decompose_sepcon H17 h3221 h3222.
simpl in H19.
Decompose_sepcon H19 h32211 h32212.
Decompose_sepcon H25 h322121 h322122.
inversion_clear H25.
inversion_clear H21.
exists (int_e x).
Compose_sepcon h322121 (h2 +++ h11 +++ h4 +++ h31 +++ h321 +++ h3222 +++ h32211).
Mapsto.
Intro_sepimp h322121' h'.
exists (int_e x0).
Compose_sepcon h32211 (h2 +++ h11 +++ h4 +++ h31 +++ h321 +++ h3222 +++ h322121').
Mapsto.
Intro_sepimp h32211' h''.
simpl in H10.
Decompose_sepcon H10 h311 h312.
Decompose_sepcon H37 h3121 h3122.
exists (nat_e next0).
Compose_sepcon h3121 (h2 +++ h11 +++ h4 +++ h311 +++ h321 +++ h32211' +++ h322121' +++ h3222).
Mapsto.
Intro_sepimp h3121' h'''.
Compose_sepcon (h3121' +++ h11 +++ h4 +++ h311 +++ h321 +++ h32211' +++ h322121' +++ h3222) h2.
generalize (hl_app l1 ((a,true)::(b,true)::l2) startp s 
 (((((((h3121' +++ h11) +++ h4) +++ h311) +++ h321) +++ h32211') +++
       h322121') +++ h3222)
); intro X; inversion_clear X.
apply H44; clear H44 H43.
Compose_sepcon h11  (((((((h3121') +++ h4) +++ h311) +++ h321) +++ h32211') +++
       h322121') +++ h3222).
auto.
eapply hl_Free with (h1 := h311 +++ h3121' +++ h321) (h2 := h4 +++ h32211' +++ h322121' +++ h3222).
Disjoint_heap.
Heap_emp_clean; Equal_heap.
auto.
intuition.
Compose_sepcon (h311 +++ h3121') h321.
simpl.
Compose_sepcon h311 h3121'.
Mapsto.
Compose_sepcon h3121' heap.emp.
Mapsto.
red; auto.
Array_equiv.
eapply hl_Free with (h1 := h32211' +++ h322121' +++ h3222) (h2 := h4).
Disjoint_heap.
Heap_emp_clean; Equal_heap.
auto.
intuition.
Compose_sepcon (h32211' +++ h322121') h3222.
simpl.
Compose_sepcon h32211' h322121'.
Mapsto.
Compose_sepcon h322121' heap.emp.
Mapsto.
red; auto.
Array_equiv.
subst next0.
cutrewrite(
get_endl l1 startp + 2 + a + 2 + b = get_endl l1 startp + 2 + (a + 2 + b)
).
auto.
omega.
cutrewrite(
(get_endl (l1 ++ (a, true) :: (b, true) :: l2) startp) = (get_endl (l1 ++ (a + 2 + b, true) :: l2) startp)
).
auto.
repeat rewrite get_endl_app.
simpl.
auto with *.
Qed.

(* several lemmas to change the status of blocks *)
Lemma hl_free2alloc: forall l1 l2 a startp s h,
   Heap_List (l1 ++ (a,true)::l2) startp s h ->
   exists y, ((nat_e (get_endl l1 startp) |-> y) **
   ((nat_e (get_endl l1 startp) |-> Allocated) -*
       (Heap_List (l1 ++ (a,false)::l2) startp ** Array (get_endl l1 startp + 2) a)))  s h.
intros.
Decompose_sepcon H h1 h2.
generalize (hl_app l1 ((a,true)::l2) startp s h1); intro X; inversion_clear X.
generalize (H2 H0); clear H2 H4 H0; intros.
Decompose_sepcon H0 h11 h12.
inversion_clear H6; try discriminate.
subst next0.
Decompose_sepcon H10 h31 h32.
Decompose_sepcon H9 h311 h312.
exists Free.
Compose_sepcon h311 (h312 +++ h32 +++ h4 +++ h11 +++ h2).
Mapsto.
Intro_sepimp h311' h'.
Compose_sepcon (h312 +++ h311' +++ h4 +++ h11 +++ h2) h32.
Compose_sepcon (h312 +++ h311' +++ h4 +++ h11) h2.
generalize (hl_app l1 ((a,false)::l2) startp s (h312 +++ h311' +++ h4 +++ h11)); intro X; inversion_clear X.
apply H20.
clear H20 H19.
Compose_sepcon h11 (h312 +++ h311' +++ h4).
auto.
eapply hl_Allocated with (h1 := (h312 +++ h311')) (h2 := h4).
Disjoint_heap.
Heap_emp_clean; Equal_heap.
auto.
intuition.
Compose_sepcon h311' h312.
Mapsto.
auto.
auto.
cutrewrite(
(get_endl (l1 ++ (a, false) :: l2) startp) = (get_endl (l1 ++ (a, true) :: l2) startp)
).
auto.
repeat rewrite get_endl_app; auto.
auto.
Qed.

Lemma hl_alloc2free: forall l1 l2 a startp s h,
   (Heap_List (l1 ++ (a,false)::l2) startp  ** Array (get_endl l1 startp + 2) a) s h ->
   exists y, ((nat_e (get_endl l1 startp) |-> y) **
   ( (nat_e (get_endl l1 startp) |-> Free) -*
       (Heap_List (l1 ++ (a,true)::l2) startp)))  s h.
intros.
Decompose_sepcon H h1 h2.
Decompose_sepcon H0 h11 h12.
generalize (hl_app l1 ((a,false)::l2) startp s h11); intro X; inversion_clear X.
generalize (H5 H2); clear H2 H5 H7; intros.
Decompose_sepcon H2 h111 h112.
inversion_clear H9; try discriminate.
Decompose_sepcon H13 h31 h32.
exists Allocated.
Compose_sepcon h31 (h32 +++ h4 +++ h111 +++ h12 +++ h2).
Mapsto.
Intro_sepimp h31' h'.
Compose_sepcon (h32 +++ h4 +++ h111 +++ h31' +++ h2) h12.
generalize (hl_app l1 ((a,true)::l2) startp s (h32 +++ h4 +++ h111 +++ h31' +++ h2)); intro X; inversion_clear X.
apply H21.
clear H21 H20.
Compose_sepcon h111 (h32 +++ h4 +++ h31' +++ h2).
auto.
eapply hl_Free with (h1 := h32 +++ h31' +++ h2) (h2 := h4).
Disjoint_heap.
Heap_emp_clean; Equal_heap.
auto.
apply H12.
Compose_sepcon (h32 +++ h31') h2.
Compose_sepcon h31' h32.
Mapsto.
auto.
auto.
auto.
cutrewrite(
(get_endl (l1 ++ (a, true) :: l2) startp) = (get_endl (l1 ++ (a, false) :: l2) startp)
).
auto.
repeat rewrite get_endl_app; auto.
Qed.

Lemma hl_free2free: forall l1 l2 a startp s h,
   Heap_List (l1 ++ (a,true)::l2) startp s h ->
   exists y, ((nat_e (get_endl l1 startp) |-> y) **
   ( (nat_e (get_endl l1 startp) |-> Free) -*
       (Heap_List (l1 ++ (a,true)::l2) startp)))  s h.
intros.
Decompose_sepcon H h1 h2.
generalize (hl_app l1 ((a,true)::l2) startp s h1); intro X; inversion_clear X.
generalize (H2 H0); clear H2 H4 H0; intros.
Decompose_sepcon H0 h11 h12.
inversion_clear H6; try discriminate.
subst next0.
Decompose_sepcon H10 h31 h32.
Decompose_sepcon H9 h311 h312.
exists Free.
Compose_sepcon h311 (h312 +++ h32 +++ h4 +++ h11 +++ h2).
Mapsto.
Intro_sepimp h311' h'.
Compose_sepcon (h312 +++ h311' +++ h4 +++ h11 +++ h32) h2.
generalize (hl_app l1 ((a,true)::l2) startp s (h312 +++ h311' +++ h4 +++ h11 +++ h32)); intro X; inversion_clear X.
apply H20.
clear H20 H19.
Compose_sepcon h11 (h312 +++ h311' +++ h4 +++ h32).
auto.
eapply hl_Free with (h1 := (h312 +++ h311' +++ h32)) (h2 := h4).
Disjoint_heap.
Heap_emp_clean; Equal_heap.
auto.
intuition.
Compose_sepcon (h311' +++ h312) h32.
Compose_sepcon h311' h312.
Mapsto.
auto.
auto.
auto.
auto.
Qed.

Lemma hl_getnext: forall l1 l2 a b startp s h,
   Heap_List (l1 ++ (a,b)::l2) startp s h ->
   ((nat_e (get_endl l1 startp + 1) |-> (nat_e (get_endl l1 startp + 2 + a))) **
   ((nat_e (get_endl l1 startp + 1) |-> (nat_e (get_endl l1 startp + 2 + a))) -*
       (Heap_List (l1 ++ (a,b)::l2) startp)
     ))  s h.
intros.
apply cell_read.
split.
Decompose_sepcon H h1 h2.
generalize (hl_app l1 ((a,b)::l2) startp s h1); intro X; inversion_clear X.
generalize (H2 H0); clear H2 H4 H0; intros.
Decompose_sepcon H0 h11 h12.
inversion_clear H6.
subst next0.
Decompose_sepcon H10 h31 h32.
Decompose_sepcon H9 h311 h312.
Decompose_sepcon H16 h3121 h3122.
Compose_sepcon h3121 (h311 +++ h32 +++ h4 +++ h11 +++ h2).
Mapsto.
red; auto.
subst next0.
Decompose_sepcon H10 h31 h32.
Decompose_sepcon H13 h321 h322.
Compose_sepcon h321 (h31 +++ h4 +++ h11 +++ h2).
Mapsto.
red; auto.
auto.
Qed.

Lemma hl_getstatus: forall l1 l2 a b startp s h,
   Heap_List (l1 ++ (a,b)::l2) startp s h ->
   ((nat_e (get_endl l1 startp) |-> (hlstat_bool2expr b)) **
   ((nat_e (get_endl l1 startp) |-> (hlstat_bool2expr b)) -*
       (Heap_List (l1 ++ (a,b)::l2) startp)
     ))  s h.
intros.
apply cell_read.
split.
Decompose_sepcon H h1 h2.
generalize (hl_app l1 ((a,b)::l2) startp s h1); intro X; inversion_clear X.
generalize (H2 H0); clear H2 H4 H0; intros.
Decompose_sepcon H0 h11 h12.
inversion_clear H6.
subst next0.
Decompose_sepcon H10 h31 h32.
Decompose_sepcon H9 h311 h312.
Decompose_sepcon H16 h3121 h3122.
Compose_sepcon h311 (h3121 +++ h32 +++ h4 +++ h11 +++ h2).
subst b.
Mapsto.
red; auto.
subst next0.
Decompose_sepcon H10 h31 h32.
Decompose_sepcon H13 h321 h322.
Compose_sepcon h31 (h321 +++ h4 +++ h11 +++ h2).
subst b.
Mapsto.
red; auto.
auto.
Qed.

Lemma hl_getnext': forall l startp s h,
   Heap_List l startp s h ->
   ((nat_e (get_endl l startp + 1) |-> (nat_e 0)) **
   ((nat_e (get_endl l startp + 1) |-> (nat_e 0)) -*
       (Heap_List l startp)
     ))  s h.
intros.
apply cell_read.
split; auto.
Decompose_sepcon H h1 h2.
simpl in H3.
Decompose_sepcon H3 h21 h22.
Decompose_sepcon H6 h221 h222.
Compose_sepcon h221 (h21 +++ h1).
Mapsto.
red; auto.
Qed.

Lemma hl_getstat': forall l startp s h,
   Heap_List l startp s h ->
   ((nat_e (get_endl l startp) |-> Allocated) **
   ((nat_e (get_endl l startp) |-> Allocated) -*
       (Heap_List l startp)
     ))  s h.
intros.
apply cell_read.
split; auto.
Decompose_sepcon H h1 h2.
simpl in H3.
Decompose_sepcon H3 h21 h22.
Decompose_sepcon H6 h221 h222.
Compose_sepcon h21 (h221 +++ h1).
Mapsto.
red; auto.
Qed.

Lemma In_hl_lt: forall l a b c startp,
  In_hl l (a,b,c) startp ->
  a < get_endl l startp.
induction l.
simpl; contradiction.
destruct a.
intros.
simpl.
simpl in H.
assert (beq_nat startp a && bool_eq c b && beq_nat n b0 = true \/ beq_nat startp a && bool_eq c b && beq_nat n b0 = false).
destruct (beq_nat startp a && bool_eq c b && beq_nat n b0); auto.
inversion_clear H0.
generalize (andb_prop _ _ H1); intros.
inversion_clear H0.
generalize (andb_prop _ _ H2); intros.
inversion_clear H0.
rewrite (beq_nat_true _ _ H4).
generalize (get_endl_gt l (a + 2 + n)); intros.
omega.
rewrite H1 in H.
eapply IHl.
apply H.
Qed.

Lemma In_hl_destruct: forall l a b c adr,   
   In_hl l (a,b,c) adr ->
   exists l1, exists l2, l = l1 ++ (b,c)::l2 /\ get_endl l1 adr = a.
induction l.
simpl.
intuition.
destruct a.
simpl; intros.
assert (beq_nat adr a && bool_eq c b && beq_nat n b0 = true \/ beq_nat adr a && bool_eq c b && beq_nat n b0 = false).
destruct (beq_nat adr a && bool_eq c b && beq_nat n b0); intuition.
inversion_clear H0.
generalize (andb_true_eq _ _ (sym_eq H1)); clear H1; intro X; inversion_clear X.
generalize (andb_true_eq _ _ H0); clear H0; intro X; inversion_clear X.
generalize (beq_nat_true _ _ (sym_eq H1)); intro; subst n.
generalize (beq_nat_true _ _ (sym_eq H0)); intro; subst a.
generalize (bool_eq_true _ _ (sym_eq H2)); intro; subst b.
exists (@nil (nat * bool)).
simpl.
exists l.
auto.
rewrite H1 in H.
generalize (IHl _ _ _ _ H); intro.
inversion_clear H0.
inversion_clear H2.
inversion_clear H0.
exists ((n,b)::x).
exists x0.
simpl.
rewrite H2; auto.
Qed.

Lemma In_hl_ge_start: forall l x y z adr,
 In_hl l (x,y,z) adr -> x >= adr.
induction l.
simpl; intuition.
destruct a; simpl; intros.
assert (beq_nat adr x && bool_eq z b && beq_nat n y = true \/
beq_nat adr x && bool_eq z b && beq_nat n y = false).
destruct (beq_nat adr x && bool_eq z b && beq_nat n y); auto.
inversion_clear H0.
generalize (andb_prop _ _ H1); intro X; inversion_clear X.
generalize (andb_prop _ _ H0); intro X; inversion_clear X.
rewrite (beq_nat_true _ _ H3).
auto.
rewrite H1 in H.
generalize (IHl _ _ _ _ H); intros.
omega.
Qed.

Lemma In_hl_dif: forall l x y a b adr,
 In_hl l (x,y,alloc) adr -> In_hl l (a,b,free) adr -> a <> x.
induction l.
intuition.
destruct a.
intros.
simpl in H.
simpl in H0.
assert (beq_nat adr x && bool_eq alloc b && beq_nat n y = true \/
beq_nat adr x && bool_eq alloc b && beq_nat n y = false).
destruct (beq_nat adr x && bool_eq alloc b && beq_nat n y); auto.
assert (beq_nat adr a && bool_eq free b && beq_nat n b0 = true \/
beq_nat adr a && bool_eq free b && beq_nat n b0 = false).
destruct (beq_nat adr a && bool_eq free b && beq_nat n b0); auto.
inversion_clear H1; inversion_clear H2.
generalize (andb_prop _ _ H3); intro X; inversion_clear X.
generalize (andb_prop _ _ H2); intro X; inversion_clear X.
generalize (andb_prop _ _ H1); intro X; inversion_clear X.
generalize (andb_prop _ _ H7); intro X; inversion_clear X.
rewrite <- (bool_eq_true _ _ H6) in H10; simpl in H10; inversion H10.
generalize (andb_prop _ _ H3); intro X; inversion_clear X.
generalize (andb_prop _ _ H2); intro X; inversion_clear X.
rewrite H3 in H; rewrite H1 in H0.
generalize (beq_nat_true _ _ H5); intros.
subst x.
generalize (In_hl_ge_start _ _ _ _ _ H0); intros.
omega.
generalize (andb_prop _ _ H1); intro X; inversion_clear X.
generalize (andb_prop _ _ H2); intro X; inversion_clear X.
rewrite H3 in H; rewrite H1 in H0.
generalize (beq_nat_true _ _ H5); intros.
subst a.
generalize (In_hl_ge_start _ _ _ _ _ H); intros.
omega.
rewrite H3 in H; rewrite H1 in H0.
eapply IHl.
apply H.
apply H0.
Qed.

Lemma In_hl_match: forall l1 l2 x y size stat startp,
  In_hl (l1 ++ (x,y)::l2) (get_endl l1 startp, size, stat) startp ->
  (size = x /\ stat = y).
induction l1.
simpl; intros.
assert (beq_nat startp startp && bool_eq stat y && beq_nat x size = true \/ beq_nat startp startp && bool_eq stat y && beq_nat x size = false).
destruct (beq_nat startp startp && bool_eq stat y && beq_nat x size); intuition.
inversion_clear H0.
clear H.
generalize (andb_prop _ _ H1); intros.
inversion_clear H.
generalize (andb_prop _ _ H0); intros.
inversion_clear H.
rewrite (bool_eq_true _ _ H4).
rewrite (beq_nat_true _ _ H2).
auto.
rewrite H1 in H.
generalize (In_hl_ge_start _ _ _ _ _ H); intros.
assert (startp < startp + 2 + x).
omega.
assert (~(startp >= startp + 2 + x /\ startp < startp + 2 + x)).
omega.
intuition.
destruct a; intros.
simpl in H.
assert (beq_nat startp (get_endl l1 (startp + 2 + n)) && bool_eq stat b && beq_nat n size = false).
apply andb_false_intro1.
apply andb_false_intro1.
assert (startp <> get_endl l1 (startp + 2 + n)).
generalize (get_endl_gt l1 (startp + 2 + n)); intros.
intuition.
apply (beq_dif_false _ _ H0).
rewrite H0 in H; clear H0.
eapply IHl1.
apply H.
Qed.

Lemma In_hl_next: forall l x y z b c adr,
  In_hl l (x,y,z) adr ->
  In_hl l (x + 2 + y,b,c) adr ->
  exists l1,
    exists l2,
      l = l1 ++ (y,z)::(b,c)::l2 /\
      x = get_endl l1 adr.
induction l.
simpl; intuition.
destruct a; simpl; intros.
assert(
beq_nat adr x && bool_eq z b && beq_nat n y = true \/
beq_nat adr x && bool_eq z b && beq_nat n y = false
).
destruct (beq_nat adr x && bool_eq z b && beq_nat n y); auto.
inversion_clear H1.
rewrite H2 in H.
generalize (andb_prop _ _ H2); clear H2; intro X; inversion_clear X.
generalize (andb_prop _ _ H1); clear H1; intro X; inversion_clear X.
assert (beq_nat adr (x + 2 + y) && bool_eq c b && beq_nat n b0 = false).
apply andb_false_intro1.
apply andb_false_intro1.
rewrite (beq_nat_true _ _ H1).
apply beq_dif_false.
omega.
rewrite H4 in H0.
generalize (beq_nat_true _ _ H2); intro; subst y.
generalize (beq_nat_true _ _ H1); intro; subst x.
generalize (In_hl_destruct _ _ _ _ _ H0); intros.
Decompose_hyp.
rewrite H6 in H0.
destruct x.
simpl in H7.
exists (@nil (nat* bool)).
exists x0.
rewrite H6.
rewrite (bool_eq_true _ _ H3).
auto.
destruct p.
simpl in H7.
generalize (get_endl_gt x (adr + 2 + n + 2 + n0)); intros.
rewrite H7 in H5.
assert (~ (adr + 2 + n + 2 + n0 <= adr + 2 + n)).
omega.
tauto.
rewrite H2 in H.
assert (beq_nat adr (x + 2 + y) && bool_eq c b && beq_nat n b0 = false).
apply andb_false_intro1.
apply andb_false_intro1.
apply beq_dif_false.
generalize (In_hl_ge_start _ _ _ _ _ H); intros.
intuition.
rewrite H1 in H0.
generalize (IHl _ _ _ _ _ _ H H0); intros.
Decompose_hyp.
exists ((n,b):: x0); exists x1.
simpl.
split.
rewrite H4.
auto.
auto.
Qed.


Lemma In_hl_last: forall l a b c adr,
  In_hl l (a,b,c) adr ->
  get_endl l adr = a + 2 + b ->
  exists l', l = l'++ (b,c)::nil.
  induction l.
  simpl; intros; contradiction.
  intros.
  destruct a.
  generalize (In_hl_lt _ _ _ _ _ H); intros.
  simpl in H1.
  simpl in H.
  assert (beq_nat adr a0 && bool_eq c b0 && beq_nat n b = true \/ 
  beq_nat adr a0 && bool_eq c b0 && beq_nat n b = false).
  destruct (beq_nat adr a0 && bool_eq c b0 && beq_nat n b); intuition.
  inversion_clear H2.
  clear H.
  generalize (andb_prop _ _ H3); clear H3; intros; Decompose_hyp.
  generalize (andb_prop _ _ H2); clear H2; intros; Decompose_hyp.
  simpl in H0.
  generalize (beq_nat_true _ _ H3);   generalize (beq_nat_true _ _ H2); intros; subst a0 n.
  destruct l.
  generalize (bool_eq_true _ _ H4); intros; subst b0.
  exists (@nil (nat*bool)).
  repeat rewrite <- ass_app; repeat rewrite <- app_nil_end; repeat rewrite <- app_comm_cons; auto.
  simpl in H0.
  destruct p.
  generalize (get_endl_gt l (adr + 2 + b + 2 + n)); intros.
  rewrite H0 in H.
  assert (False); [omega | contradiction].
  rewrite H3 in H.
  simpl in H0.
  generalize (IHl _ _ _ _ H H0); intros.
  Decompose_hyp.
  subst l.
  exists ((n,b0)::x); auto.
Qed.


Lemma In_hl_first: forall l adr sz st,
  In_hl l (adr,sz,st) adr ->  
  exists l', l = (sz,st)::l'.
  induction l.
  simpl; intros; contradiction.
  intros.
  destruct a.
  simpl in H.
  assert (beq_nat adr adr && bool_eq st b && beq_nat n sz0 = true \/ 
  beq_nat adr adr && bool_eq st b && beq_nat n sz0 = false).
  destruct (beq_nat adr adr && bool_eq st b && beq_nat n sz0); intuition.
  inversion_clear H0.
  generalize (andb_prop _ _ H1); clear H1; intros; Decompose_hyp.
  generalize (andb_prop _ _ H1); clear H1; intros; Decompose_hyp.
  generalize (beq_nat_true _ _ H2); intros; subst n.
  generalize (bool_eq_true _ _ H3); intros; subst b.  
  exists l; auto.
  rewrite H1 in H; clear H1.
  generalize (In_hl_ge_start _ _ _ _ _ H); intros.
  assert (False); [omega | contradiction].
Qed.


(***********)
(* Tactics *)
(***********)

(* debug function *)

Ltac Print x := assert (x=x); [auto | idtac].

(* same as cutrewrite but for a hypothesis *)

Ltac Cutrewrite_hyp H A :=
  match A with
    | ?x = ?x => idtac
    | _ => 
      let x:= fresh in 
        (
          assert (x: A); [idtac | rewrite x in H; clear x]
        )
  end.

(* Finding a contradiction in boolean expression *)

Ltac Omega_exprb_contradiction_assert P :=
  assert (P); Omega_exprb.

Ltac Omega_exprb_contradiction :=
  match goal with
    | id: ?s |b= ?P |- _ => assert (False); [Omega_exprb_contradiction_assert (s |b/= P) | contradiction]
    | id: ?s |b/= ?P |- _ => assert (False); [Omega_exprb_contradiction_assert (s |b= P) | contradiction]
  end.


(* destruct a hl list that contains an element *)

Ltac In_hl_destruct_hyp H :=
  match goal with
    | H: In_hl ?l (?adr, ?size, ?status) ?start |- _ =>
      generalize (In_hl_destruct l adr size status start H); intros; Decompose_hyp; subst l
  end.

(* Tactic that compute the equilence of a hl list such that it can be use by hl_getxxx *)

  Ltac HLList_head l :=
    match l with
      | ?hd::?tl => constr:(hd::nil)
      | ?l1 ++ ?l2 => 
        let x:=(HLList_head l1) in (
          match x with
            | nil => l1
            | _ => x
          end
        )   
      | _ => l
    end.

  Ltac HLList_tail l :=
    match l with
      | ?hd::?tl => tl
      | ?l1 ++ ?l2 => 
        let x:=(HLList_tail l1) in (
          match x with
            | nil => l2
            | _ => constr:(x ++ l2)
          end
        )   
      | _ => constr:(@nil (nat*bool))
    end.

  Ltac Normalize_HLList l :=    
    match l with
      | nil => constr:(@nil (nat*bool))
      | _ => 
        let hd := (HLList_head l) in (
          let tl := (HLList_tail l) in (
            let tl' := (Normalize_HLList tl) in (
              match tl' with
                | nil => hd
                | _ => constr:(hd ++ tl')
              end
            )
          )
        )
    end.


  Ltac Format_HLList_head l elt :=
    match l with
      | ((elt,?st)::nil) => constr:(@nil (nat*bool))
      | ((elt,?st)::nil) ++ ?l2 => constr:(@nil (nat*bool))
      | ?l1 ++ ?l2 => 
        let hd:= (Format_HLList_head l2 elt) in (
          match hd with
            | nil => l1
            | _ => constr:(l1 ++ hd)
          end          
          )        
    end.


  Ltac Format_HLList_tail l elt :=
    match l with
      | ((elt,?st)::nil) => l
      | ((elt,?st)::nil) ++ ?l2 => constr:((elt,st)::l2)
      | ?l1 ++ ?l2 => 
        let tl := (Format_HLList_tail l1 elt) in (
          match tl with
            | nil => (Format_HLList_tail l2 elt)
            | _ => constr:(tl ++ l2)
          end
        ) 
      | _ => constr:(@nil (nat*bool))
    end.


  Ltac Format_HLList l elt :=
    let y:= (Normalize_HLList l) in (
      let hd:= (Format_HLList_head y elt) in (
        let tl:= (Format_HLList_tail y elt) in (
          constr:(hd ++ tl)
        )
      )
    ).


  (* Resolve a goal for equality of two list (only if equal term to term) *)
  
  Ltac List_eq :=
    repeat rewrite <- ass_app; repeat rewrite <- app_nil_end; repeat rewrite <- app_comm_cons; auto.


 (* Resolve the first hypothese of the cell_read lemma using hl_getstatus given
      H: the Heap_List Hypothesis
      elt: the size of the block
  *)
  Ltac Hl_getstatus H elt :=
    match goal with
      | H: Heap_List ?l ?start ?s ?h |- _ =>
        let l' := (Format_HLList l elt) in (
          match l with
            | l' =>
              let h1:= fresh in(
                let h2:= fresh in (
                  let x:= fresh in (
                    generalize (hl_getstatus _ _ _ _ _ _ _ H); intro x; Decompose_sepcon x h1 h2;
                      Compose_sepcon h1 h2; [idtac | red; auto]
                  )
                )
              )              
            | _ =>
                  Cutrewrite_hyp H (l = l'); [List_eq |
                    (let h1:= fresh in(
                      let h2:= fresh in (
                        let x:= fresh in (
                          generalize (hl_getstatus _ _ _ _ _ _ _ H); intro x; Decompose_sepcon x h1 h2;
                            Compose_sepcon h1 h2; [idtac | red; auto]
                        )
                      )
                    )
                    )
                  ]
          end
          )
          
    end.

  (* Same thing but for Hl_getstat' *)

  Ltac Hl_getstat' H :=
    let h1:= fresh in(
      let h2:= fresh in (
        let x:= fresh in (
          generalize (hl_getstat' _ _ _ _ H); intro x; Decompose_sepcon x h1 h2;
            Compose_sepcon h1 h2; [idtac | red; auto]
        )
      )
    ).


  (* Same thing but for Hl_getnext *)

  Ltac Hl_getnext H elt :=
    match goal with
      | H: Heap_List ?l ?start ?s ?h |- _ =>
        let l' := (Format_HLList l elt) in (
          match l with
            | l' =>
              let h1:= fresh in(
                let h2:= fresh in (
                  let x:= fresh in (
                    generalize (hl_getnext _ _ _ _ _ _ _ H); intro x; Decompose_sepcon x h1 h2;
                      Compose_sepcon h1 h2; [idtac | red; auto]
                  )
                )
              )              
            | _ =>
                  Cutrewrite_hyp H (l = l'); [List_eq |
                    (let h1:= fresh in(
                      let h2:= fresh in (
                        let x:= fresh in (
                          generalize (hl_getnext _ _ _ _ _ _ _ H); intro x; Decompose_sepcon x h1 h2;
                            Compose_sepcon h1 h2; [idtac | red; auto]
                        )
                      )
                    )
                    )
                  ]
          end
          )
          
    end.

  (* Same thing but for Hl_getnext' *)

  Ltac Hl_getnext' H :=
    let h1:= fresh in(
      let h2:= fresh in (
        let x:= fresh in (
          generalize (hl_getnext' _ _ _ _ H); intro x; Decompose_sepcon x h1 h2;
            Compose_sepcon h1 h2; [idtac | red; auto]
        )
      )
    ).
    
  
  


