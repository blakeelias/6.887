Require Import Frap Pset2Sig.
Require Import OrdersFacts.

(* For your convenience, we beforehand provide some useful facts about orders.
 * You can skim through the list of theorems by using "Print," or visiting 
 * this page:
 * https://coq.inria.fr/library/Coq.Structures.OrdersFacts.html
 *)
Include (OrderedTypeFacts Pset2Sig).
Include (OrderedTypeTest Pset2Sig).
Print OrderedTypeFacts.
(* Print OrderedTypeTest. *)

(* Our proof also uses the following facts that have been included above from libraries. *)
Check eq_lt.
Check eq_sym.
Check lt_eq.
Check lt_not_eq.
Check lt_trans.
Check compare_refl.
Check compare_lt_iff. (* Note that this one can be used with [apply], despite the fact that it
                       * includes an "if and only if" ([<->]) where other theorems use simple
                       * implication ([->]). *)
Check compare_gt_iff.
Check compare_eq_iff.

Theorem insert_member: forall tr n, BST tr -> member n (insert n tr) = true.
Proof.
induct tr.
simplify.
rewrite compare_refl.
equality.
simplify.
cases (compare n t).
simplify.
rewrite Heq; equality.
simplify.
rewrite Heq.
rewrite IHtr1; equality.
simplify.
rewrite Heq.
rewrite IHtr2; equality.
Qed.

Lemma insert_less_than: forall tr n a, BST tr /\ tree_lt a tr /\ lt n a -> tree_lt a (insert n tr).
Proof.
induct tr.
simplify.
propositional.
simplify.
case (compare n t).
simplify.
propositional.
simplify.
propositional.
apply IHtr1.
propositional.
simplify.
propositional.
apply IHtr2.
propositional.
Qed.

Lemma insert_greater_than: forall tr n a, BST tr /\ tree_gt a tr /\ lt a n -> tree_gt a (insert n tr).
induct tr.
simplify.
propositional.
simplify.
case (compare n t).
simplify.
propositional.
simplify.
propositional.
apply IHtr1.
propositional.
simplify.
propositional.
apply IHtr2.
propositional.
Qed.



Theorem insert_ok: forall tr n, BST tr -> BST (insert n tr).
Proof.
(*intros n tr.
simplify.
case (insert tr n).
simplify. equality.*)


induct tr.
simplify.
propositional.
simplify.
cases (compare n t).
simplify.
propositional.
simplify.
propositional.
apply IHtr1.
apply H0.
simplify.
apply insert_less_than.
propositional.
apply compare_lt_iff.
apply Heq.

simplify.
propositional.
apply IHtr2.
apply H1.
apply insert_greater_than.
propositional.
apply compare_gt_iff.
apply Heq.
Qed.

(* Lemma tree_max: forall tr n, tree_lt (rightmost tr) tr. *)

Lemma rightmost_tree_lt:
  forall tr v n, tree_lt n tr -> rightmost tr = Some v -> compare v n = Lt.
Proof.
  induct tr; simplify.
  - equality.
  - cases tr2; simplify; first_order.
    apply compare_lt_iff.
    equality.
Qed.

Lemma rightmost_tree_gt:
  forall tr v n, tree_gt n tr -> rightmost tr = Some v -> compare v n = Gt.
Proof.
  induct tr; simplify.
  - equality.
  - cases tr2; simplify; first_order.
    apply compare_gt_iff.
    equality.
Qed.

Lemma delete_rightmost_tree_lt:
  forall tr n, tree_lt n tr -> tree_lt n (delete_rightmost tr).
Proof.
  induct tr; simplify; propositional.
  cases tr2; simplify; propositional.
  apply IHtr2.
  propositional.
Qed.

Lemma delete_rightmost_tree_gt:
  forall tr n, tree_gt n tr -> tree_gt n (delete_rightmost tr).
Proof.
  induct tr; simplify; propositional.
  cases tr2; simplify; propositional.
  apply IHtr2.
  propositional.
Qed.

Lemma delete_tree_lt:
  forall tr v n, tree_lt n tr -> tree_lt n (delete v tr).
Proof.
  induct tr; simplify; propositional.
  cases (compare v t); simplify; propositional.
  - cases (rightmost tr1); simplify; propositional.
    + apply compare_lt_iff.
      apply rightmost_tree_lt with (tr := tr1).
      assumption.
      assumption.
    + apply delete_rightmost_tree_lt.
      assumption.
  - apply IHtr1.
    assumption.
  - apply IHtr2.
    assumption.
Qed.

Lemma delete_tree_gt:
  forall tr v n, tree_gt n tr -> tree_gt n (delete v tr).
Proof.
  induct tr; simplify; propositional.
  cases (compare v t); simplify; propositional.
  - cases (rightmost tr1); simplify; propositional.
    + apply compare_gt_iff.
      apply rightmost_tree_gt with (tr := tr1).
      assumption.
      assumption.
    + apply delete_rightmost_tree_gt.
      assumption.
  - apply IHtr1.
    assumption.
  - apply IHtr2.
    assumption.
Qed.

Lemma tree_lt_sub:
  forall tr x y, lt x y -> tree_lt x tr -> tree_lt y tr.
Proof.
  induct tr; simplify; propositional.
  apply lt_trans with (y := x); assumption.
  apply IHtr1 with (x := x); assumption.
  apply IHtr2 with (x := x); assumption.
Qed.

Lemma tree_gt_sub:
  forall tr x y, lt y x -> tree_gt x tr -> tree_gt y tr.
Proof.
  induct tr; simplify; propositional.
  apply lt_trans with (y := x); assumption.
  apply IHtr1 with (x := x); assumption.
  apply IHtr2 with (x := x); assumption.
Qed.

Lemma delete_rightmost_rightmost_tree_lt:
  forall tr v, BST tr -> rightmost tr = Some v -> tree_lt v (delete_rightmost tr).
Proof.
induct tr; simplify; propositional.
Check Some v.
Check Some t.
cases tr2.
equality.
simplify.
propositional.
cases tr2_2.
equality.
Check lt_trans.
Check compare_gt_iff.
apply compare_gt_iff.
Check rightmost_tree_gt.
apply rightmost_tree_gt with (tr := (Node t1 tr2_2_1 tr2_2_2)).
assumption. assumption.
cases tr2_2.
invert H0.
apply tree_lt_sub with (x := t); assumption.
apply tree_lt_sub with (x := t).

Check compare_gt_iff.
apply compare_gt_iff.
Check rightmost_tree_gt.
apply rightmost_tree_gt with (tr := (Node t1 tr2_2_1 tr2_2_2)).
assumption. assumption. assumption.
apply IHtr2.
propositional.
propositional.
Qed.

Lemma delete_rightmost_rightmost_tree_gt:
  forall tr1 tr2 n v,
    tree_lt n tr1 -> tree_gt n tr2 ->
    BST tr1 -> rightmost tr1 = Some v -> tree_gt v tr2.
Proof.
induct tr2; simplify; propositional.
apply compare_lt_iff.
apply rightmost_tree_lt with (tr := tr1).
apply tree_lt_sub with (x := n). assumption.
assumption. assumption.
apply IHtr2_1 with (n := n). assumption. assumption.
assumption. assumption.
apply IHtr2_2 with (n := n); assumption.
Qed.

(*Lemma delete_rightmost_BST: forall tr, BST tr -> BST (delete_rightmost tr).
Proof.
Admitted.
*)
(*
induct tr.
simplify. equality.
simplify.
cases tr2.
apply H.
simplify.
propositional.
cases tr2_2.
apply H4.
*)

Lemma delete_rightmost_BST:
  forall tr, BST tr -> BST (delete_rightmost tr).
  induct tr. simplify. propositional.
  simplify.
  cases tr2. apply H.
  simplify. propositional.
  cases tr2_2.
  assumption.
  Check rightmost_tree_gt.

Admitted.

(*
Proof.
  induct tr.
  simplify.
  propositional.
  simplify.
  case tr2.
  apply H.
  simplify.
  propositional.
  cases t2.
  assumption.

induct tr.
simplify. equality.
simplify.
cases tr2.
propositional.
simplify.
propositional.
cases tr2_2.
assumption.
simplify.
propositional.
cases tr2_2_2.
assumption.
*)


Theorem delete_ok: forall tr n, BST tr -> BST (delete n tr).
Proof.
induct tr.
simplify. equality.
simplify.
cases (compare n t).
cases (rightmost tr1).
simplify.
propositional.

simplify.

apply delete_rightmost_BST. apply H0.
apply delete_rightmost_rightmost_tree_lt. assumption.
assumption.
apply delete_rightmost_rightmost_tree_gt with (tr1:=tr1) (tr2:=tr2) (n:=t) (v:=t0).
assumption.
assumption.
assumption.
assumption.
apply H.
simplify.
propositional.
apply IHtr1. assumption.
apply delete_tree_lt. assumption.
simplify.
propositional.
apply IHtr2. assumption.
apply delete_tree_gt. assumption.
Qed.


(* OPTIONAL PART! *)
(*Theorem delete_member: forall tr n, BST tr -> member n (delete n tr) = false.
Proof.
Admitted.*)
