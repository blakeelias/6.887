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

Theorem delete_ok: forall tr n, BST tr -> BST (delete n tr).
Proof.
(*induct tr.
simplify. equality.
simplify.
cases (compare n t).
cases (rightmost tr1).
simplify.
propositional.
cases (delete_rightmost tr1).
simplify. equality.
simplify.
propositional.
apply H*)


(* OPTIONAL PART! *)
(*Theorem delete_member: forall tr n, BST tr -> member n (delete n tr) = false.
Proof.
Admitted.*)
