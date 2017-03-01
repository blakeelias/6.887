Require Import Frap Pset3Sig.


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


