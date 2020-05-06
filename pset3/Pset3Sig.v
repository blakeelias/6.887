(** * 6.887 Formal Reasoning About Programs, Spring 2017 - Pset 3 *)

(* Authors: 
 * Blake Elias
 *)

(** * Correctness of XML/XPATH *)

Require Import Frap.
Require Import String.

Inductive tree :=
| Leaf (name : string) (value : string)
| Node (name : string) (left : tree) (right : tree).

Inductive tree_with_parent :=
| Root (tr : tree)
| Child (tr : tree) (parent: tree_with_parent).

Inductive xpath : Set :=
| ChildrenWithName (name : string)
| NodesWithValue (v : string)
| Parents
| Descendents.

Definition selection := list tree_with_parent.

Fixpoint name (tr : tree) : string := 
  match tr with
  | Leaf name value => name
  | Node name tr1 tr2 => name
  end.

Fixpoint value (tr : tree) : option string := 
  match tr with
  | Leaf name value => Some value
  | Node name tr1 tr2 => None
  end.

Fixpoint children (tr : tree) (p : tree_with_parent) : list tree_with_parent :=
  match tr with
  | Leaf name value => nil
  | Node name tr1 tr2 => [Child tr1 p; Child tr2 p]
end.

Fixpoint child1 (tr : tree) (p : tree_with_parent) : list tree_with_parent :=
  match tr with
  | Leaf name value => nil
  | Node name tr1 tr2 => [Child tr1 p]
end.

Fixpoint child2 (tr : tree) (p : tree_with_parent) : list tree_with_parent :=
  match tr with
  | Leaf name value => nil
  | Node name tr1 tr2 => [Child tr2 p]
end.


(** Parents Command **)

Fixpoint parent (trp : tree_with_parent) : selection :=
match trp with
| Root _ => nil
| Child _ parent => [parent]
end.

Fixpoint parents (sel : selection) : selection :=
  flat_map parent sel.

(** ChildrenWithName command **)
Fixpoint getChildren (trp : tree_with_parent) : selection :=
match trp with
| Root tr => (children tr trp)
| Child tr p => (children tr trp)
end.
Fixpoint getChildrenList (sel : selection) : selection :=
flat_map getChildren sel.

Fixpoint getNodesWithName (sel : selection) (name : string) : selection :=
match sel with
| nil => nil
| s :: s' =>
  (match s with
  | Root tr =>
    match tr with
    | Leaf n v => if name ==v n then [s] else []
    | Node n _ _ => if name ==v n then [s] else []
    end
  | Child tr parent => 
    match tr with
    | Leaf n v => if name ==v n then [s] else []
    | Node n _ _ => if name ==v n then [s] else []
    end
  end) ++ getNodesWithName s' name
end.

Fixpoint children_with_name (sel : selection) (name : string) : selection :=
getNodesWithName (getChildrenList sel) name.

(** NodesWithValue command **)

Fixpoint nodes_with_value (sel : selection) (value : string) : selection :=
match sel with
| nil => nil
| s :: s' =>
  (match s with
  | Root tr =>
    match tr with
    | Leaf _ v => if value ==v v then [s] else []
    | Node _ _ _ => []
    end
  | Child tr parent => 
    match tr with
    | Leaf _ v => if value ==v v then [s] else []
    | Node _ _ _ => []
    end
  end) ++ nodes_with_value s' value
end.


(** Descedants command **)

(*
descendents'' fxml -> fxml_p -> list fxml_p
descendents' : fxml_p -> list fxml_p
  descendents' calls descendents'' 

Fixpoint descendants'' (tr : tree) (trp : tree_with_parent) : selection :=
match tr with
| Leaf n v => nil
| Node n tr1 tr2 => tr :: (descendants (child1 tr trp)) ++ (descendants (child2 tr trp))
end.
trp :: descendants'' (children tr) (getChildren trp)

Fixpoint descendants' (trp : tree_with_parent) : selection :=
match trp with
| Root tr => descendants'' tr trp
| Child tr _ => descendants'' tr trp
end.

Fixpoint descendants (sel : selection) : selection :=
sel ++ (descendants getChildren sel). *)


(* Can try constructing a node as follows: 
Let n1 = NodeWithValue "number" "6.009".
*)

Fixpoint interp1 (instruction : xpath) (s : selection) : selection :=
match instruction with
| ChildrenWithName n => children_with_name s n
| NodesWithValue v => nodes_with_value s v
| Parents => parents s
| Descendents => nil (* put this back in when I have a function for it! *)
end.

Fixpoint interp (instructions : list xpath) (s : selection) : selection :=
  match instructions with
  | nil => s
  | instruction :: instructions' => interp instructions' (interp1 instruction s)
  end.

(** Begin proofs below **)

Theorem flat_map_append {A B} : forall (f : A -> list B) x y,
(flat_map f (x ++ y)) = (flat_map f x) ++ (flat_map f y).
Proof.
induction x; simplify.
equality.
rewrite IHx.
apply app_assoc.
Qed.

Theorem no_extra_children: forall root n1 n2 x,
  In x (interp [ (ChildrenWithName n1) ; (ChildrenWithName n2) ; Parents ] [root])
  -> In x (interp [ (ChildrenWithName n1) ] [root]).
Proof.


Lemma parentsList_children : forall sel x,
    In x (parents (getChildrenList sel)) -> In x sel.
  Proof.
Admitted.

  Lemma children_with_node_name_subset_children : forall (sel : selection) name child,
    In child (children_with_name sel name) -> 
      In child (getChildrenList sel).
  Proof.
    induct sel.
    simplify.
    equality.

    simplify.
    cases a; simplify.
    unfold flat_map.
  Admitted.

  Lemma parent_child_commands : forall y root n,
    In y (interp [ ChildrenWithName n ; Parents ] [root]) -> In y [root].
  Proof.

  simplify.

  cases root.

  Lemma cancel_out_identical_prefix : forall selection prefix instr1 instr2 x,
    (In x (interp instr1 selection) -> In x (interp instr2 selection)) ->
    (In x (interp (prefix ++ instr1) selection) -> In x (interp (prefix ++ instr2) selection)).
  Proof.
  Admitted.

  intros root n1 n2 x.

  apply cancel_out_identical_prefix with (prefix := [NodeName n1]).
  apply parent_child_commands.

(*  unfold .

  apply parent_child_commands with (root := (interp1 (NodeName n1) [root])) (n := n2).

  simplify.

  cases root; simplify.
  equality.
  equality.
  case (Top.hasName n1 root1).
  case (Top.hasName n1 root2); simplify. *)


 (* unsure where to go next. Probably would need to use parent_child axiom somewhere
  * here - though unsure if taking that as an axiom is just assuming what I'm supposed to prove! *)
