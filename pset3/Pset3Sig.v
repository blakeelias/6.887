(** * 6.887 Formal Reasoning About Programs, Spring 2017 - Pset 3 *)

(* Authors: 
 * Blake Elias
 *)

(** * Correctness of XML/XPATH *)

Require Import String.
Require Import List.


Inductive tree :=
| Leaf: tree
| NodeWithValue: string -> string -> tree
| NodeWithChildren: string -> tree -> tree -> tree.

(* Then a singleton is just a node without subtrees. *)
Definition Singleton (n: string) (v: string) := NodeWithValue n v.

Inductive xpath : Set :=
| NodeName (name : string)
| Value (v : string)
| Parents
| Descendents.

Definition selection := list tree.

Fixpoint name (tr : tree) : option string := 
  match tr with
  | Leaf => None
  | NodeWithValue name value => Some name
  | NodeWithChildren name tr1 tr2 => Some name
  end.

Fixpoint value (tr : tree) : option string := 
  match tr with
  | Leaf => None
  | NodeWithValue name value => Some value
  | NodeWithChildren name tr1 tr2 => None
  end.

Fixpoint children (tr : tree) : list tree :=
  match tr with
  | Leaf => nil
  | NodeWithValue name value => nil
  | NodeWithChildren name tr1 tr2 => tr1 :: ( cons tr2 nil )
end.

Fixpoint childrenList (trs : list tree) : list tree :=
  flat_map children trs.

Fixpoint descendents (tr : tree) : list tree :=
  match tr with
  | Leaf => Leaf :: nil
  | NodeWithValue name value => NodeWithValue name value :: nil
  | NodeWithChildren name tr1 tr2 => (NodeWithChildren name tr1 tr2) :: (descendents tr1 ++ descendents tr2)
  end. 

Fixpoint descendentsList (trList : list tree) : list tree :=
  flat_map descendents trList.

Compute prefix "abc" "abcd".

Fixpoint string_eq (str1 str2 : string) : bool :=
  andb (prefix str1 str2) (prefix str2 str1).

Fixpoint hasValue (val : string) (tr : tree) : bool :=
  match tr with
  | Leaf => false
  | NodeWithValue name value => string_eq val value
  | NodeWithChildren name tr1 tr2 => false
  end.

Fixpoint getNodesWithValue (selectedTreeList : list tree) (val : string) : list tree :=
  filter (hasValue val) selectedTreeList.

Fixpoint hasName (name : string) (tr : tree) : bool :=
  match tr with
  | Leaf => false
  | NodeWithValue n v => string_eq n name
  | NodeWithChildren n tr1 tr2 => string_eq n name
  end.

Fixpoint getNodesWithNodeName (treeList : list tree) (name : string) : list tree :=
  filter (hasName name) treeList.

Fixpoint childrenWithNodeName (selection : list tree) (name : string) : list tree :=
  match selection with
  | tr :: l => (match tr with
    | Leaf => nil
    | NodeWithValue n v => nil
    | NodeWithChildren n tr1 tr2 => (if (hasName name tr1) then (cons tr1 nil) else nil) ++ (if (hasName name tr2) then (cons tr2 nil) else nil)
    end) ++ childrenWithNodeName l name
  | nil => nil
  end.

Fixpoint tree_eq (tr1 tr2 : tree) : bool :=
  match tr1 with
  | Leaf => 
    match tr2 with
    | Leaf => true
    | NodeWithValue n v => false
    | NodeWithChildren n tr1 tr2 => false
    end
  | NodeWithValue n1 v1 => match tr2 with
    | Leaf => false
    | NodeWithValue n2 v2 => andb (string_eq n1 n2) (string_eq v1 v2)
    | NodeWithChildren n tr1 tr2 => false
    end
  | NodeWithChildren n1 tr1_1 tr1_2 => match tr2 with
    | Leaf => false
    | NodeWithValue n2 v2 => false
    | NodeWithChildren n2 tr2_1 tr2_2 => (string_eq n1 n2) && (tree_eq tr1_1 tr2_1) && (tree_eq tr1_2 tr2_2)
    end
  end.

Fixpoint isParent (child parent : tree) : bool :=
  match parent with
  | Leaf => false
  | NodeWithValue name value => false
  | NodeWithChildren n tr1 tr2 => (orb (tree_eq child tr1) (tree_eq child tr2))
  end.

Fixpoint parents (tr root : tree) : list tree :=
   filter (isParent tr) (descendents root).

Fixpoint parentsList (root : tree) (treeList : list tree) : list tree :=
  flat_map (parents root) treeList.

(* Can try constructing a node as follows: 
Let n1 = NodeWithValue "number" "6.009".
*)

Fixpoint interp1 (instruction : xpath) (s : selection) : selection :=
  match instruction with
  | NodeName n => childrenWithNodeName s n
  | Value v => getNodesWithValue s v
  | Parents => parentsList s
  | Descendents => descendentsList s
  end.

Fixpoint interp (instructions : list xpath) (s : selection) : selection :=
  match instructions with
  | nil => s
  | instruction :: instructions' => interp instructions' (interp1 instruction s)
  end.

(** Begin proofs below **)

Require Import Frap.

Check parentsList.

Theorem no_extra_children: forall root n1 n2 x,
  In x (interp [ (NodeName n1) ; (NodeName n2) ; Parents ] [root])
  -> In x (interp [ (NodeName n1) ] [root]).
Proof.

  Check children.
  Check parentsList.
  Lemma parentsList_children : forall tr,
    parentsList (children tr) = (cons tr nil).
  Proof.
    

  Admitted.

  Lemma children_with_node_name_subset_children : forall (selection : list tree) name child,
    In child (childrenWithNodeName selection name) -> 
      In child (childrenList selection).
  Proof.
    induct selection0.
    simplify.
    equality.

    simplify.
    cases a; simplify.
    unfold flat_map.
  Admitted.

  Lemma parent_child_commands : forall y root n,
    In y (interp [ NodeName n ; Parents ] [root]) -> In y [root].
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
