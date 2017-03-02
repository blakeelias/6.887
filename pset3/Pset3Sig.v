(** * 6.887 Formal Reasoning About Programs, Spring 2017 - Pset 3 *)

(* Authors: 
 * Blake Elias
 *)

(** * Correctness of XML/XPATH *)

Require Import String.
Require Import List.


Inductive tree :=
| Leaf: list tree -> tree
| NodeWithValue: string -> string -> list tree -> tree
| NodeWithChildren: string -> tree -> tree -> list tree -> tree.

Inductive xpath : Set :=
| NodeName (name : string)
| Value (v : string)
| Parents
| Descendents
| Concat (x1 x2 : xpath).

Definition selection := list tree.

Fixpoint name (tr : tree) : option string := 
  match tr with
  | Leaf parent => None
  | NodeWithValue name value parent => Some name
  | NodeWithChildren name tr1 tr2 parent => Some name
  end.

Fixpoint value (tr : tree) : option string := 
  match tr with
  | Leaf parent => None
  | NodeWithValue name value parent => Some value
  | NodeWithChildren name tr1 tr2 parent => None
  end.

Fixpoint children (tr : tree) : list tree :=
  match tr with
  | Leaf parent => nil
  | NodeWithValue name value parent => nil
  | NodeWithChildren name tr1 tr2 parent => tr1 :: ( cons tr2 nil )
end.

Fixpoint childrenList (trs : list tree) : list tree :=
  flat_map children trs.

Fixpoint descendents (tr : tree) : list tree :=
  match tr with
  | Leaf _ => tr :: nil
  | NodeWithValue _ _ _ => tr :: nil
  | NodeWithChildren name tr1 tr2 parent => tr :: (descendents tr1 ++ descendents tr2)
  end. 

Fixpoint descendentsList (trList : list tree) : list tree :=
  flat_map descendents trList.

Compute prefix "abc" "abcd".

Fixpoint string_eq (str1 str2 : string) : bool :=
  andb (prefix str1 str2) (prefix str2 str1).

Fixpoint hasValue (val : string) (tr : tree) : bool :=
  match tr with
  | Leaf _ => false
  | NodeWithValue name value _ => string_eq val value
  | NodeWithChildren name tr1 tr2 _ => false
  end.

Fixpoint getNodesWithValue (selectedTreeList : list tree) (val : string) : list tree :=
  filter (hasValue val) selectedTreeList.

Fixpoint hasName (name : string) (tr : tree) : bool :=
  match tr with
  | Leaf _ => false
  | NodeWithValue n v _ => string_eq n name
  | NodeWithChildren n tr1 tr2 _ => string_eq n name
  end.

Fixpoint getNodesWithNodeName (treeList : list tree) (name : string) : list tree :=
  filter (hasName name) treeList.

Fixpoint childrenWithNodeName (selection : list tree) (name : string) : list tree :=
  match selection with
  | tr :: l => (match tr with
    | Leaf _ => nil
    | NodeWithValue n v _ => nil
    | NodeWithChildren n tr1 tr2 _ => (if (hasName name tr1) then (cons tr1 nil) else nil) ++ (if (hasName name tr2) then (cons tr2 nil) else nil)
    end) ++ childrenWithNodeName l name
  | nil => nil
  end.

(* Fixpoint tree_eq (tr1 tr2 : tree) : bool :=
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
  end. *)

(* Fixpoint isParent (child parent : tree) : bool :=
  match parent with
  | Leaf => false
  | NodeWithValue name value => false
  | NodeWithChildren n tr1 tr2 => (orb (tree_eq child tr1) (tree_eq child tr2))
  end. *)

Fixpoint parent (tr : tree) : list tree :=
  match tr with
  | Leaf parent => parent
  | NodeWithValue _ _ parent => parent
  | NodeWithChildren _ _ _ parent => parent
  end.

Fixpoint parentsList (treeList : list tree) : list tree :=
  flat_map parent treeList.

(* Can try constructing a node as follows: 
Let n1 = NodeWithValue "number" "6.009".
*)


Fixpoint interp (e : xpath) (s : selection) : selection :=
  match e with
  | NodeName n => childrenWithNodeName s n
  | Value v => getNodesWithValue s v
  | Parents => parentsList s
  | Descendents => descendentsList s
  | Concat e1 e2 => interp e2 (interp e1 s)
  end.

(** Begin proofs below **)

Require Import Pset3Sig.
Require Import List.
Require Import Frap.

Theorem no_extra_children: forall root n1 n2 x,
  In x (interp 
  (Concat (NodeName n1)
   (Concat (NodeName n2)
    Parents)) (cons root nil))
  -> In x (interp 
    (NodeName n1)
    (cons root nil)).
Proof.
  simplify.
  cases root.

(* another approach: 
  induct root; simplify.
  equality.
  equality.
  case root1.
... unsure where to go next! *)
Admitted.

(* problem here... *)