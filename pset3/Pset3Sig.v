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

Fixpoint name (tr : tree) : string := 
  match tr with
  | Leaf => " "
  | NodeWithValue name value => name
  | NodeWithChildren name tr1 tr2 => name
  end.

Fixpoint value (tr : tree) : string := 
  match tr with
  | Leaf => " "
  | NodeWithValue name value => value
  | NodeWithChildren name tr1 tr2 => " "
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

Let n1 = NodeWithValue "number" "6.009".

