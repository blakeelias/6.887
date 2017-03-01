Require Import Pset3Sig.
Require Import List.
Require Import Frap.

Theorem no_extra_children: forall root n1 n2 x,
  In x (parentsList
    root
    (childrenWithNodeName
         (childrenWithNodeName (cons root nil) n1)
        n2))
  -> In x (childrenWithNodeName (cons root nil) n1).
Proof.
  induction root.
  simplify.
  equality.
  simplify.
  equality.
  simplify.

  
Admitted.
